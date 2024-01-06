//! Exact covering with colors (XCC) using "dancing cells"
//! (Knuth §§7.2.2.1,3, Christmas Lectures 2018,23).
//!
//! A finite set of *items* is to be exactly covered by a finite
//! subset of *options* (not to be confused with Rust `Option`s).
//! *Primary items* are to be covered exactly once; *secondary items*
//! may be covered more than once, but must match in *color* across
//! options. Any CSP or SAT problem may be formulated using XCC;
//! for a CSP, the variables are the primary items, and the domains
//! are the options. Domains are represented using sparse sets with
//! reversible memory for fast backtracking.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::string::ToString;

use thiserror::Error;

use crate::domain::{Domain, SparseIntegerSet};

#[derive(Clone, Debug, Eq)]
pub enum Item<T: Hash + Eq, C: Hash + Eq> {
    /// An item that must be covered exactly once.
    Primary(T),

    /// An item that may be covered more than once,
    /// as long as its color is consistent across options.
    Secondary(T, Option<C>),
}

pub type Items<T, C> = Vec<Item<T, C>>;
pub type Options<T, C> = Vec<Items<T, C>>;

impl<T, C> Item<T, C>
where
    T: Hash + Eq + ToString,
    C: Hash + Eq + ToString,
{
    pub fn name(&self) -> String {
        match self {
            Self::Primary(name) => name.to_string(),
            Self::Secondary(name, _color) => name.to_string(),
        }
    }

    pub fn color(&self) -> Option<&C> {
        match self {
            Self::Primary(_name) => None,
            Self::Secondary(_name, color) => color.as_ref(),
        }
    }

    pub fn is_primary(&self) -> bool {
        match self {
            Self::Primary(_name) => true,
            Self::Secondary(_name, _color) => false,
        }
    }

    pub fn is_secondary(&self) -> bool {
        !self.is_primary()
    }
}

impl<T, C> fmt::Display for Item<T, C>
where
    T: Hash + Eq + ToString,
    C: Hash + Eq + ToString,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(color) = self.color() {
            f.write_fmt(format_args!("{}:{}", self.name(), color.to_string()))
        } else {
            f.write_fmt(format_args!("{}", self.name()))
        }
    }
}

impl<T, C> PartialEq for Item<T, C>
where
    T: Hash + Eq,
    C: Hash + Eq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Primary(s), Self::Primary(o))
            | (Self::Secondary(s, None), Self::Secondary(o, _))
            | (Self::Secondary(s, _), Self::Secondary(o, None)) => s == o,
            (Self::Secondary(s, Some(c)), Self::Secondary(o, Some(d))) => s == o && c == d,
            (_, _) => false,
        }
    }
}

impl<T, C> Hash for Item<T, C>
where
    T: Hash + Eq,
    C: Hash + Eq,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Primary(t) | Self::Secondary(t, _) => Hash::hash(t, state),
        }
    }
}

/// Things that may go wrong initializing & solving an XCC problem.
#[derive(Debug, Error)]
pub enum XccError<T, C>
where
    T: Hash + Eq + fmt::Display,
    C: Hash + Eq + fmt::Display,
{
    #[error("No options declared")]
    NoOptions,
    #[error("Primary item {0} is not used in any option, so no solutions are possible")]
    PrimaryItemNotUsed(Item<T, C>),
    #[error("Primary item {0} appears more than once in option {1}")]
    PrimaryItemUsedTwice(Item<T, C>, Items<T, C>),
    #[error("Secondary item {0} inconsistently colored in option {1}")]
    SecondaryItemInconsistentlyColored(Item<T, C>, Items<T, C>),
    #[error("Trail exceeded maximum size of {0}")]
    TrailOverflow(usize),
}

/// Maximum length of the backtracking trail through the search space.
const MAX_TRAIL_LEN: usize = 1_000;

// Internal types use item & option ids.
type ActiveItems = SparseIntegerSet<usize>;
type ActiveOptions = Vec<SparseIntegerSet<usize>>;
type ColorMap = HashMap<(usize, usize), usize>;
type OptionItems = Vec<SparseIntegerSet<usize>>;
type Solution = Vec<usize>;
type Solutions = Vec<Solution>;
type Trail = Vec<(usize, usize, Vec<(usize, usize)>)>;

/// XCC solver à la Knuth §7.2.2.3.
#[must_use]
#[derive(Debug)]
pub struct DancingCells<T: Hash + Eq, C: Hash + Eq> {
    /// The given items, in the given order. Never changed;
    /// ids are assigned by their position here.
    items: Items<T, C>,

    /// The given options (lists of items), in the given order.
    /// Never changed; ids are assigned by their position here.
    options: Options<T, C>,

    /// Which options involve what items, by id. Never changed;
    /// determines item involvement and sibling relations.
    option_items: OptionItems,

    /// The colors with which secondary items appear in options,
    /// indexed by `(option_id, item_id)` pairs. Never changed;
    /// used to consistently color secondary items.
    colors: ColorMap,

    /// The smallest id designating a secondary item. Never changed;
    /// determines which items are considered primary or secondary.
    second: usize,

    /// Whether or not to log status messages to standard error.
    trace: bool,
}

struct DanceState {
    trail: Trail,
    solution: Solution,
    active_items: ActiveItems,
    active_options: ActiveOptions,
}

impl<T, C> DancingCells<T, C>
where
    T: Clone + Hash + Eq + fmt::Debug + fmt::Display,
    C: Clone + Hash + Eq + fmt::Debug + fmt::Display,
{
    pub fn new(
        mut items: Items<T, C>,
        options: Options<T, C>,
        trace: bool,
    ) -> Result<Self, XccError<T, C>> {
        if options.is_empty() {
            return Err(XccError::NoOptions);
        }

        for item in items.iter() {
            if item.is_primary()
                && !options
                    .iter()
                    .any(|o| o.iter().any(|i| i.name() == item.name()))
            {
                return Err(XccError::PrimaryItemNotUsed(item.to_owned()));
            }
        }

        // Make primary items precede secondary ones, and record the boundary.
        items.sort_by_key(Item::is_secondary);
        let second = items
            .iter()
            .position(Item::is_secondary)
            .unwrap_or(usize::MAX);

        // Map item → id.
        let item_ids = items
            .iter()
            .enumerate()
            .map(|(index, item)| (item, index))
            .collect::<HashMap<&Item<T, C>, usize>>();

        // Record (by id) which options involve what items and how they are
        // colored. Check as we go that within an option, no primary item
        // appears more than once and all secondary items are consistently
        // colored.
        let mut color_ids = HashMap::<&C, usize>::new();
        let mut option_items = OptionItems::new();
        let mut colors = ColorMap::new();
        let mut uniq_items = HashSet::<usize>::new();
        let mut uniq_colors = HashMap::<usize, usize>::new();
        for (o, option) in options.iter().enumerate() {
            uniq_items.clear();
            let ids = SparseIntegerSet::new(option.iter().map(|i| item_ids[i]));
            for &i in ids.iter() {
                if i < second && !uniq_items.insert(i) {
                    return Err(XccError::PrimaryItemUsedTwice(
                        items[i].clone(),
                        option.clone(),
                    ));
                }
            }
            option_items.push(ids);

            uniq_colors.clear();
            for item in option {
                if let Some(color) = item.color() {
                    let i = item_ids[item];
                    let n = color_ids.len() + 1; // 0 = unique color
                    let c = *color_ids.entry(&color).or_insert(n);
                    if uniq_colors.insert(i, c).is_none() {
                        colors.insert((o, i), c);
                    } else {
                        return Err(XccError::SecondaryItemInconsistentlyColored(
                            items[i].clone(),
                            option.clone(),
                        ));
                    }
                }
            }
        }

        Ok(Self {
            items,
            options,
            option_items,
            colors,
            second,
            trace,
        })
    }

    /// Choose subsets of the options such that (i) every primary
    /// item occurs exactly once; and (ii) every secondary item
    /// has been assigned at most one color. See Knuth §§7.2.2.1,3.
    // TODO: yield solutions one at a time.
    pub fn solve(&self) -> Result<Vec<Options<T, C>>, XccError<T, C>> {
        let n = self.items.len();
        let m = self.options.len();
        let mut state = DanceState {
            trail: Trail::new(),
            solution: Solution::new(),
            active_items: ActiveItems::new(0..n),
            active_options: (0..n)
                .map(|i| (0..m).filter(|&o| self.is_involved(o, i, 0)).collect())
                .collect::<ActiveOptions>(),
        };
        let mut solutions = Solutions::new();

        // Knuth 7.2.2.1-(9), 7.2.2.1X,C, 7.2.2.3C.
        loop {
            if let Some((item, option)) = self.choose(&state) {
                self.cover(item, option, &mut state)?;
                if state.active_items.is_empty() {
                    solutions.push(state.solution.clone());
                }
            } else if !self.backtrack(&mut state) {
                break;
            }
        }

        // Map solutions from ids back into options.
        self.trace_solutions(&solutions);
        Ok(solutions
            .into_iter()
            .map(|options: Vec<usize>| {
                options
                    .into_iter()
                    .map(|option| self.options[option].clone())
                    .collect::<Options<T, C>>()
            })
            .collect::<Vec<Options<T, C>>>())
    }

    /// Look up how `item` is colored in `option`. Return a color id,
    /// or `0` if it is not assigned a color there (or is primary).
    fn color(&self, option: usize, item: usize) -> usize {
        self.colors.get(&(option, item)).copied().unwrap_or(0)
    }

    /// Visit the items that are involved with (contained by) `option`.
    fn involved(&self, option: usize) -> impl Iterator<Item = &usize> {
        self.option_items[option].iter()
    }

    /// Does `option` involve (contain) `item` with (optional, other) `color`?
    /// The complemented color condition lets us use this predicate to delete
    /// conflicting options.
    fn is_involved(&self, option: usize, item: usize, color: usize) -> bool {
        self.option_items[option].contains(&item)
            && (self.is_primary(item) || self.color(option, item) != color)
    }

    /// Is `item` a primary (mandatory, uncolored) item?
    fn is_primary(&self, item: usize) -> bool {
        item < self.second
    }

    /// Is `item` a secondary (optional, colored) item?
    fn is_secondary(&self, item: usize) -> bool {
        !self.is_primary(item)
    }

    /// Choose an active primary item to cover using the *minimum remaining
    /// values* (MRV) heuristic (viz., the item with the smallest positive
    /// number of active options), or `None` if there is no such item; then
    /// select the first active option for that item.
    fn choose(
        &self,
        DanceState {
            active_items,
            active_options,
            ..
        }: &DanceState,
    ) -> Option<(usize, usize)> {
        active_items
            .iter()
            .filter_map(|&item| {
                if self.is_secondary(item) || active_options[item].is_empty() {
                    None
                } else {
                    Some((item, &active_options[item]))
                }
            })
            .min_by_key(|(_item, options)| options.len())
            .map(|(item, options)| {
                let option = options.first().expect("active items should have options");
                (item, option)
            })
    }

    /// Having chosen `option` to cover `item`, delete it from the active options,
    /// record a trail entry if there are any remaining ways to cover `item`, and
    /// hide all siblings of `item` in `option`.
    fn cover(
        &self,
        item: usize,
        option: usize,
        DanceState {
            trail,
            solution,
            active_items,
            active_options,
            ..
        }: &mut DanceState,
    ) -> Result<(), XccError<T, C>> {
        if self.trace {
            eprintln!(
                "** Covering item {} with option {}",
                self.format_item(item),
                self.format_option(option),
            );
        }

        assert!(self.is_primary(item), "can't choose a secondary item");
        assert!(
            active_options[item].delete(&option),
            "option {} is inactive, so can't cover item {}",
            self.format_option(option),
            self.format_item(item),
        );
        if active_options[item].is_empty() {
            assert!(
                active_items.delete(&item),
                "item {} is already inactive",
                self.format_item(item)
            );
        } else {
            self.trail(trail, solution, active_items, active_options)?;
        }

        for &sibling in self.involved(option) {
            let color = self.color(sibling, option);
            self.hide(sibling, color, active_items, active_options);
        }

        self.trace_state("after covering", active_items, active_options);
        Ok(solution.push(option))
    }

    /// Deactivate `item` and all active options that involve it.
    fn hide(
        &self,
        item: usize,
        color: usize,
        active_items: &mut ActiveItems,
        active_options: &mut ActiveOptions,
    ) {
        for &other in active_items.iter() {
            active_options[other].delete_if(|&option| self.is_involved(option, item, color));
        }
        active_items.delete(&item);
    }

    /// Save the active state in the trail for backtracking.
    fn trail(
        &self,
        trail: &mut Trail,
        solution: &Solution,
        active_items: &ActiveItems,
        active_options: &ActiveOptions,
    ) -> Result<(), XccError<T, C>> {
        if trail.len() >= MAX_TRAIL_LEN {
            Err(XccError::TrailOverflow(MAX_TRAIL_LEN))
        } else {
            let s = solution.len();
            let n = active_items.len();
            assert!(n > 0, "no active items to trail");
            let options = active_items
                .iter()
                .map(|&i| (i, active_options[i].len()))
                .collect::<Vec<(usize, usize)>>();
            Ok(trail.push((s, n, options)))
        }
    }

    /// Restore the active state from the last trail entry and return `true`,
    /// or `false` if the trail is empty.
    fn backtrack(
        &self,
        DanceState {
            trail,
            solution,
            active_items,
            active_options,
        }: &mut DanceState,
    ) -> bool {
        if let Some((s, n, options)) = trail.pop() {
            solution.truncate(s);
            assert!(n > 0, "no active items on trail");
            active_items.restore(n);
            for &(i, m) in options.iter() {
                assert!(m > 0, "no active options for {}", self.format_item(i));
                active_options[i].restore(m);
            }
            self.trace_state("after backtracking", active_items, active_options);
            true
        } else {
            false
        }
    }

    /// If tracing is active, write a description of the active items & options to stderr.
    fn trace_state(&self, when: &'static str, items: &ActiveItems, options: &ActiveOptions) {
        if self.trace {
            eprintln!(
                "** Active items {when}: {{{}}}; options {{{}}}",
                items
                    .iter()
                    .map(|&i| self.format_item(i))
                    .collect::<Vec<_>>()
                    .join(", "),
                options
                    .iter()
                    .enumerate()
                    .map(|(i, options)| {
                        format!(
                            "{} => {{{}}}",
                            self.format_item(i),
                            options
                                .iter()
                                .map(|&o| self.format_option(o))
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
    }

    /// If tracing is active, write a set of solutions to stderr.
    pub fn trace_solutions(&self, solutions: &Vec<Vec<usize>>) {
        if self.trace {
            eprintln!(
                "* Got {} solution(s):\n* {}",
                solutions.len(),
                solutions
                    .iter()
                    .map(|options| {
                        options
                            .iter()
                            .map(|&o| self.format_option(o))
                            .collect::<Vec<_>>()
                            .join(", ")
                    })
                    .collect::<Vec<_>>()
                    .join("\n* ")
            );
        }
    }

    fn format_item(&self, item: usize) -> String {
        self.items[item].name()
    }

    fn format_option(&self, option: usize) -> String {
        format!(
            "[{}]",
            self.options[option]
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(" ")
        )
    }
}

#[cfg(test)]
mod test {
    use super::{DancingCells, Item, XccError};
    use crate::builder::XccBuilder;

    /// Detect invalid problems.
    #[test]
    fn invalid_xcc() {
        let builder = XccBuilder::new();
        assert!(matches!(builder.build(), Err(XccError::NoOptions)));

        let mut builder = XccBuilder::new();
        builder.parse_primary_items(["a", "b"]).unwrap();
        builder.parse_option(["a"]).unwrap();
        assert!(matches!(
            builder.build(),
            Err(XccError::PrimaryItemNotUsed(_))
        ));

        let mut builder = XccBuilder::new();
        builder.parse_primary_items(["a"]).unwrap();
        builder.parse_option(["a", "a"]).unwrap();
        assert!(matches!(
            builder.build(),
            Err(XccError::PrimaryItemUsedTwice(_, _))
        ));

        let mut builder = XccBuilder::new();
        builder.parse_primary_items(["a"]).unwrap();
        builder.parse_secondary_items(["x"]).unwrap();
        builder.parse_option(["a", "x", "x:X", "x:Y"]).unwrap();
        assert!(matches!(
            builder.build(),
            Err(XccError::SecondaryItemInconsistentlyColored(_, _))
        ));
    }

    macro_rules! sol {
        ($v:ident, $i:expr, $j:expr) => {{
            $v[$i][$j].iter().map(|i| i.to_string()).collect::<Vec<_>>()
        }};
    }

    // TODO: macro_rules! xcc(problem, solution)

    #[test]
    fn trivial_xc_1() {
        let mut builder = XccBuilder::new();
        builder.parse_primary_items(["a"]).unwrap();
        builder.parse_option(["a"]).unwrap();
        builder.trace(false).unwrap();
        let xc = builder.build().unwrap();
        let solutions = xc.solve().unwrap();
        assert_eq!(solutions.len(), 1);
        assert_eq!(sol!(solutions, 0, 0), ["a"]);
    }

    #[test]
    fn trivial_xc_2() {
        let mut builder = XccBuilder::new();
        builder.parse_primary_items(["a", "b"]).unwrap();
        builder.parse_option(["a"]).unwrap();
        builder.parse_option(["b"]).unwrap();
        builder.trace(false).unwrap();
        let xc = builder.build().unwrap();
        let solutions = xc.solve().unwrap();
        assert_eq!(solutions.len(), 1);
        assert_eq!(solutions[0].len(), 2);
        assert_eq!(sol!(solutions, 0, 0), ["a"]);
        assert_eq!(sol!(solutions, 0, 1), ["b"]);
    }

    #[test]
    fn trivial_xc_3() {
        let mut builder = XccBuilder::new();
        builder.parse_primary_items(["a", "b"]).unwrap();
        builder.parse_option(["a"]).unwrap();
        builder.parse_option(["b"]).unwrap();
        builder.parse_option(["a", "b"]).unwrap();
        builder.trace(false).unwrap();
        let xc = builder.build().unwrap();
        let solutions = xc.solve().unwrap();
        assert_eq!(solutions.len(), 2);
        assert_eq!(solutions[0].len(), 2);
        assert_eq!(sol!(solutions, 0, 0), ["a"]);
        assert_eq!(sol!(solutions, 0, 1), ["b"]);
        assert_eq!(solutions[1].len(), 1);
        assert_eq!(sol!(solutions, 1, 0), ["a", "b"]);
    }

    /// Exact covering: Knuth 7.2.2.1-(6).
    #[test]
    fn toy_xc() {
        let mut builder = XccBuilder::new();
        builder
            .parse_primary_items(["a", "b", "c", "d", "e", "f", "g"])
            .unwrap();
        builder.parse_option(["c", "e"]).unwrap();
        builder.parse_option(["a", "d", "g"]).unwrap();
        builder.parse_option(["b", "c", "f"]).unwrap();
        builder.parse_option(["a", "d", "f"]).unwrap();
        builder.parse_option(["b", "g"]).unwrap();
        builder.parse_option(["d", "e", "g"]).unwrap();
        builder.trace(false).unwrap();
        let xc = builder.build().unwrap();
        let solutions = xc.solve().unwrap();
        assert_eq!(solutions.len(), 1);
        assert_eq!(solutions[0].len(), 3);
        assert_eq!(sol!(solutions, 0, 0), ["a", "d", "f"]);
        assert_eq!(sol!(solutions, 0, 1), ["b", "g"]);
        assert_eq!(sol!(solutions, 0, 2), ["c", "e"]);
    }

    /// Exact covering with colors: Knuth 7.2.2.1-(49), 7.2.2.3-(113).
    #[test]
    fn toy_xcc() {
        let mut builder = XccBuilder::new();
        builder.parse_primary_items(["p", "q", "r"]).unwrap();
        builder.parse_secondary_items(["x", "y"]).unwrap();
        builder.parse_option(["p", "q", "x", "y:A"]).unwrap();
        builder.parse_option(["p", "r", "x:A", "y"]).unwrap();
        builder.parse_option(["p", "x:B"]).unwrap();
        builder.parse_option(["q", "x:A"]).unwrap();
        builder.parse_option(["r", "y:B"]).unwrap();
        builder.trace(false).unwrap();
        let xcc = builder.build().unwrap();
        let solutions = xcc.solve().unwrap();
        assert_eq!(solutions.len(), 1);
        assert_eq!(solutions[0].len(), 2);
        assert_eq!(sol!(solutions, 0, 0), ["q", "x:A"]);
        assert_eq!(sol!(solutions, 0, 1), ["p", "r", "x:A", "y"]);
    }

    /// "Extreme" XC problem: Knuth 7.2.2.1-(82).
    /// All _2^n - 1_ possible options on _n_ primary items.
    #[test]
    fn extreme_xc() {
        let n = 8;
        let items = (0..n)
            .map(|i| Item::<usize, usize>::Primary(i))
            .collect::<Vec<_>>();
        let options = gray_codes::VecSubsets::of(&items)
            .into_iter()
            .map(|x| x.into_iter().cloned().collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let xc = DancingCells::new(items.clone(), options, false).unwrap();
        let solutions = xc.solve().unwrap();
        for solution in solutions {
            let mut solution = solution.into_iter().flatten().collect::<Vec<_>>();
            solution.sort_by_key(|item| match item {
                Item::Primary(t) => *t,
                Item::Secondary(_t, _c) => unreachable!("no secondary items"),
            });
            assert_eq!(&solution, &items);
        }
    }
}
