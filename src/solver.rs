//! Exact covering with colors (XCC) using dancing cells
//! (Knuth §§ 7.2.2.1,3, Christmas Lectures 2018, 2023).
//!
//! A finite set of *items* is to be exactly covered by a finite subset of
//! *options* (not to be confused with Rust's `Option`). *Primary items*
//! are to be covered exactly once; *secondary items* may be covered more
//! than once, but must match in *color* across options. A solver searches
//! for exact covers without enumerating all possible subsets.
//!
//! Any CSP or SAT problem may be formulated using XCC; e.g., for a CSP,
//! the primary items are the variables, and the options are the domains.
//! We can also use it for finding models of logic programs, where the
//! primary items are the rules, secondary items are (ground) atomic
//! formulas, and the options are ways of satisfying the rules with various
//! interpretations (sets of atomic formulas taken as true).
//!
//! During a search, active items and options are represented using
//! sparse sets with reversible memory for fast backtracking; see the
//! `crate::domain` module for details. The memory required for a search
//! should be constant once the problem is set up.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::string::ToString;

use thiserror::Error;

use crate::domain::{Domain, SparseIntegerSet};
use crate::tracer::Trace;

/// A primary or secondary item. The `Ord` requirement is so that the
/// solver can build an item → id map and operate internally on integers
/// instead of instances. Solutions are decoded back to `Item` instances
/// as they are found.
#[derive(Clone, Debug, Eq, Ord, PartialOrd, PartialEq)]
pub enum Item<T, C>
where
    T: Ord,
    C: Ord,
{
    /// An item that must be covered exactly once.
    Primary(T),

    /// An item that may be covered more than once,
    /// as long as its color is consistent across options.
    Secondary(T, Option<C>),
}

/// An option (not a Rust `Option`) is a subset of items.
pub type Items<T, C> = Vec<Item<T, C>>;

/// And a solution is a set of options.
pub type Options<T, C> = Vec<Items<T, C>>;

impl<T, C> Item<T, C>
where
    T: Ord + ToString,
    C: Ord + ToString,
{
    pub fn item(&self) -> &T {
        match self {
            Self::Primary(item) => item,
            Self::Secondary(item, _color) => item,
        }
    }

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
    T: Ord + ToString,
    C: Ord + ToString,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(color) = self.color() {
            f.write_fmt(format_args!("{}:{}", self.name(), color.to_string()))
        } else {
            f.write_fmt(format_args!("{}", self.name()))
        }
    }
}

/// Things that may go wrong initializing & solving an XCC problem.
#[derive(Debug, Error)]
pub enum XccError<T, C>
where
    T: Ord + Clone + fmt::Display,
    C: Ord + Clone + fmt::Display,
{
    #[error("No more solutions")]
    NoMoreSolutions,
    #[error("Primary item {0} appears more than once in option {1}")]
    PrimaryItemUsedTwice(Item<T, C>, Items<T, C>),
    #[error("Secondary item {0} inconsistently colored in option {1}")]
    SecondaryItemInconsistentlyColored(Item<T, C>, Items<T, C>),
    #[error("Trail exceeded maximum size of {0}")]
    TrailOverflow(usize),
    #[error("Item {0} was not declared")]
    UndeclaredItem(Item<T, C>),
}

/// Maximum length of the backtracking trail through the search space.
/// Measured in entries, not items or options; each entry contains a
/// few fixed sizes and a vector of sizes whose length is the number
/// of currently active items.
const MAX_TRAIL_LEN: usize = 1_000;

// Internal types use item & option ids.
type ActiveItems = SparseIntegerSet<usize>;
type ActiveOptions = Vec<SparseIntegerSet<usize>>;
type ColorMap = BTreeMap<(usize, usize), usize>;
type OptionItems = Vec<SparseIntegerSet<usize>>;
type Solution = Vec<usize>;
type Trail = Vec<(usize, usize, Vec<(usize, usize)>)>;

/// XCC solver à la Knuth §7.2.2.3. The tables here are initialized
/// once and never changed; all mutable state is relegated to the
/// `DanceState` structure, and the search procedure is controlled
/// by the `DanceStep` iterator. But all of the algorithm-specific
/// logic is implemented on this structure.
#[must_use]
#[derive(Debug)]
pub struct DancingCells<T, C>
where
    T: Ord,
    C: Ord,
{
    /// The given items, in the given order.
    /// Item ids are assigned by their position here.
    items: Items<T, C>,

    /// The given options (lists of items), in the given order.
    /// Option ids are assigned by their position here.
    options: Options<T, C>,

    /// Which options involve what items, by id. Determines
    /// item involvement and sibling relations in an option.
    option_items: OptionItems,

    /// The colors with which secondary items appear in options,
    /// indexed by `(option_id, item_id)` pairs. Used to ensure
    /// consistently colored secondary items.
    colors: ColorMap,

    /// The smallest id designating a secondary item.
    /// Determines which items are considered primary.
    second: usize,

    /// Whether or not to log status messages to standard error.
    trace: Trace,
}

impl<T, C> DancingCells<T, C>
where
    T: Ord + Clone + fmt::Debug + fmt::Display,
    C: Ord + Clone + fmt::Debug + fmt::Display,
{
    /// Check and initialize the XCC problem, but do not solve it yet.
    pub fn new(
        mut items: Items<T, C>,
        options: Options<T, C>,
        trace: Trace,
    ) -> Result<Self, XccError<T, C>> {
        // Make primary items precede secondary ones, and record the boundary.
        items.sort_by_key(Item::is_secondary);
        let second = items
            .iter()
            .position(Item::is_secondary)
            .unwrap_or(usize::MAX);

        // Map item name → id.
        let item_ids = items
            .iter()
            .enumerate()
            .map(|(index, item)| (item.item(), index))
            .collect::<BTreeMap<&T, usize>>();

        // Record (by id) which options involve what items and how they are
        // colored. Check as we go that within an option, no primary item
        // appears more than once and all secondary items are consistently
        // colored.
        let mut color_ids = BTreeMap::<&C, usize>::new();
        let mut option_items = OptionItems::new();
        let mut colors = ColorMap::new();
        let mut uniq_items = BTreeSet::<usize>::new();
        for (o, option) in options.iter().enumerate() {
            for item in option.iter() {
                if !item_ids.contains_key(item.item()) {
                    return Err(XccError::UndeclaredItem(item.clone()));
                }
            }

            uniq_items.clear();
            let ids = SparseIntegerSet::new(option.iter().map(|item| item_ids[item.item()]));
            for &i in ids.iter() {
                if i < second && !uniq_items.insert(i) {
                    return Err(XccError::PrimaryItemUsedTwice(
                        items[i].clone(),
                        option.clone(),
                    ));
                }
            }
            option_items.push(ids);

            for item in option {
                if let Some(color) = item.color() {
                    let i = item_ids[item.item()];
                    let n = color_ids.len() + 1; // 0 = unique color
                    let c = *color_ids.entry(color).or_insert(n);
                    if let Some(&d) = colors.get(&(o, i)) {
                        if d != c {
                            return Err(XccError::SecondaryItemInconsistentlyColored(
                                items[i].clone(),
                                option.clone(),
                            ));
                        }
                    } else {
                        colors.insert((o, i), c);
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

    /// Solve the XCC problem: search for subsets of the options such that
    /// (i) every primary item occurs exactly once; and (ii) every secondary
    /// item is assigned at most one color. See Knuth §§7.2.2.1,3.
    pub fn solve(&self) -> DanceStep<T, C> {
        let n = self.items.len();
        let m = self.options.len();
        let state = DanceState {
            trail: Trail::new(),
            solution: Solution::new(),
            active_items: ActiveItems::new(0..n),
            active_options: (0..n)
                .map(|i| (0..m).filter(|&o| self.is_involved(o, i, 0)).collect())
                .collect::<ActiveOptions>(),
        };
        DanceStep::new(self, state)
    }

    /// Find the next solution. See Knuth 7.2.2.1-(9), 7.2.2.1X,C, 7.2.2.3C.
    fn step(&self, state: &mut DanceState) -> Result<Options<T, C>, XccError<T, C>> {
        loop {
            if let Some((item, option)) = self.choose(state) {
                self.cover(item, option, state)?;
                if state.active_items.is_empty()
                    || state.active_items.iter().all(|&i| self.is_secondary(i))
                {
                    return Ok(self.decode_solution(&state.solution));
                }
            } else if !self.backtrack(state) {
                return Err(XccError::NoMoreSolutions);
            }
        }
    }

    /// Decode a set of option ids into (cloned) options.
    fn decode_solution(&self, solution: &Solution) -> Options<T, C> {
        self.trace_solution(solution);
        solution
            .iter()
            .map(|&option| self.options[option].clone())
            .collect()
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

    /// Having chosen `option` to cover `item`, delete it from the set of
    /// active options, record a trail entry if there are any remaining
    /// ways to cover `item`, and hide all siblings of `item` in `option`.
    fn cover(
        &self,
        item: usize,
        option: usize,
        state: &mut DanceState,
    ) -> Result<(), XccError<T, C>> {
        trace!(
            self.trace,
            "** Covering item {} with option {}",
            self.format_item(item),
            self.format_option(option),
        );
        assert!(self.is_primary(item), "can't choose a secondary item");
        assert!(
            state.active_options[item].delete(&option),
            "option {} is inactive, so can't cover item {}",
            self.format_option(option),
            self.format_item(item),
        );
        if !state.active_options[item].is_empty() {
            self.trail(state)?;
        }

        for &sibling in self.involved(option) {
            let color = self.color(option, sibling);
            for &other in state.active_items.iter() {
                state.active_options[other]
                    .delete_if(|&option| self.is_involved(option, sibling, color));
            }
            state.active_items.delete(&sibling);
        }

        self.trace_state("after covering", &state.active_items, &state.active_options);
        state.solution.push(option);
        Ok(())
    }

    /// Save the active state in the trail for backtracking.
    fn trail(
        &self,
        DanceState {
            trail,
            solution,
            active_items,
            active_options,
            ..
        }: &mut DanceState,
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
            trail.push((s, n, options));
            Ok(())
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
            assert!(n > 0, "no active items on trail");
            solution.truncate(s);
            active_items.restore(n);
            for &(i, m) in options.iter() {
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
        trace!(
            self.trace,
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
        );
    }

    /// If tracing is active, write a solution to stderr.
    pub fn trace_solution(&self, solution: &Solution) {
        trace!(
            self.trace,
            "* Got a solution: {}",
            solution
                .iter()
                .map(|&o| self.format_option(o))
                .collect::<Vec<_>>()
                .join(", ")
        );
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

/// All active state associated with a search for solutions
/// to an XCC problem. The solver will reference and modify
/// this data, but not own it.
#[derive(Debug)]
struct DanceState {
    trail: Trail,
    solution: Solution,
    active_items: ActiveItems,
    active_options: ActiveOptions,
}

/// An iterator over all solutions to an XCC problem. Each iteration
/// finds the next solution; termination, accumulation, and inspection
/// of solutions may be done by the standard methods on `Iterator`.
/// Owns all of the mutable search state and drives the search via
/// a shared reference to the solver, but implements no search logic
/// other than "stop when no more solutions are available".
pub struct DanceStep<'a, T, C>
where
    T: Ord + Clone + fmt::Debug + fmt::Display,
    C: Ord + Clone + fmt::Debug + fmt::Display,
{
    solver: &'a DancingCells<T, C>,
    state: DanceState,
}

impl<'a, T, C> DanceStep<'a, T, C>
where
    T: Ord + Clone + fmt::Debug + fmt::Display,
    C: Ord + Clone + fmt::Debug + fmt::Display,
{
    fn new(solver: &'a DancingCells<T, C>, state: DanceState) -> Self {
        Self { solver, state }
    }
}

impl<'a, T, C> Iterator for DanceStep<'a, T, C>
where
    T: Ord + Clone + fmt::Debug + fmt::Display,
    C: Ord + Clone + fmt::Debug + fmt::Display,
{
    type Item = Result<Options<T, C>, XccError<T, C>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.solver.step(&mut self.state) {
            Err(XccError::NoMoreSolutions) => None,
            solution => Some(solution),
        }
    }
}

#[cfg(test)]
mod test {
    use std::collections::BTreeSet;

    use super::{DancingCells, Item, Options, XccError};

    macro_rules! item {
        [$i:ident] => { Item::Primary::<&str, &str>(stringify!($i)) };
        [$i:ident:None] => { Item::Secondary::<&str, &str>(stringify!($i), None) };
        [$i:ident:$c:ident] => { Item::Secondary::<&str, &str>(stringify!($i), Some(stringify!($c))) };
    }

    macro_rules! items {
        [$($i:ident$(:$c:ident)?),*] => { vec![$(item![$i$(:$c)?]),*] };
    }

    macro_rules! solutions {
        ($([$([$($option:tt)*]),*]),*) => { vec![$(vec![$(items![$($option)*]),*]),*] };
    }

    /// Detect invalid problems.
    #[test]
    fn invalid_xcc() {
        assert!(matches!(
            DancingCells::new(vec![], vec![items![a]], false),
            Err(XccError::UndeclaredItem(item![a]))
        ));

        assert!(matches!(
            DancingCells::new(vec![item![a]], vec![items![a, a]], false),
            Err(XccError::PrimaryItemUsedTwice(item![a], _))
        ));

        assert!(matches!(
            DancingCells::new(items![a, x:None], vec![items![a, x, x:X, x:Y]], false),
            Err(XccError::SecondaryItemInconsistentlyColored(
                item![x:None],
                _
            ))
        ));
    }

    #[test]
    fn trivial_xc_0() {
        let items = vec![];
        let options = vec![];
        let solver = DancingCells::<&str, &str>::new(items, options, false).unwrap();
        let solutions = solver.solve().collect::<Result<Vec<_>, _>>().unwrap();
        assert!(solutions.is_empty());
    }

    #[test]
    fn trivial_xc_1a() {
        let items = items![a, b];
        let options = vec![items![a]]; // b is unused, so can't be covered
        let solver = DancingCells::<&str, &str>::new(items, options, false).unwrap();
        let solutions = solver.solve().collect::<Result<Vec<_>, _>>().unwrap();
        assert!(solutions.is_empty());
    }

    #[test]
    fn trivial_xc_1b() {
        let items = items![a];
        let options = vec![items![a]];
        let solver = DancingCells::<&str, &str>::new(items, options, false).unwrap();
        let solutions = solver.solve().collect::<Result<Vec<_>, _>>().unwrap();
        assert_eq!(solutions, solutions!([[a]]));
    }

    #[test]
    fn trivial_xc_2() {
        let items = items![a, b];
        let options = vec![items![a], items![b]];
        let solver = DancingCells::<&str, &str>::new(items, options, false).unwrap();
        let solutions = solver.solve().collect::<Result<Vec<_>, _>>().unwrap();
        assert_eq!(solutions, solutions!([[a], [b]]));
    }

    #[test]
    fn trivial_xc_3() {
        let items = items![a, b];
        let options = vec![items![a], items![b], items![a, b]];
        let solver = DancingCells::<&str, &str>::new(items, options, false).unwrap();
        let solutions = solver.solve().collect::<Result<Vec<_>, _>>().unwrap();
        assert_eq!(solutions, solutions!([[a], [b]], [[a, b]]));
    }

    /// Exact covering: Knuth 7.2.2.1-(6).
    #[test]
    fn toy_xc() {
        let items = items![a, b, c, d, e, f, g];
        let options = vec![
            items![c, e],
            items![a, d, g],
            items![b, c, f],
            items![a, d, f],
            items![b, g],
            items![d, e, g],
        ];
        let solver = DancingCells::<&str, &str>::new(items, options, false).unwrap();
        let solutions = solver.solve().collect::<Result<Vec<_>, _>>().unwrap();
        assert_eq!(solutions, solutions!([[a, d, f], [b, g], [c, e]]));
    }

    /// Exact covering with colors: Knuth 7.2.2.1-(49), 7.2.2.3-(113).
    #[test]
    fn toy_xcc() {
        let items = items![p, q, r, x:None, y:None];
        let options = vec![
            items![p, q, x, y:A],
            items![p, r, x:A, y],
            items![p, x:B],
            items![q, x:A],
            items![r, y:B],
        ];
        let solver = DancingCells::<&str, &str>::new(items, options, false).unwrap();
        let solutions = solver.solve().collect::<Result<Vec<_>, _>>().unwrap();
        assert_eq!(solutions, solutions!([[q, x:A], [p, r, x:A, y]]));
    }

    /// "Extreme" XC problem of Knuth 7.2.2.1-(82): use all 2^_n_ - 1
    /// possible options on _n_ primary items. The tunable parameters
    /// are _n_ and _r_, how often to report & sample the solutions
    /// found so far. (Sampling lets us approximate checking uniqueness
    /// of solutions without keeping most of them.) Knuth finds all
    /// 1,382,958,545 solutions for _n_ = 15 "in just 432 gigamems"
    /// with his dancing cells implementation. This code running in
    /// release mode on the author's workstation (Intel i9-13900K)
    /// finds them in about 3 hours; finding the 10,480,142,147 solutions
    /// for _n_ = 16 takes about 24 hours. We keep _n_ set to a value
    /// that runs in < 1 second (in release mode) for the test.
    #[test]
    fn extreme_xc() {
        // Parameters.
        const N: u8 = 10;
        const R: usize = 1_000_000;

        // Knuth §7.2.1.1
        let items = (0..N).map(Item::Primary).collect::<Vec<_>>();
        let options = gray_codes::VecSubsets::of(&items)
            .map(|x| x.into_iter().cloned().collect::<Vec<_>>())
            .collect::<Vec<_>>();

        let xxc = DancingCells::new(items.clone(), options, false).unwrap();
        let mut i = 0;
        let mut uniq = BTreeSet::<Options<u8, u8>>::new();
        for result in xxc.solve() {
            let solution: Options<u8, u8> = result.unwrap();
            let mut solution_items = solution.iter().flatten().cloned().collect::<Vec<_>>();
            solution_items.sort_by_key(|item| match item {
                Item::Primary(t) => *t,
                Item::Secondary(_t, _c) => unreachable!("no secondary items"),
            });
            assert_eq!(&solution_items, &items);

            i += 1;
            if i % R == 0 {
                assert!(uniq.insert(solution.clone()));
                eprintln!(
                    "* {i} solutions so far, like {{{}}}",
                    solution
                        .iter()
                        .map(|s| format!(
                            "[{}]",
                            s.iter()
                                .map(|i| i.to_string())
                                .collect::<Vec<_>>()
                                .join(" ")
                        ))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
        }
        assert!(i > 0);
        if i > R {
            eprintln!("* {i} solutions total.")
        }
    }
}
