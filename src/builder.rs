//! Set up an XCC problem.

use std::collections::HashMap;
use std::hash::Hash;
use std::string::ToString;

use thiserror::Error;

use crate::solver::{DancingCells, Item, XccError, Options, Items};

/// Things that may go wrong setting up an XCC problem.
#[derive(Debug, Error)]
pub enum BuildError<T: ToString> {
    #[error("Invalid item {0}")]
    InvalidItem(T),
    #[error("Item {0} is used in an option but not declared")]
    ItemNotDeclared(T),
    #[error("Item {0} is declared more than once")]
    ItemDeclaredTwice(T),
    #[error("No primary items declared")]
    NoPrimaryItems,
    #[error("Item {0} is declared as primary but is assigned a color")]
    PrimaryItemColored(T),
}

/// Set up an XCC problem. Items may be represented by strings
/// like `"p"`; secondary items may include colors like `"x:A"`.
/// Options may be represented by lists of such items, and every
/// option must include at least one primary item.
#[derive(Debug, Default)]
pub struct XccBuilder<T: Hash + Eq, C: Hash + Eq> {
    /// name → primary
    names: HashMap<T, bool>,
    items: Items<T, C>,
    options: Options<T, C>,
}

fn parse_name(name: impl ToString) -> Result<String, BuildError<String>> {
    let name = name.to_string();
    if name.contains(':') {
        return Err(BuildError::InvalidItem(name));
    }
    Ok(name)
}

impl<'a> XccBuilder<String, String> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn item(&mut self, item: Item<String, String>) -> Result<(), BuildError<String>> {
        let name = item.name();
        if self.names.contains_key(&name) {
            return Err(BuildError::ItemDeclaredTwice(name));
        }
        self.names.insert(name, item.is_primary());
        self.items.push(item);
        Ok(())
    }

    pub fn option(&mut self, option: Vec<Item<String, String>>) -> Result<(), BuildError<String>> {
        if !option.iter().any(Item::is_primary) {
            return Err(BuildError::NoPrimaryItems);
        }
        self.options.push(option);
        Ok(())
    }

    pub fn parse_primary_items<T: ToString>(
        &mut self,
        names: impl IntoIterator<Item = T>,
    ) -> Result<(), BuildError<String>> {
        for name in names.into_iter() {
            self.item(Item::Primary(parse_name(name)?))?;
        }
        Ok(())
    }

    pub fn parse_secondary_items<T: ToString>(
        &mut self,
        names: impl IntoIterator<Item = T>,
    ) -> Result<(), BuildError<String>> {
        for name in names.into_iter() {
            self.item(Item::Secondary(parse_name(name)?, None))?;
        }
        Ok(())
    }

    pub fn parse_option<T: ToString>(
        &mut self,
        items: impl IntoIterator<Item = T>,
    ) -> Result<(), BuildError<String>> {
        let mut option = Vec::new();
        for item in items {
            let item = item.to_string();
            match item.split_once(':') {
                None => {
                    if let Some(primary) = self.names.get(&item) {
                        option.push(if *primary {
                            Item::Primary(item)
                        } else {
                            Item::Secondary(item, None)
                        });
                    } else {
                        return Err(BuildError::ItemNotDeclared(item));
                    }
                }
                Some((name, color)) => {
                    let name = name.to_string();
                    let color = color.to_string();
                    if let Some(primary) = self.names.get(&name) {
                        option.push(if *primary {
                            return Err(BuildError::PrimaryItemColored(name));
                        } else {
                            Item::Secondary(name, Some(color))
                        });
                    } else {
                        return Err(BuildError::ItemNotDeclared(name));
                    }
                }
            }
        }
        self.option(option)
    }

    pub fn build(self) -> Result<DancingCells<String, String>, XccError<String, String>> {
        DancingCells::new(self.items, self.options)
    }
}

#[test]
fn builder() {
    let mut builder = XccBuilder::new();
    assert!(matches!(
        builder.parse_primary_items(["a:A"]),
        Err(BuildError::InvalidItem(_))
    ));
    assert!(builder.parse_primary_items(["a"]).is_ok());
    assert!(matches!(
        builder.parse_secondary_items(["a"]),
        Err(BuildError::ItemDeclaredTwice(_)),
    ));
    assert!(builder.parse_secondary_items(["b"]).is_ok());
    assert!(matches!(builder.build(), Err(XccError::NoOptions)));

    let mut builder = XccBuilder::new();
    assert!(builder.parse_primary_items(["a", "b"]).is_ok());
    assert!(builder.parse_option(["a"]).is_ok());
    assert!(matches!(
        builder.build(),
        Err(XccError::PrimaryItemNotUsed(_)),
    ));

    let mut builder = XccBuilder::new();
    assert!(builder.parse_primary_items(["p", "q"]).is_ok());
    assert!(builder.parse_secondary_items(["x", "y"]).is_ok());
    assert!(matches!(
        builder.parse_option(["x"]),
        Err(BuildError::NoPrimaryItems)
    ));
    assert!(matches!(
        builder.parse_option(["z"]),
        Err(BuildError::ItemNotDeclared(_))
    ));
    assert!(matches!(
        builder.parse_option(["p:A"]),
        Err(BuildError::PrimaryItemColored(_))
    ));
    assert!(builder.parse_option(["p", "q", "x:A", "y:B"]).is_ok());
    assert!(builder.build().is_ok());
}
