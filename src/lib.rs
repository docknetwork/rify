extern crate alloc;
extern crate core;

mod common;
mod lang_bindings;
mod mapstack;
mod prove;
mod reasoner;
mod rule;
mod translator;
mod vecset;

pub use prove::{prove, RuleApplication};
pub use rule::{Entity, Rule};
