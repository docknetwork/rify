extern crate alloc;
extern crate core;

mod common;
mod lang_bindings;
mod mapstack;
mod prove;
mod reasoner;
mod rule;
mod translator;
mod validate;
mod vecset;

pub use prove::{prove, RuleApplication};
pub use rule::{Entity, Rule};
pub use validate::{validate, Invalid, Valid};

pub type Claim<T> = [T; 3];
