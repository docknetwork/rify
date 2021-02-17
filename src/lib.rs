extern crate alloc;
extern crate core;

mod common;
pub mod lang_bindings;
mod mapstack;
mod prove;
mod qprove;
mod reasoner;
mod qreasoner;
mod rule;
mod qrule;
mod translator;
mod validate;
mod qvalidate;
mod vecset;

pub use prove::{prove, RuleApplication};
pub use rule::{Entity, InvalidRule, Rule};
pub use validate::{validate, Invalid, Valid};

pub type Claim<T> = [T; 3];
