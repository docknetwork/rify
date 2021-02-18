extern crate alloc;
extern crate core;

mod common;
pub mod lang_bindings;
mod mapstack;
mod prove;
mod reasoner;
mod rule;
mod translator;
mod validate;
mod vecset;

pub use prove::{prove, RuleApplication};
pub use rule::{Entity, InvalidRule, Rule};
pub use validate::{validate, Invalid, Valid};

#[cfg(doctest)]
mod test_readme {
  macro_rules! external_doc_test {
    ($x:expr) => {
        #[doc = $x]
        extern {}
    };
  }

  external_doc_test!(include_str!("../README.md"));
}
