extern crate alloc;
extern crate core;

mod common;
mod infer;
mod mapstack;
mod prove;
mod reasoner;
mod rule;
mod translator;
mod validate;
mod vecset;

pub use infer::infer;
pub use prove::{prove, CantProve, RuleApplication};
pub use rule::{Entity, InvalidRule, Rule};
pub use validate::{validate, Invalid, Valid};

#[cfg(doctest)]
mod test_readme {
    macro_rules! external_doc_test {
        ($x:expr) => {
            #[doc = $x]
            extern "C" {}
        };
    }

    external_doc_test!(include_str!("../README.md"));
}
