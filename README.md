# rify

[![Crates.io](https://img.shields.io/crates/v/rify)](https://crates.io/crates/rify)
[![Docs](https://docs.rs/rify/badge.svg)](https://docs.rs/rify)
[![npm](https://img.shields.io/npm/v/rify)](https://www.npmjs.com/package/rify)

Rify is a [forward chaining](https://en.wikipedia.org/wiki/Forward_chaining) [inference engine](https://en.wikipedia.org/wiki/Inference_engine) designed specifically for use on in-memory RDF graphs.

It accepts conjunctive rules with limited expressiveness so reasoning is bounded by `O(n^k)` in both memory and in computation where n is the number of nodes in the input RDF graph.

Reasoning generates a proof which can be used to quickly verify the result pragmatically.

Logical rules are defined as if-then clauses. Something like this:

```rust
struct Rule {
    if_all: Vec<[Entity; 3]>,
    then: Vec<[Entity; 3]>,
}

enum Entity {
    /// A named variable with an unknown value.
    Any(String),
    /// A literal RDF node.
    Exactly(RdfNode),
}

// actual definitions of these types are templated but this is the gist
```

# Use

Two functions are central to this library: `prove` and `validate`.

```rust
// Example use of `prove`

use rify::{
    prove,
    Entity::{Any, Exactly},
    Rule, RuleApplication,
};

// (?a, is, awesome) ∧ (?a, score, ?s) -> (?a score, awesome)
let awesome_score_axiom = Rule::create(
    vec![
        [Any("a"), Exactly("is"), Exactly("awesome")], // if someone is awesome
        [Any("a"), Exactly("score"), Any("s")],    // and they have some score
    ],
    vec![[Any("a"), Exactly("score"), Exactly("awesome")]], // then they must have an awesome score
)?;

assert_eq!(
    prove::<&str, &str>(
        &[["you", "score", "unspecified"], ["you", "is", "awesome"]],
        &[["you", "score", "awesome"]],
        &[awesome_score_axiom]
    )?,
    &[
        // (you is awesome) ∧ (you score unspecified) -> (you score awesome)
        RuleApplication {
            rule_index: 0,
            instantiations: vec!["you", "unspecified"]
        }
    ]
);
```

```rust
// Example use of `validate`

use rify::{
    prove, validate, Valid,
    Entity::{Any, Exactly},
    Rule, RuleApplication,
};

// (?a, is, awesome) ∧ (?a, score, ?s) -> (?a score, awesome)
let awesome_score_axiom = ...;

let proof = vec![
    // (you is awesome) ∧ (you score unspecified) -> (you score awesome)
    RuleApplication {
        rule_index: 0,
        instantiations: vec!["you", "unspecified"]
    }
];

let Valid { assumed, implied } = validate::<&str, &str>(
    &[awesome_score_axiom],
    &proof,
).map_err(|e| format!("{:?}", e))?;

// Now we know that under the given rules, if all RDF triples in `assumed` are true, then all
// RDF triples in `implied` are also true.
```

# recipies

In addition to normal cargo commands like `cargo test` and `cargo check` the `./justfile`
defines some scripts which can be useful during development. For example, `just js-test` will
test the javascript bindings to this library. See `./justfile` for more.

# License

This project is licensed under either of Apache License, Version 2.0 or MIT license, at your option.
