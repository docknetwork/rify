# rify

[![Crates.io](https://img.shields.io/crates/v/rify)](https://crates.io/crates/rify)
[![Docs](https://docs.rs/rify/badge.svg)](https://docs.rs/rify)
[![npm](https://img.shields.io/npm/v/rify)](https://www.npmjs.com/package/rify)

Rify is a [forward chaining](https://en.wikipedia.org/wiki/Forward_chaining) [inference engine](https://en.wikipedia.org/wiki/Inference_engine) designed specifically for use on in-memory RDF graphs.

It accepts conjunctive rules with limited expressiveness so reasoning is bounded by `O(n^k)` in both memory and in computation where n is the number of nodes in the input RDF dataset.

Given premises and target statement[s], rify can generate a proof which can be used to quickly verify the result programatically.

Logical rules are defined as if-then clauses. Something like this:

```rust
struct Rule {
    if_all: Vec<[Entity; 4]>,
    then: Vec<[Entity; 4]>,
}

// Notice it's `[Entity; 4]`, not `[Entity; 3]`. This reasoner operates on Rdf Quads, not triples.
// You can still reason over triples by binding a unique resource e.g. `RdfTerm::DefaultGraph`
// as the graph in all rules and all quads.

enum Entity {
    /// A a named variable with an unknown value.
    Unbound(String),
    /// A literal with a constant value.
    Bound(RdfTerm),
}

// actual definitions of these types are templated but this is the gist

// You get to define this type! Here is an example definition.
enum RdfTerm {
    Blank(usize),
    Iri(String),
    Literal {
        datatype: String,
        value: String,
        lang_tag: Option<String>,
    },
    DefaultGraph,
}
```

Rify doesn't care whether its input and output is valid rdf. For example, it will happily accept a quad whose predicate is a literal. https://www.w3.org/TR/rdf11-concepts/#section-triples

# Use

Three functions are central to this library: `prove`, `validate`, and `infer`.

## prove

```rust
use rify::{
    prove,
    Entity::{Unbound, Bound},
    Rule, RuleApplication,
};

// (?a, is, awesome) ∧ (?a, score, ?s) -> (?a score, awesome)
let awesome_score_axiom = Rule::create(
    vec![
        // if someone is awesome
        [Unbound("a"), Bound("is"), Bound("awesome"), Bound("default_graph")],
        // and they have some score
        [Unbound("a"), Bound("score"), Unbound("s"), Bound("default_graph")],
    ],
    vec![
        // then they must have an awesome score
        [Unbound("a"), Bound("score"), Bound("awesome"), Bound("default_graph")]
    ],
).expect("invalid rule");

assert_eq!(
    prove::<&str, &str>(
        // list of already known facts (premises)
        &[
            ["you", "score", "unspecified", "default_graph"],
            ["you", "is", "awesome", "default_graph"]
        ],
        // the thing we want to prove
        &[["you", "score", "awesome", "default_graph"]],
        // ordered list of logical rules
        &[awesome_score_axiom]
    ),
    Ok(vec![
        // the desired statement is proven by instantiating the `awesome_score_axiom`
        // (you is awesome) ∧ (you score unspecified) -> (you score awesome)
        RuleApplication {
            rule_index: 0,
            instantiations: vec!["you", "unspecified"]
        }
    ])
);
```

# validate

```rust
use rify::{
    prove, validate, Valid,
    Rule, RuleApplication,
    Entity::{Bound, Unbound}
};

// same as above
let awesome_score_axiom = Rule::create(
    vec![
        [Unbound("a"), Bound("is"), Bound("awesome"), Bound("default_graph")],
        [Unbound("a"), Bound("score"), Unbound("s"), Bound("default_graph")],
    ],
    vec![[Unbound("a"), Bound("score"), Bound("awesome"), Bound("default_graph")]],
).expect("invalid rule");

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
).expect("invalid proof");

// Now we know that under the given rules, if all quads in `assumed` are true, then all
// quads in `implied` are also true.
```

## infer

```rust
use rify::{infer, Entity::{Unbound, Bound}, Rule};

// (?a, is, awesome) ∧ (?a, score, ?s) -> (?a score, awesome)
let awesome_score_axiom = Rule::create(
    vec![
        // if someone is awesome
        [Unbound("a"), Bound("is"), Bound("awesome"), Bound("default_graph")],
        // and they have some score
        [Unbound("a"), Bound("score"), Unbound("s"), Bound("default_graph")],
    ],
    vec![
        // then they must have an awesome score
        [Unbound("a"), Bound("score"), Bound("awesome"), Bound("default_graph")]
    ],
).expect("invalid rule");

let mut facts = vec![
    ["you", "score", "unspecified", "default_graph"],
    ["you", "is", "awesome", "default_graph"]
];

let new_facts = infer::<&str, &str>(&facts, &[awesome_score_axiom]);
facts.extend(new_facts);

assert_eq!(
    &facts,
    &[
        ["you", "score", "unspecified", "default_graph"],
        ["you", "is", "awesome", "default_graph"],
        ["you", "score", "awesome", "default_graph"],
    ],
);
```

# Recipes

In addition to normal cargo commands like `cargo test` and `cargo check` the `./justfile`
defines some scripts which can be useful during development. For example, `just js-test` will
test the javascript bindings to this library. See `./justfile` for more.

# License

This project is licensed under either of Apache License, Version 2.0 or MIT license, at your option.
