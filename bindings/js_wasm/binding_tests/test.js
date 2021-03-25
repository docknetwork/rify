import { prove, validate, infer } from 'rify';
import { expect } from 'chai';

// poor man's replacement for jest because making jest work with webpack+wasm is problematic
function tests(tests) {
  let red = '\x1b[31m';
  let green = '\x1b[32m';
  let reset = '\x1b[0m';

  let stats = [];
  for (let [name, cb] of tests) {
    let passed;
    try {
      cb();
      console.log(green + '✓ ', name, 'passed', reset);
      passed = true;
    } catch (e) {
      console.error(red + '❌', name, reset);
      console.log(e);
      passed = false;
    }
    stats.push(passed);
  }
  let passed_count = stats.filter(a => a).length;
  console.log(`${passed_count}/${tests.length} tests passed`);
  process.exit(passed_count === tests.length ? 0 : 1);
}

/// specify an unbound entity to be included in a rule
function a(str) {
  return { Unbound: str };
}

/// specify a bound entity, i.e. one whith a concrete name to be included in a rule
function e(str) {
  return { Bound: str };
}

// a credential in Explicit Ethos form
const CREDENTIAL_EE = [
  ["root_authority", "claims", "_:0", "default_graph"],
  ["_:0", "subject", "root_authority", "default_graph"],
  ["_:0", "predicate", "defersTo", "default_graph"],
  ["_:0", "object", "issuer", "default_graph"],
  ["issuer", "claims", "_:1", "default_graph"],
  ["_:1", "subject", "bobert", "default_graph"],
  ["_:1", "predicate", "mayPurchase", "default_graph"],
  ["_:1", "object", "http://www.heppnetz.de/ontologies/vso/ns#Vehicle", "default_graph"],
];
const RULES = [
  // to claim deference is deference
  {
    if_all: [
      [a("super"), e("claims"), a("claim1"), e("default_graph")],
      [a("claim1"), e("subject"), a("super"), e("default_graph")],
      [a("claim1"), e("predicate"), e("defersTo"), e("default_graph")],
      [a("claim1"), e("object"), a("minor"), e("default_graph")],
    ],
    then: [
      [a("super"), e("defersTo"), a("minor"), e("default_graph")],
    ],
  },
  // defered entity may make claims on behalf of the deferer
  {
    if_all: [
      [a("super"), e("defersTo"), a("minor"), e("default_graph")],
      [a("minor"), e("claims"), a("claim1"), e("default_graph")],
    ],
    then: [
      [a("super"), e("claims"), a("claim1"), e("default_graph")],
    ],
  },
  // the verifier trusts root_authority
  {
    if_all: [
      [e("root_authority"), e("claims"), a("c"), e("default_graph")],
      [a("c"), e("subject"), a("s"), e("default_graph")],
      [a("c"), e("predicate"), a("p"), e("default_graph")],
      [a("c"), e("object"), a("o"), e("default_graph")],
    ],
    then: [
      [a("s"), a("p"), a("o"), e("default_graph")],
    ],
  }
];

tests([
  ['loading of rules works', () => {
    prove([], [], RULES);
    validate(RULES, []);
  }],

  ['The proof is the output of the theorem prover (DCK-69).', () => {
    // call `prove` then use the output of `prove` to verify the ruleset
    const composite_claims = [
      ["bobert", "mayPurchase", "http://www.heppnetz.de/ontologies/vso/ns#Vehicle", "default_graph"]
    ];
    let proof = prove(CREDENTIAL_EE, composite_claims, RULES);
    expect(proof).to.deep.equal([
      {
        rule_index: 0,
        instantiations: ['root_authority', '_:0', 'issuer']
      },
      {
        rule_index: 1,
        instantiations: ['root_authority', 'issuer', '_:1']
      },
      {
        rule_index: 2,
        instantiations: [
          '_:1',
          'bobert',
          'mayPurchase',
          'http://www.heppnetz.de/ontologies/vso/ns#Vehicle'
        ]
      }
    ]);
    let valid = validate(RULES, proof);
    expect(valid).to.deep.equal({
      assumed: [
        ['_:0', 'object', 'issuer', 'default_graph'],
        ['_:0', 'predicate', 'defersTo', 'default_graph'],
        ['_:0', 'subject', 'root_authority', 'default_graph'],
        [
          '_:1',
          'object',
          'http://www.heppnetz.de/ontologies/vso/ns#Vehicle',
          'default_graph'
        ],
        ['_:1', 'predicate', 'mayPurchase', 'default_graph'],
        ['_:1', 'subject', 'bobert', 'default_graph'],
        ['issuer', 'claims', '_:1', 'default_graph'],
        ['root_authority', 'claims', '_:0', 'default_graph']
      ],
      implied: [
        [
          'bobert',
          'mayPurchase',
          'http://www.heppnetz.de/ontologies/vso/ns#Vehicle',
          'default_graph'
        ],
        ['root_authority', 'claims', '_:1', 'default_graph'],
        ['root_authority', 'defersTo', 'issuer', 'default_graph']
      ]
    });
  }],

  ['If an invalid proof is provided, then the program correctly judges it to be invalid.', () => {
    let err;

    // bad rule application
    err = catch_error(() => validate(RULES, [{ rule_index: 0, instantiations: ['only one'] }]));
    expect(err).to.deep.equal({ InvalidProof: 'BadRuleApplication' });

    // no_such_rule
    err = catch_error(() => validate(RULES, [{ rule_index: 1000, instantiations: [] }]));
    expect(err).to.deep.equal({ InvalidProof: 'NoSuchRule' });
  }],

  // // User can input a proof of composite cred derived from set of creds.
  // // The verification result is provided to the user.
  // // The program reports all composite claims which were shown to be implied.
  // // A program correctly validates the proof.
  // ['valid proof', () => {
  //   expect(1 + 1).to.equal(3);
  // }],

  ['Example from doctest for prove actually runs.', () => {
    // (?a, is, awesome) ∧ (?a, score, ?s) -> (?a score, awesome)
    let awesome_score_axiom = {
      if_all: [
        [{ Unbound: "a" }, { Bound: "is" }, { Bound: "awesome" }, { Bound: "default_graph" }],
        [{ Unbound: "a" }, { Bound: "score" }, { Unbound: "s" }, { Bound: "default_graph" }],
      ],
      then: [
        [{ Unbound: "a" }, { Bound: "score" }, { Bound: "awesome" }, { Bound: "default_graph" }]
      ],
    };
    let proof = prove(
      [
        ["you", "score", "unspecified", "default_graph"],
        ["you", "is", "awesome", "default_graph"],
      ],
      [["you", "score", "awesome", "default_graph"]],
      [awesome_score_axiom],
    );
    expect(proof).to.deep.equal([{
      rule_index: 0,
      instantiations: ["you", "unspecified"]
    }])
  }],

  ['Example from doctest for validate actually runs.', () => {
    // (?a, is, awesome) ∧ (?a, score, ?s) -> (?a score, awesome)
    let awesome_score_axiom = {
      if_all: [
        [{ Unbound: "a" }, { Bound: "is" }, { Bound: "awesome" }, { Bound: "default_graph" }],
        [{ Unbound: "a" }, { Bound: "score" }, { Unbound: "s" }, { Bound: "default_graph" }],
      ],
      then: [
        [{ Unbound: "a" }, { Bound: "score" }, { Bound: "awesome" }, { Bound: "default_graph" }]
      ],
    };
    let known_facts = [
      ["you", "score", "unspecified", "default_graph"],
      ["you", "is", "awesome", "default_graph"],
    ];
    let valid = validate(
      [awesome_score_axiom],
      [{
        rule_index: 0,
        instantiations: ["you", "unspecified"]
      }],
    );
    expect(valid).to.deep.equal({
      assumed: [
        ["you", "is", "awesome", "default_graph"],
        ["you", "score", "unspecified", "default_graph"],
      ],
      implied: [
        ["you", "score", "awesome", "default_graph"],
      ]
    });

    // now we check that all the assumptions made by the proof are known to be true
    for (let f of valid.assumed) {
      if (!known_facts.some(kf => JSON.stringify(kf) === JSON.stringify(f))) {
        throw new Error("Proof makes an unverified assumption.");
      }
    }

    // After verifying all the assumptions in the proof are true, we know that the
    // quads in valid.implied are true with respect to the provided rules.
  }],

  ['Example from doctest for infer actually runs.', () => {
    // (?a, is, awesome) ∧ (?a, score, ?s) -> (?a score, awesome)
    let awesome_score_axiom = {
      if_all: [
        [{ Unbound: "a" }, { Bound: "is" }, { Bound: "awesome" }, { Bound: "default_graph" }],
        [{ Unbound: "a" }, { Bound: "score" }, { Unbound: "s" }, { Bound: "default_graph" }],
      ],
      then: [
        [{ Unbound: "a" }, { Bound: "score" }, { Bound: "awesome" }, { Bound: "default_graph" }]
      ],
    };
    let facts = [
      ["you", "score", "unspecified", "default_graph"],
      ["you", "is", "awesome", "default_graph"],
    ];
    let new_facts = infer(facts, [awesome_score_axiom]);
    facts = facts.concat(new_facts);
    expect(facts).to.deep.equal([
      ["you", "score", "unspecified", "default_graph"],
      ["you", "is", "awesome", "default_graph"],
      ["you", "score", "awesome", "default_graph"],
    ]);
  }],
]);

/// catch whichever error is emitted by when cb is called and return it
/// If no error is emitted, throw a new error
function catch_error(cb) {
  try {
    cb();
  } catch (e) {
    return e;
  }
  throw "expected function to throw an error but no error was thrown";
}
