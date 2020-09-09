import { prove } from 'rify';

// a credential in Explicit Ethos form
const CREDENTIAL_EE = [];
const RULES = [
  // [
  //   [
  //     // if [super? claims [super? defersTo minor?]]
  //     [Any("super"), Exa("claims"), Any("claim1")],
  //     [Any("claim1"), Exa("subject"), Any("super")],
  //     [Any("claim1"), Exa("predicate"), Exa("defersTo")],
  //     [Any("claim1"), Exa("object"), Any("minor")],
  //   ],
  //   [
  //     // then [super? defersTo minor?]
  //     [Any("super"), Exa("defers"), Any("minor")],
  //   ],
  // ],
  // [
  //   [
  //     // if [super? defersTo minor?]
  //     [Any("super"), Exa("defersTo"), Any("minor")],
  //     // and [minor? claims claim1?]
  //     [Any("minor"), Exa("claims"), Any("claim1")],
  //   ],
  //   [
  //     // then [super? claims claim2?]
  //     [Any("super"), Exa("claims"), Any("claim1")],
  //   ],
  // ],
];

test('The proof is the output of the theorem prover (DCK-69).', () => {
  // call `prove` then use the output of `prove` to verify the ruleset
  const composite_claims = [];
  let proof = prove(CREDENTIAL_EE, composite_claims, RULES);
});

test('If an invalid proof is provided, then the program correctly judges it to be invalid.', () => {
  // // bad rule application
  // let facts: Vec<Claim<& str>> = vec![["a", "a", "a"]];
  // let rules_v1 = decl_rules::<& str, & str > (& [[
  //   & [[Any("a"), Exa("a"), Exa("a")]],
  //   & [[Exa("b"), Exa("b"), Exa("b")]],
  // ]]);
  // let rules_v2 = decl_rules::<& str, & str > (& [[
  //   & [[Exa("a"), Exa("a"), Exa("a")]],
  //   & [[Exa("b"), Exa("b"), Exa("b")]],
  // ]]);
  // let composite_claims = vec![["b", "b", "b"]];
  // let proof = prove(& facts, & composite_claims, & rules_v1).unwrap();
  // let err = validate(& rules_v2, & proof).unwrap_err();
  // assert_eq!(err, Invalid:: BadRuleApplication);

  // // no_such_rule
  // let facts: Vec<Claim<& str>> = vec![["a", "a", "a"]];
  // let rules = decl_rules::<& str, & str > (& [[
  //   & [[Exa("a"), Exa("a"), Exa("a")]],
  //   & [[Exa("b"), Exa("b"), Exa("b")]],
  // ]]);
  // let composite_claims = vec![["b", "b", "b"]];
  // let proof = prove(& facts, & composite_claims, & rules).unwrap();
  // let err = validate::<& str, & str > (& [], & proof).unwrap_err();
  // assert_eq!(err, Invalid:: NoSuchRule);
  expect(1 + 1).toBe(3);
});

// User can input a proof of composite cred derived from set of creds.
// The verification result is provided to the user.
// The program reports all composite claims which were shown to be implied.
// A program correctly validates the proof.
test('valid proof', () => {
  expect(1 + 1).toBe(3);
});
