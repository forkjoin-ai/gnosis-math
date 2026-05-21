# Greek Logic Canon

Parent: [Gnosis](../README.md)

The historical monolith [`../GreekLogicCanon.lean`](../GreekLogicCanon.lean) imports Mathlib and a wide Gnosis chain. New material that must stay **Init-only** for the math sandbox policy lives in this directory first, then promotes into the monolith after Mathlib peeling.

See [docs/MATH_SANDBOX.md](../../../../docs/MATH_SANDBOX.md) § next-phase integration.

## Modules

- [DiscreteBoundary.lean](./DiscreteBoundary.lean) - Init-only seed for finite
  combinatorial fragments before promotion into the wider Greek logic canon.
- [PropositionalInference.lean](./PropositionalInference.lean) - Init-only
  formalization of the common propositional inference rules: modus ponens,
  modus tollens, disjunctive syllogism, hypothetical syllogism,
  simplification, conjunction, addition, and constructive dilemma.
- [propositional-inference.gg](./propositional-inference.gg) - GG formula-tree
  topology mirror of those propositional inference rules.
- [QuestionVacuum.lean](./QuestionVacuum.lean) - Init-only finite
  question-vacuum formalization: 12 generic question formats, 7 Precision Q&A
  categories, 42 Precision Q&A subcategories, and exactly 81 single-hole
  question formats across the 24 valid categorical syllogisms.
- [question-vacuum.gg](./question-vacuum.gg) - GG topology mirror of the
  question format, state, and syllogistic single-hole catalogs.
- [precision-qa-question-map.gg](./precision-qa-question-map.gg) - GG mirror
  mapping the Precision Q&A category/subcategory framework onto finite
  question-format tags for closure-diff generation.
- [SyllogisticLogic.lean](./SyllogisticLogic.lean) - Init-only first-order
  formalization of the 24 valid categorical syllogisms, with unconditional
  forms separated from conditional forms that require explicit existential
  import for `S`, `M`, or `P`.
- [syllogistic-logic.gg](./syllogistic-logic.gg) - GG topology mirror of the
  same 24 forms for aeon-logic fact-finding and fact-checking scans.
- [Tetrapharmakos.lean](./Tetrapharmakos.lean) - Init-only Epicurean
  tetrapharmakos boundary module.
