# Apotheosis

Parent: [Gnosis](../README.md)

`Gnosis/Apotheosis/` contains mechanical-brain carrier definitions migrated
from the legacy `open-source/gnosis/lean/Lean/Apotheosis` tree into the
`gnosis-math` Lean hierarchy.

## Modules

- [ApotheosisDefs.lean](./ApotheosisDefs.lean) — core goal, belief, witness,
  reasoning-step, specialist, agent, and parliament-decision carriers with the
  irreducible-goal theorem and explicit axiom boundaries for semantic claims.
- [MechanicalIntrospection.lean](./MechanicalIntrospection.lean) — agent
  self-model and meta-reasoning carriers with explicit axiom boundaries for
  self-knowledge, DAG structure, bounded introspection, correction, and
  well-foundedness claims.
- [ParliamentConsensus.lean](./ParliamentConsensus.lean) — specialist-vote and
  parliament carriers with explicit axiom boundaries for transitivity, fair
  weighting, dissent preservation, convergence, and diversity claims.
- [SystemOneTwo.lean](./SystemOneTwo.lean) — fast/slow cognitive response
  carriers, strategy selection predicates, and explicit axiom boundaries for
  latency, energy, accuracy, parallel execution, and historical learning claims.
- [TelemetryWitness.lean](./TelemetryWitness.lean) — witness-frame,
  witness-chain, codec, compactness, and witness-stream carriers with explicit
  axiom boundaries for DAG, causality, validity, auditability, and losslessness
  claims.
