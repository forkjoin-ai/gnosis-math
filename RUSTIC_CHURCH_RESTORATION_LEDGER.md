# Rustic Church Restoration Ledger

This ledger tracks Lean files that were collapsed into structural placeholders and should be restored as Init-only Rustic Church modules rather than blindly reverted.

## Collapse Evidence

The main collapse point is:

- commit: `09b31d0d91501631769d3fe517e3191ab48234b7`
- subject: `chore: sync submodule changes`
- date: Thu Apr 30 2026

The collapse pattern is a large theorem sketch replaced by a small `import Init` file with a placeholder theorem and prose that describes a future rebuild. That wording is stale now: the Init-only rebuild is the standing proof contract, not an unfinished migration exception.

## Restoration Rule

Do not restore these files by reverting the collapse commit. The old files often depended on Mathlib surface area, generated APIs, automation, or speculative theory modules that no longer belong in the Init-only package.

For each file:

1. Recover the original definitions and theorem families from git history.
2. Separate the finite Init-compatible core from Real, ENNReal, PMF, BigOperators, tactic-heavy, or external API shells.
3. Rebuild the core with `import Init`.
4. Keep harder shells as named restoration targets only when their dependencies have honest Init replacements.
5. Remove ledger-anchor language once a module has at least one meaningful structure and theorem family.

## High-Priority Collapsed Files

| File | Deleted lines in collapse history | Current shape | Restore strategy |
| --- | ---: | --- | --- |
| `Gnosis/NegotiationEquilibrium.lean` | 2544 | 17-line placeholder | Restore Nat negotiation channel, BATNA boundary, concession gradient, coherence, and finite heat counters. Defer void-walking and semiotic bridge shells until their Init cores are present. |
| `Gnosis/BeautyOptimality.lean` | 2188 | 17-line placeholder | Restore finite workload/objective monotonicity first. Defer Real-valued convexity and external `ForkRaceFoldTheorems.Axioms` shells. |
| `Gnosis/LandauerBuley.lean` | 1669 | 17-line placeholder | Restore finite erasure/heat tax core. Defer PMF, Real, ENNReal, and entropy shells. |
| `Gnosis/InterferenceCoarsening.lean` | 1215 | 17-line placeholder | Restore finite coarsening/interference order laws. Defer analytic or measure-theoretic claims. |
| `Gnosis/CommunityCompositions.lean` | 1154 | 17-line placeholder | Restore composition structures over finite communities and monotone aggregation laws. |
| `Gnosis/KnotTheory/KnotTheoryGrind.lean` | 1053 | 17-line placeholder | Restore finite knot-token invariants before any topology-heavy shell. |
| `Gnosis/PhilosophicalAllegories.lean` | 726 | 17-line placeholder | Restore typed allegory morphisms and non-identity constraints. |
| `Gnosis/GreekLogicCanon.lean` | 711 | 17-line placeholder | Restore finite canon relationships and citation-like witness structure. |
| `Gnosis/Cancer/CancerTopology.lean` | 691 | 17-line placeholder | Restore finite topology/order witnesses; defer biological claims requiring external models. |
| `Gnosis/CombinatorialBruteForce.lean` | 638 | 17-line placeholder | Restore finite search-space and pruning inequalities. |
| `Gnosis/Cancer/CancerTreatments.lean` | 363 | restored | Restored finite treatment-sequencing core: metabolic gates, checkpoint cascades, senescence waypoints, viral displacement, and counter-vent depletion. |

## First Restoration Target: NegotiationEquilibrium

Original intent recovered from `git show 09b31d0^:Gnosis/NegotiationEquilibrium.lean`:

- `NegotiationChannel`: two parties with multi-dimensional interests compressed into a single offer stream.
- `negotiation_deficit_positive`, `negotiation_deficit_value`, `negotiation_deficit_bounded`: finite deficit laws.
- `NegotiationRound`: an offer fork with one accepted or least-bad alternative.
- `batna_is_void_boundary`, `batna_grows_with_rounds`: rejected offers accumulate as the BATNA boundary.
- `NegotiationState`: per-term rejection counts and complement weights.
- `concession_gradient_positive`, `concession_gradient_monotone`: less-rejected terms receive at least as much concession weight.
- `negotiation_coherence`: shared rejection history gives identical finite update functions.
- heat/regret/context shells: valuable, but should be rebuilt only after their finite dependencies exist.

The honest Init replacement is a finite Nat core:

- deficit is `totalDimensions - 1`, not an `Int` bridge;
- BATNA boundary is `offerCount - 1`;
- concession weight is `rounds - rejectionCount + 1`;
- shared history coherence is definitional equality;
- heat is a finite rejection counter.

## Current Status

- `Gnosis/NegotiationEquilibrium.lean`: restored from placeholder to finite Init core. Verified with `lake build Gnosis.NegotiationEquilibrium`.
- `Gnosis/Cancer/CancerTreatments.lean`: restored from placeholder to finite Init core. Verified with `lake build Gnosis.Cancer.CancerTreatments`.
- `Gnosis/BeautyOptimality.lean`: next large candidate after negotiation compiles.
- `Gnosis/LandauerBuley.lean`: high-value but requires careful split between finite erasure tax and analytic entropy shells.
