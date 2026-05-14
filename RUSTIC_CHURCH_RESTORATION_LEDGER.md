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
| `Gnosis/NegotiationEquilibrium.lean` | 2544 | restored | Restored Nat negotiation channel, BATNA boundary, concession gradient, coherence, and finite heat counters. Void-walking, semiotic bridge, and analytic heat shells remain deferred until their Init cores are present. |
| `Gnosis/BeautyOptimality.lean` | 2188 | restored | Restored finite workload/objective monotonicity, zero-deficit Pareto boundary, additive composition witness, and `Gnosis.Axioms` schema instantiation. Real-valued convexity and external `ForkRaceFoldTheorems.Axioms` shells remain deferred. |
| `Gnosis/LandauerBuley.lean` | 1669 | restored | Restored finite erasure/heat tax core and bridged it to the bracket/refinement precision stack (`ThermodynamicRefinement`, `MythOfInfinitePrecision`). PMF, Real, ENNReal, and entropy shells remain deferred. |
| `Gnosis/InterferenceCoarsening.lean` | 1215 | restored | Restored finite coarsening witness layer, schema bridge, zero-vent repair theorem, and concrete two-by-four collapse certificate. Analytic graph quotient and measure-theoretic shells remain deferred. |
| `Gnosis/CommunityCompositions.lean` | 1154 | restored | Restored finite local-to-global community aggregation, max/sum merge bounds, monotone remaining-burden laws, community discount bridge, and coarsening-witness handoff. Higher-level application shells remain deferred. |
| `Gnosis/KnotTheory/KnotTheoryGrind.lean` | 1053 | restored | Restored finite connected-sum accounting, chain-crossing/cost laws, session-ledger decomposition, clinamen-lift one-crossing bridge, and nontrivial-chain positive-tax theorem. Spiral/scheduler-heavy shells remain deferred. |
| `Gnosis/PhilosophicalAllegories.lean` | 726 | restored | Restored typed allegory carriers, non-identity morphism constraints, composition accounting, positive information-gain certificates, and a small master theorem. Domain-specific semiotic/Buleyean applications remain deferred. |
| `Gnosis/GreekLogicCanon.lean` | 711 | restored | Restored finite Greek canon entries, citation witnesses, acyclic rank laws, citation span positivity, and bridge morphisms into `PhilosophicalAllegories`. Broad paradox-resolution shells remain deferred. |
| `Gnosis/Cancer/CancerTopology.lean` | 691 | restored | Restored finite vent-capacity topology, deficit severity ordering, mutation severity witnesses, GBM-style numeric profiles, and treatment-restoration bridge to `CancerTreatments`. Biological/empirical claims remain deferred. |
| `Gnosis/CombinatorialBruteForce.lean` | 638 | restored | Restored finite search-space accounting, unresolved/full-scan laws, pruning survivor bounds, work-savings inequalities, and race/fold winner/vent identities. Broad theorem-family composition shells remain deferred. |
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
- `Gnosis/BeautyOptimality.lean`: restored from placeholder to finite Init core. Verified with `lake build Gnosis.BeautyOptimality`.
- `Gnosis/LandauerBuley.lean`: restored from placeholder to finite Init core. Verified with `lake build Gnosis.LandauerBuley`.
- `Gnosis/InterferenceCoarsening.lean`: restored from placeholder to finite Init core. Verified with `lake build Gnosis.InterferenceCoarsening`.
- `Gnosis/CommunityCompositions.lean`: restored from placeholder to finite Init core. Verified with `lake build Gnosis.CommunityCompositions`.
- `Gnosis/KnotTheory/KnotTheoryGrind.lean`: restored from placeholder to finite Init core. Verified with `lake build Gnosis.KnotTheory.KnotTheoryGrind`.
- `Gnosis/PhilosophicalAllegories.lean`: restored from placeholder to finite Init core. Verified with `lake build Gnosis.PhilosophicalAllegories`.
- `Gnosis/GreekLogicCanon.lean`: restored from placeholder to finite Init core. Verified with `lake build Gnosis.GreekLogicCanon`.
- `Gnosis/Cancer/CancerTopology.lean`: restored from placeholder to finite Init core. Verified with `lake build Gnosis.Cancer.CancerTopology`.
- `Gnosis/CombinatorialBruteForce.lean`: restored from placeholder to finite Init core. Verified with `lake build Gnosis.CombinatorialBruteForce`.
- High-priority collapsed ledger list is now restored through `Gnosis/CombinatorialBruteForce.lean`; remaining restored row in this section is `Gnosis/Cancer/CancerTreatments.lean`.
