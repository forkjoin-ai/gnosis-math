# GnosisMath Organization and Integration Roadmap

Parent: [README.md](./README.md)

## Current State

- Ledger: `Gnosis.lean` imports all `899` `Gnosis/**/*.lean` modules.
- Build: `lake build` is green at `902` jobs.
- Anchors remaining: `137` modules are still ledger anchors rather than live Init-only theorem modules.
- Canonicalized live integration layers already restored:
  - `Gnosis.DeficitCapacity`
  - `Gnosis.AmericanFrontier`
  - `Gnosis.DiversityOptimality`
  - `Gnosis.ImmigrationTopology`
  - `Gnosis.DiversityIsConcurrency`
  - `Gnosis.CommunityDominance`
  - `Gnosis.ImmigrationDiversityIntegration`
  - `Gnosis.CoveringSpaceCausality` now reuses the canonical deficit surface instead of shadowing it.

## Objective

Turn the current ledger-complete package into an organized, honest Init-only integration surface:

1. Keep the full package building at every step.
2. Replace anchors with real theorem modules in dependency order.
3. Move duplicated theorem names onto canonical modules.
4. Leave Mathlib-shaped or colliding sketches ledgered until they are rebuilt honestly.

## Dependency Order

1. Core arithmetic and deficit surface
   Status: done
   Modules: `DeficitCapacity`, `AmericanFrontier`, `DiversityOptimality`, `CoveringSpaceCausality`
2. Immigration and transport-growth surface
   Status: partially done
   Target modules: `ImmigrationTopology`, `ImmigrationDiversityIntegration`, `CommunityDominance`, `DiversityIsConcurrency`, `DiversityUnwound`
3. Post-linear / frontier composition surface
   Status: pending
   Target modules: `PostLinear`, `DeficitCapacity` dependents, frontier-ordering files
4. Celestial classifier and orbit surface
   Status: pending
   Target modules: `CelestialGainControlPrediction`, `CelestialNaturalDivision`, `CelestialSurveySearch`, `CelestialPlanetTaxonomy`
5. Cancer / prediction clusters
   Status: pending
   Target modules: `Cancer/*`, `PredictionProofs`, neighboring bridge modules
6. Deep composition and philosophical clusters
   Status: pending
   Target modules: `DeepReduction`, `Novel*`, `Philosophical*`, `Community*`
7. Collision cleanup and namespace compression
   Status: pending
   Target modules: bridge/oracle subtrees that duplicate declarations or reintroduce Mathlib-only shapes

## Rules For Execution

- A module leaves anchor status only when it compiles as a real Init-only module.
- Compatibility theorem names belong in one canonical module, not repeated in multiple files.
- A tranche is complete only when `lake build` stays green after the refactor.
- If a module still depends on missing Mathlib surfaces, it stays ledgered and is documented as such.

## Tranche Log

- Done: restored the deficit/frontier/diversity integration chain and canonicalized `CoveringSpaceCausality`.
- Done: restored `ImmigrationTopology`, `DiversityIsConcurrency`, `CommunityDominance`, and `ImmigrationDiversityIntegration` as live Init-only modules.
- Next: restore `DiversityUnwound` or a post-linear/frontier dependent so the immigration surface fans back out into more real theorem files.
