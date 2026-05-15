# Gnosis

Parent: [Gnosis Math](../README.md)

`Gnosis/` contains the Lean modules exported by the `Gnosis` aggregate import.
Most files are single-claim or single-domain proof kernels, while subdirectories
group larger families of related claims.

## Key Modules

- [AnarchyJacksonQueueBridge.lean](./AnarchyJacksonQueueBridge.lean) — reads
  the Anarchy/control tradeoff game from `PhysarumRopelength` as a finite
  Jackson queue: control pressure becomes arrival load, distributed local
  agents and boundary signals become service capacity, healthy anarchy clears
  the queue, command-control accumulates backlog, and mycelial capacity
  strictly dominates the human Jackson capacity model at positive node count
  while preserving the intrinsic **3/4** geometric ergodicity rate constraint;
  the same-load mycelial service weakly lowers and clears healthy-anarchy
  backlog without changing that rate.
- [SkyrmsEnergyTax.lean](./SkyrmsEnergyTax.lean) — chapel-grade dynamic energy
  market settlement: node externalities pay a clinamen-floor Skyrms tax,
  attention/truth/diversity define rebate weight, lower externality strictly
  lowers tax and payable burden, and two-node certificates conserve the
  collected redistribution pool.
- [BuddhistAttachmentSkyrms.lean](./BuddhistAttachmentSkyrms.lean) —
  operational analogue of Buddhist attachment for attention carriers; anchors
  `tanha` as failed attention plus unresolved debt, `dukkha` as Skyrms carrying
  cost, and `nirodha` as release that clears the refusal index while preserving
  rebate weight. It also proves the persistence theorem used by runtime
  evidence folds: accumulating failed attention or unresolved debt cannot lower
  operational karma tax, and strictly raises it when the new refusal pressure is
  positive. Its hard-gate review theorem keeps measured promotion evidence
  subordinate to the existing optimal admissible Skyrms/Gatekeeping statement.
- [SmartMaskingBand.lean](./SmartMaskingBand.lean) — bounded token-band /
  phoneme-band formalization for constrained decode. It proves that strict
  finite masks reduce the discrete work budget, and its default-promotion
  predicate requires non-Paris quality prompts so the Paris probe remains a
  smoke test rather than the optimized target. Runtime hook:
  [`distributed-inference` smart-mask benchmark](../../gnosis/distributed-inference/README.md).
- [TwelveSlotSixtySixPairsCarrier.lean](./TwelveSlotSixtySixPairsCarrier.lean) — neutral **`Fin 12`** slots + strict ascending pairs
  keyed to **`pairsIJ`** (**66** rows); shared spine for domain wrappers below.
- [TwelveSlotSixtySixPairsCyclicShear.lean](./TwelveSlotSixtySixPairsCyclicShear.lean) — **`rotateTwelveSlot`** (**`cyclicSucc`**) and
  **`StrictAscendingPair.rotatePairStep`** / **`rotatePairIterate`** aligned with **`rotPairNatAdd`** on chords (**global period `twelve`**).
- [GnosisTimeClock.lean](./GnosisTimeClock.lean) — **`TimePhase`** (**`Fin 12`** dial), **`tick`**, **`phaseOfNatTick`**, bridges to **`Circadian.aeon`**
  and **`TwelveSlot`**; solar-hour stability (**`phaseOfNatTick_add_minutesPerHour_mul`**).
- [EscherichiaColiOrthologTwelveCarrier.lean](./EscherichiaColiOrthologTwelveCarrier.lean) — *E. coli* group bibliography wrapper
  around the shared spine (**genomics motivation only**).
- [NikMapTwelveCarrier.lean](./NikMapTwelveCarrier.lean) — NIKA2 **12**-map / **66** cross-pair wrapper around the same spine
  (**Ponthieu, 2025** cosmological / confusion-noise motivation only).
- [FoilForrestWalk.lean](./FoilForrestWalk.lean) — **`List`** walks over **`pairsIJ`** strict pair steps (**Foil** index scaffold;
  spelling **Forrest** names a friend). Wired from Forest via **`open-source/gnosis/src/forest/forrest-skyrms-bridge.ts`**
  (`encodeHardAssignmentAsForrestWalk`, `bundleSkyrmsWithForrestWalk`) plus **`SkyrmsWalkHooks`** in
  [`skyrms-walk.ts`](../../gnosis/src/forest/skyrms-walk.ts). Lean carries gates only; TS carries **`η`** / Nash dynamics.
- [FoilZeroDragCompatibility.lean](./FoilZeroDragCompatibility.lean) — Init-only FOIL
  zero-drag compatibility certificates: coverage implies zero residual drag,
  drag is antitone in harvested witness coverage, cleared `RfSignalGate`-style
  thresholds select the 10-bit frame, raw byte observations clamp potential
  channels to the Monster-vector floor, the FOIL projection matches the Aeon
  Flow header width, and the quantum-facing carrier matches the already-proved
  twelve-slot noise bridge.
- [IncompletenessBettiFrontier.lean](./IncompletenessBettiFrontier.lean) —
  ties the bounded Goedel proof-budget wall, Betti/void duality, and the
  negative-knowledge ledger into one frontier certificate: residual unmeasured
  paths should be routed to measurement and documented absence, not mistaken
  for completion.
- [SimpsonsParadox.lean](./SimpsonsParadox.lean) — finite two-stratum Simpson's
  paradox witness: treatment A wins within both strata, treatment B wins after
  aggregation, with all rates compared by `Nat` cross-multiplication.
- [SelectionBiasPeriodicHoleBridge.lean](./SelectionBiasPeriodicHoleBridge.lean)
  — packages Wald bombers, Simpson aggregation, and the IUPAC 118-row periodic
  table matrix as one structural-hole lesson: visible survivor/table rows are
  not the whole manifold, and the hidden complement changes the recommendation.
- [SurvivorshipBias.lean](./SurvivorshipBias.lean) — Wald bomber armor witness:
  survivor hit counts select wings/fuselage/tail, missing-loss counts select
  engines/cockpit/fuel tanks, and the engine target routes through the existing
  Simpson/survivorship queue-boundary bridge.
- [RusticChurchContinuumPromotion.lean](./RusticChurchContinuumPromotion.lean) — Init-only
  scaffolding for [`docs/RusticChurchToContinuumChecklist.md`](./docs/RusticChurchToContinuumChecklist.md)
  §§1–3 (promotion tags, measure-entry hypothesis shape, axiom-budget / refusal anchors).
- [BracketedSpace.lean](./BracketedSpace.lean) — rational bracket towers for
  real-like values that preserve a nonzero uncertainty interval, with finite
  Phi refinement certificates suitable for FOIL cache-reuse gates.
- [DiscreteContinuumConstants.lean](./DiscreteContinuumConstants.lean) — Nat-only
  footholds for continuum constants: finite scaled-rational certificates for
  log thresholds, Euler's number partial sums, Archimedean pi brackets,
  square-root brackets, golden-ratio brackets, and named promotion obligations
  for the later analysis layer.
- [DiscreteContinuumConstantRefinement.lean](./DiscreteContinuumConstantRefinement.lean)
  — finite refinement towers over those footholds, proving checked bracket
  widths shrink for Euler's number, pi, sqrt two, and the golden ratio.
- [DiscreteMachineNumberApproximation.lean](./DiscreteMachineNumberApproximation.lean)
  — finite nearest-representable certificates for binary64 (`f64`, Java
  `double`, TypeScript `number`) and binary32 (`f32`, Java `float`) cells for
  pi, Euler's number, sqrt two, and the golden ratio, with midpoint promotion
  obligations isolating the continuum proof.
- [DiscreteMachineNumberFastPath.lean](./DiscreteMachineNumberFastPath.lean)
  — closed Boolean skip paths that decide whether an existing rational bracket
  already lies inside a finite machine cell's midpoint interval; current
  constant brackets record honest `false` frontier status until refinements
  become tight enough.
- [PeriodicAeonPhaseBridge.lean](./PeriodicAeonPhaseBridge.lean) - maps the **118**
  discrete periodic carrier band to the **12**-fold aeon torus (`Fin ambientDim`),
  charts to **`Fin twelve`** for `AeonCycleTwelveShadow`, and identifies enumeration phase with
  **`iteratedCyclicSucc`** from **`twelveCycleOrigin`** (still not chemical group placement).
- [RL.lean](./RL.lean) - Buleyean reinforcement-learning primitives, including
  rejection information and rejection-trained budget growth.
- [RLBudgetLedgerBridge.lean](./RLBudgetLedgerBridge.lean) - bridge proving
  one-bule-per-rejection ledger spend matches rejection-trained budget growth
  and weakly lowers Buleyean RL cost.
- [ProvableRandomness.lean](./ProvableRandomness.lean) - Init-only randomness
  boundary certificate: deterministic byte cycles cover all 256 byte values,
  a Lacey-style DNA-dimension stream covers the byte boundary exactly once per
  cycle, and FOIL ambient entropy enters as a runtime certificate before Lean
  proves the 10-bit projection gate.

## Child Directories

- [docs](./docs/README.md) - short bridge-discipline notes (not Lean-checked).
- [Contrarian](./Contrarian/README.md) - compact anti-theorem modules for claims
  where challenge, absence, latency, silence, or other apparent deficits map to
  formal benefits under explicit assumptions.
- [Civil](./Civil/README.md) - civil-engineering and transportation kernels,
  including queue flow, route equilibrium, and quasicrystal stoplight timing.
- [EntropyBridge](./EntropyBridge/README.md) - entropy bridge modules.
- [GnosisMath](./GnosisMath/README.md) - internal Gnosis math support modules.
- [GreekLogicCanon](./GreekLogicCanon/README.md) - Greek logic canon modules.

## Aggregate Import

`../Gnosis.lean` is the package-level aggregate import. Add new modules there
when they should participate in `lake build Gnosis`.
