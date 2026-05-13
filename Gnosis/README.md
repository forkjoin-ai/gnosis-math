# Gnosis

Parent: [Gnosis Math](../README.md)

`Gnosis/` contains the Lean modules exported by the `Gnosis` aggregate import.
Most files are single-claim or single-domain proof kernels, while subdirectories
group larger families of related claims.

## Key Modules

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
- [RusticChurchContinuumPromotion.lean](./RusticChurchContinuumPromotion.lean) — Init-only
  scaffolding for [`docs/RusticChurchToContinuumChecklist.md`](./docs/RusticChurchToContinuumChecklist.md)
  §§1–3 (promotion tags, measure-entry hypothesis shape, axiom-budget / refusal anchors).
- [PeriodicAeonPhaseBridge.lean](./PeriodicAeonPhaseBridge.lean) - maps the **118**
  discrete periodic carrier band to the **12**-fold aeon torus (`Fin ambientDim`),
  charts to **`Fin twelve`** for `AeonCycleTwelveShadow`, and identifies enumeration phase with
  **`iteratedCyclicSucc`** from **`twelveCycleOrigin`** (still not chemical group placement).
- [RL.lean](./RL.lean) - Buleyean reinforcement-learning primitives, including
  rejection information and rejection-trained budget growth.
- [RLBudgetLedgerBridge.lean](./RLBudgetLedgerBridge.lean) - bridge proving
  one-bule-per-rejection ledger spend matches rejection-trained budget growth
  and weakly lowers Buleyean RL cost.

## Child Directories

- [docs](./docs/README.md) - short bridge-discipline notes (not Lean-checked).
- [Contrarian](./Contrarian/README.md) - compact anti-theorem modules for claims
  where challenge, absence, latency, silence, or other apparent deficits map to
  formal benefits under explicit assumptions.
- [EntropyBridge](./EntropyBridge/README.md) - entropy bridge modules.
- [GnosisMath](./GnosisMath/README.md) - internal Gnosis math support modules.
- [GreekLogicCanon](./GreekLogicCanon/README.md) - Greek logic canon modules.

## Aggregate Import

`../Gnosis.lean` is the package-level aggregate import. Add new modules there
when they should participate in `lake build Gnosis`.
