# Rustic Church → continuum promotion checklist

This note records **discipline** for moving gnosis-math carriers from **Init-only /
kernel-decidable** strata toward **ℝ**, **measure**, or **QCD-colored** mathematics.
It does not prove any continuum theorem by itself.

## 1. Type promotion map (what changes layer)

| Discrete / Init carrier | Before promoting, ask… | Typical promoted target (future Mathlib-era) |
|-------------------------|------------------------|-----------------------------------------------|
| `Nat`, `Fin n`, lists of `Nat` (`KPlane` rows) | Is every ops claim still exact mod rounding? | `ℝ`, `Rn`, structured finite-dimensional spaces |
| `Fin 12` phase / column torus | Is modular arithmetic the **whole** story or a chart index? | `S¹` or `ℝ / 12ℤ` with explicit quotient witnesses |
| `PeriodicCalibrationMorphism` mass shadows | Are digits SI-backed or morphism hypotheses? | CODATA-backed `ℝ` ratios + uncertainty propagation |
| God-formula `Nat` weights (`godWeight`) | Is the slice still the **same** inequality `v ≤ R`? | Same predicate on `ℝ` with ordered-semiring lemmas |
| Gauge / color prose (“QCD”) | Are we naming **SU(3)** reps or metaphorical routing? | Bundled **fiber 3** + connection **only** if imported |

## 2. Measure / probability entry gates

- State the **σ-algebra** or finite supporting set before integrating.
- If using pushforward from `Fin n`, prove **measurability** is trivial (discrete σ-algebra).
- Prefer **explicit distributions** over informal “random walk” language.

## 3. Axiom budget (tie to `PeriodicAtBridge`)

- Any equality tying kernel certificates to **meters, seconds, eV, barns, …** belongs in a **named morphism or hypothesis record**, not as a stray `rfl` across namespaces.
- Reuse refusal posture: see `Gnosis.PeriodicAtBridge.refusalCalibrationStrings` (“SI without calibration”).
- New continuum axioms need a **one-line audit trail**: which discrete theorem they refine, and which experiment would falsify the bridge.

## 4. Non-unification rules (anti-confusion)

These Lean symbols **must not** silently identify:

- `DiscretePeriodicCarrier.idx` (118-band enumeration)  
- Mendeleev **group / period** placement (layout-specific)  
- `omegaWeightedSyntheticIonizationMicroEv` (ledger filler)  
- Tabulated CODATA / JSON IE or mass  

- `Fin ambientDim` phase from **`idx.val % ambientDim`** (`Gnosis.PeriodicAeonPhaseBridge`)  
- Chemical “group 1 … group 18” indices without an explicit **lookup table morphism**.

## 5. Standing-wave coordinate bridge reminder

`Gnosis.AeonStandingWaveCoordinateBridge` embeds Death #1 standing-wave data into a **Grassmannian coordinate-plane chart** with **`d = Circadian.aeon = ambientDim`**.  
Module doc: **not** a smooth `ℝ²` manifold theorem—promotion is still explicit.

## 6. Audit snapshot (Periodic / Aeon / bridge hygiene)

**Automated grep posture (informal):**

- No top-level `axiom` declarations surfaced under `Gnosis/` in a recent scan.
- Most files document “zero `sorry`”; spot-check any module that **imports** heavier analytic stubs when Mathlib arrives.

Re-run verification when adding imports:

```bash
rg '^axiom\\b' open-source/gnosis-math/Gnosis --glob '*.lean'
rg '\\bsorry\\b' open-source/gnosis-math/Gnosis --glob '*.lean' # inspect hits (many are comments)
```

## 7. Narrow lemma targets (good incremental work)

- ~~Enumerate **`enumerationPhaseFinTwelve`** as **`iteratedCyclicSucc h12`** from **`twelveCycleOrigin`**~~ — see
  `Gnosis.PeriodicAeonPhaseBridge.enumeration_phase_fin_twelve_eq_iterated_cyclic_succ_from_origin` plus chart lemmas
  `fin_twelve_ambient_roundtrip` / `ambient_twelve_roundtrip`.
- Factor **`enumerationPhaseFinAmbient`** through **chart composition** once a second aeon coordinate chart beside **`[0,1]`**
  is packaged beside `aeonBasisCoordinatePlane`.
- Relate **gcd stride return** (`AeonTwelveCarrierList.stride_origin_return`, varying **`s`**) to **enumeration ticks**
  via **`Gnosis.PeriodicAeonPhaseBridge`**: **`Fin twelve`** **`enumeration_phase_stride_square`** /
  **`enumerationPhaseFinTwelveAfterStride`**, ambient carrier square **`enumeration_phase_stride_square_ambient`**, **`fin_ambient_to_twelve_iterate_cyclic_succ`**, ambient packaging **`enumerationPhaseFinAmbientAfterStride`** with
  **`enumeration_phase_stride_square_via_ambient_chart`**, **`fin_ambient_to_twelve_after_stride`**, **`fin_twelve_to_ambient_after_stride`**, discrete periods **`iterated_cyclic_succ_period_ambient`**, **`iterate_twelve_from_origin_is_period_via_ambient`**, **`iterate_ambient_from_origin_via_twelve_period`**, inverse iterate **`fin_twelve_to_ambient_iterate_cyclic_succ`**, single-step core **`DiscreteClosedTimelikeStep.iteratedCyclicSucc_one_eq_cyclicSucc`** with chart **`fin_ambient_to_twelve_cyclic_succ`** / **`fin_twelve_to_ambient_cyclic_succ`**, value lemma **`enumeration_phase_stride_square_val`**,
  residue pullback (**`nat_mod_n_add_stride_pull_residue`** / **`nat_mod_twelve_add_stride_pull_residue`** / **`nat_mod_ambient_add_stride_pull_residue`**), gcd closure **`stride_origin_return_at_twelve_cycle_origin`**,
  and **`twelve_cycle_origin_eq_finZero`** for reuse with **`finZero`** lemmas.
- When Pauling (or similar) columns exist in calibration data, state **decidable** ε-harmonic predicates vs hydrogen anchors.
