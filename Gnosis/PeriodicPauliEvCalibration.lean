import Init
import Gnosis.PeriodicAtBridge
import Gnosis.PeriodicPauliEvCalibrationData

/-!
# Pauli-proxy ↔ SI calibration (`PeriodicCalibrationMorphism` + eV tables)

This module **instantiates** the bridge that the ledger anti-theorem refuses without
hypotheses: explicit **CODATA-adjacent chemistry tables** (tabulated relative masses and
first-ionization energies imported from public JSON) plus **hydrogen-anchored** scales
mapping an abstract **Pauli proxy** (`12 · Z`, aligned with the **12** Pauli floor in
`Gnosis.MassHierarchyFromBule`) separately to **micro-electronvolts** and to **micro-u**
mass slope.

What is **not** claimed:

* No theorem identifies `[2, 59]` tower factors with measured ionization structure.
* No theorem proves the linear proxy reproduces ionization energies or masses for all **Z**
  — only the **hydrogen anchor identities** below match the imported columns at **H**.
* Heavy-row ionization entries may be **zero** where the source JSON omits data.

What **is** claimed:

* A concrete `PeriodicCalibrationMorphism` backed by **micro-u** masses.
* A bundled `PeriodicPauliEvCalibrationMorphism` exposing **dual hydrogen anchors**
  (IE + relative mass slopes), tabulated ionization, an explicit **ω'-weighted synthetic IE**
  shadow for missing-table slots, **Ω** and **sopfr** shadows on **Z**, and calibration cores.

Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace PeriodicPauliEvCalibration

open PeriodicAtBridge (DiscretePeriodicCarrier PeriodicCalibrationMorphism MassRatioShadow
  atomicNumber SiContinuumCarrierShadow)

/-! ## Discrete Pauli proxy (kernel-aligned narrative, not SM derivation) -/

/-- Abstract Pauli ledger load per row: **`12 × Z`** (see `MassHierarchyFromBule` floor). -/
def pauliProxyTwelveZ (row : DiscretePeriodicCarrier) : Nat :=
  atomicNumber row * 12

/-! ## Braiding-density shadow (prime ω on **Z**, Init-only) -/

/-- Trial division helper (fuel stops search). -/
def trialFactorAux (n k maxSteps : Nat) : Nat :=
  match maxSteps with
  | 0 => n
  | maxSteps' + 1 =>
      if k * k > n then n
      else if n % k == 0 then k
      else trialFactorAux n (k + 1) maxSteps'

/-- Smallest non-trivial factor discovered by bounded trial division (`n ≥ 2`). -/
def smallestPrimeFactor (n : Nat) : Nat :=
  if n < 2 then 1 else trialFactorAux n 2 n

/-- Total prime factors with multiplicity for **`n ≤ 118`** (fuel-bounded recursion). -/
def primeOmegaAux (n fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
      if n ≤ 1 then 0
      else
        let p := smallestPrimeFactor n
        if p ≥ n then 1 else 1 + primeOmegaAux (n / p) fuel'

def primeOmegaFuel (n fuel : Nat) : Nat :=
  if n ≤ 1 then 0 else primeOmegaAux n fuel

/-- Total prime factors with multiplicity for **`n ≤ 118`** (fuel-bounded recursion). -/
def primeOmega118 (n : Nat) : Nat :=
  primeOmegaFuel n 12

/-! ### Sum-of-prime-factors shadow (sopfr / “routing mass” bookkeeping)

Logarithmically smaller than **Z**, but richer than **Ω** alone: repeated small primes
inflate both **Ω** and **sopfr**; large prime steps inflate **Z** faster than **sopfr**.
This stays Init-only arithmetic — **not** electronegativity or reactivity.
-/

def sopfrAux (n fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
      if n ≤ 1 then 0
      else
        let p := smallestPrimeFactor n
        if p ≥ n then n else p + sopfrAux (n / p) fuel'

def sopfrFuel (n fuel : Nat) : Nat :=
  if n ≤ 1 then 0 else sopfrAux n fuel

/-- Sum of prime factors with multiplicity for **`n ≤ 118`** (same fuel budget as **Ω**). -/
def sopfr118 (n : Nat) : Nat :=
  sopfrFuel n 12

/-- Braiding-density bookkeeping shadow on carriers (counts prime factors of **Z**). -/
def braidPrimeOmegaScore (row : DiscretePeriodicCarrier) : Nat :=
  primeOmega118 (atomicNumber row)

/-- Sum-of-prime-factors (“routing-path mass”) shadow on **Z**. -/
def braidSopfrScore (row : DiscretePeriodicCarrier) : Nat :=
  sopfr118 (atomicNumber row)

/-! ## Tabulated lookups (`Fin 118` aligned with IUPAC rows) -/

def relativeAtomicMassMicroUAt (row : DiscretePeriodicCarrier) : Nat :=
  PeriodicPauliEvCalibrationData.relativeAtomicMassMicroUList.get
    ⟨row.idx.val, by
      rw [PeriodicPauliEvCalibrationData.relative_atomic_mass_list_length]
      exact row.idx.isLt⟩

def firstIonizationMicroEvAt (row : DiscretePeriodicCarrier) : Nat :=
  PeriodicPauliEvCalibrationData.firstIonizationMicroEvList.get
    ⟨row.idx.val, by
      rw [PeriodicPauliEvCalibrationData.first_ionization_list_length]
      exact row.idx.isLt⟩

/-! ## Core mass morphism (micro-u over **10⁶**) -/

def codataMassCalibrationCore : PeriodicCalibrationMorphism where
  siMarker := { calibrationExpected := true }
  massRatioShadow := fun row =>
    ⟨relativeAtomicMassMicroUAt row, 1000000⟩

/-! ## Hydrogen-anchored Pauli → micro-eV and micro-u linear slopes -/

/-- Scale **`proxy`** by a reduced rational `(num / den)` — shared algebra for IE / mass bridges. -/
def scaledMicroEvFromPauliProxy (proxy num den : Nat) : Nat :=
  (proxy * num) / den

abbrev scaledMicroRelativeMassFromPauliProxy :=
  scaledMicroEvFromPauliProxy

/-! ### Synthetic ionization shadow (ledger narrative / missing-table filler)

Where the imported IE column is **0**, that marks **no continuum witness** in-file — not a
proof that the atom has zero ionization.

The map below is an explicit **non-CODATA** morphism ingredient: multiply the hydrogen-
anchored rational slope by **`12 · Z · ω'(Z)`**, where **`ω'(1) := 1`** and **`ω'(Z>1) := Ω(Z)`**
so hydrogen keeps the IE anchor identity while heavy rows get a discrete multiplicative
weight from prime-factor multiplicity.

**No theorem** identifies this column with measured ionization energies; it exists so the
ledger can thread a *single* deterministic replacement instead of silently reading **0**
as physical null.
-/

/-- Ω on **Z**, but pins **`Z = 1` → 1** so the hydrogen row keeps nontrivial synthetic IE. -/
def effectiveBraidOmegaWeight (row : DiscretePeriodicCarrier) : Nat :=
  let z := atomicNumber row
  let ω := braidPrimeOmegaScore row
  if z ≤ 1 then 1 else ω

/-- ω'-weighted hydrogen-slope IE shadow (micro-eV numerator scale as tabulated column). -/
def omegaWeightedSyntheticIonizationMicroEv (row : DiscretePeriodicCarrier) : Nat :=
  scaledMicroEvFromPauliProxy
    (pauliProxyTwelveZ row * effectiveBraidOmegaWeight row)
    PeriodicPauliEvCalibrationData.hydrogenAnchoredMicroEvPerPauliUnitNumerator
    PeriodicPauliEvCalibrationData.hydrogenAnchoredMicroEvPerPauliUnitDenominator

theorem hydrogen_omega_weighted_synthetic_ie_matches_tabulated_row :
    omegaWeightedSyntheticIonizationMicroEv ⟨0, by decide⟩ =
      firstIonizationMicroEvAt ⟨0, by decide⟩ := by
  native_decide

theorem hydrogen_anchor_scaled_ie_matches_table :
    scaledMicroEvFromPauliProxy
        (pauliProxyTwelveZ ⟨0, by decide⟩)
        PeriodicPauliEvCalibrationData.hydrogenAnchoredMicroEvPerPauliUnitNumerator
        PeriodicPauliEvCalibrationData.hydrogenAnchoredMicroEvPerPauliUnitDenominator
      =
      PeriodicPauliEvCalibrationData.firstIonizationMicroEvList.get
        ⟨0, by native_decide⟩ := by
  native_decide

theorem hydrogen_anchor_scaled_mass_matches_table :
    scaledMicroRelativeMassFromPauliProxy
        (pauliProxyTwelveZ ⟨0, by decide⟩)
        PeriodicPauliEvCalibrationData.hydrogenAnchoredMicroRelativeMassPerPauliUnitNumerator
        PeriodicPauliEvCalibrationData.hydrogenAnchoredMicroRelativeMassPerPauliUnitDenominator
      =
      PeriodicPauliEvCalibrationData.relativeAtomicMassMicroUList.get
        ⟨0, by native_decide⟩ := by
  native_decide

/-! ## Bundled Pauli / SI calibration morphism -/

structure PeriodicPauliEvCalibrationMorphism where
  /-- Relative atomic mass morphism (`u · 10⁻⁶` numerator shadows). -/
  coreMass : PeriodicCalibrationMorphism
  /-- Reduced rational scale **micro-eV / Pauli-proxy-unit** (hydrogen IE anchored). -/
  microEvPerPauliNumerator : Nat
  microEvPerPauliDenominator : Nat
  hEvDenPos : 0 < microEvPerPauliDenominator
  /-- Reduced rational scale **micro-u / Pauli-proxy-unit** (hydrogen mass anchored). -/
  microRelativeMassPerPauliNumerator : Nat
  microRelativeMassPerPauliDenominator : Nat
  hMassDenPos : 0 < microRelativeMassPerPauliDenominator
  /-- Tabulated first-ionization micro-eV column (source JSON; zeros when missing). -/
  ionizationMicroEv : DiscretePeriodicCarrier → Nat
  /-- Deterministic **non-tabulated** IE shadow (`Ω`/`ω'`-weighted hydrogen slope); not CODATA. -/
  syntheticIonizationMicroEv : DiscretePeriodicCarrier → Nat
  /-- Prime-factor-count shadow used as discrete “braiding density” handle. -/
  braidDensityScore : DiscretePeriodicCarrier → Nat

def codataPauliEvCalibrationWitness : PeriodicPauliEvCalibrationMorphism where
  coreMass := codataMassCalibrationCore
  microEvPerPauliNumerator :=
    PeriodicPauliEvCalibrationData.hydrogenAnchoredMicroEvPerPauliUnitNumerator
  microEvPerPauliDenominator :=
    PeriodicPauliEvCalibrationData.hydrogenAnchoredMicroEvPerPauliUnitDenominator
  hEvDenPos := PeriodicPauliEvCalibrationData.hydrogen_anchor_den_pos
  microRelativeMassPerPauliNumerator :=
    PeriodicPauliEvCalibrationData.hydrogenAnchoredMicroRelativeMassPerPauliUnitNumerator
  microRelativeMassPerPauliDenominator :=
    PeriodicPauliEvCalibrationData.hydrogenAnchoredMicroRelativeMassPerPauliUnitDenominator
  hMassDenPos := PeriodicPauliEvCalibrationData.hydrogen_anchor_mass_den_pos
  ionizationMicroEv := firstIonizationMicroEvAt
  syntheticIonizationMicroEv := omegaWeightedSyntheticIonizationMicroEv
  braidDensityScore := braidPrimeOmegaScore

theorem codata_core_mass_ratio_at_hydrogen :
    (codataMassCalibrationCore.massRatioShadow ⟨0, by decide⟩).num = 1008000 := by
  native_decide

theorem braid_density_for_z118 :
    braidPrimeOmegaScore ⟨117, by decide⟩ = 2 := by
  native_decide

end PeriodicPauliEvCalibration
end Gnosis
