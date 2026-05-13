import Init
import Gnosis.PeriodicAtBridge
import Gnosis.PeriodicPauliEvCalibration

/-!
# Calibration stress tests: where the shadow sharpens or diverges

This module **does not** upgrade discrete braid bookkeeping into quantum chemistry.

It packages three honest tensions:

1. **Missing IE slots** — JSON zeros become explicit **synthetic** micro-eV via
   `omegaWeightedSyntheticIonizationMicroEv`. That map is **deterministic ledger glue**, not
   a measurement claim (see docstring on `PeriodicPauliEvCalibration.omegaWeightedSyntheticIonizationMicroEv`).
2. **Richer braid shadows** — beyond **Ω**, `braidSopfrScore` tracks sum-of-prime-factors mass.
   There is **no** imported Pauling electronegativity column here; any correlation claim needs
   external data + statistics — out of scope for Init-only proofs.
3. **Mass vs linear Pauli slope** — `massDebtSignedMicroU` is **relative atomic mass minus**
   the hydrogen-mass-anchored **`12·Z`** slope in micro-u. Positive values mean “excess above
   that linear bridge”; interpreting that excess as nuclear binding / “vented fold energy” is
   **narrative physics**, not proved here (no liquid-drop theorem).

“Island of stability” ionization brackets for transfermium rows require **hypothesis-level**
continuum inputs; this file refuses to invent numeric Og IE bands.

Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace PeriodicPauliEvCalibrationShadows

open PeriodicAtBridge (DiscretePeriodicCarrier)
open PeriodicPauliEvCalibration

/-- Carrier index for **Z = 118** (Oganesson). -/
abbrev og118Row : DiscretePeriodicCarrier :=
  { idx := ⟨117, by decide⟩ }

abbrev neonRow : DiscretePeriodicCarrier :=
  { idx := ⟨9, by decide⟩ }

abbrev argonRow : DiscretePeriodicCarrier :=
  { idx := ⟨17, by decide⟩ }

/-- Tabulated hydrogen first ionization (micro-eV column). -/
def hydrogenTabulatedFirstIonizationMicroEv : Nat :=
  PeriodicPauliEvCalibrationData.firstIonizationMicroEvList.get ⟨0, by native_decide⟩

theorem hydrogen_tabulated_first_ionization_pos : 0 < hydrogenTabulatedFirstIonizationMicroEv := by
  native_decide

/-! ## Og118: missing tabulated IE vs nonzero synthetic column -/

theorem og118_tabulated_first_ionization_is_missing_slot :
    firstIonizationMicroEvAt og118Row = 0 := by
  native_decide

theorem og118_synthetic_ionization_strictly_positive :
    0 < omegaWeightedSyntheticIonizationMicroEv og118Row := by
  native_decide

theorem og118_effective_braid_weight_eq_prime_omega :
    effectiveBraidOmegaWeight og118Row = braidPrimeOmegaScore og118Row := by
  native_decide

theorem og118_braid_prime_omega_eq_two :
    braidPrimeOmegaScore og118Row = 2 := by
  native_decide

theorem og118_braid_sopfr_eq_sum_of_tower_primes :
    braidSopfrScore og118Row = 61 := by
  native_decide

/-- Synthetic Og prediction is exactly **`Ω(118)` times** the naive hydrogen-slope IE at the same **Z**. -/
theorem og118_synthetic_is_prime_omega_multiple_of_linear_ie_slope :
    omegaWeightedSyntheticIonizationMicroEv og118Row =
      braidPrimeOmegaScore og118Row *
        scaledMicroEvFromPauliProxy (pauliProxyTwelveZ og118Row)
          PeriodicPauliEvCalibrationData.hydrogenAnchoredMicroEvPerPauliUnitNumerator
          PeriodicPauliEvCalibrationData.hydrogenAnchoredMicroEvPerPauliUnitDenominator := by
  native_decide

/-! ### Harmonic coincidence at Og118 (algebra of anchors — not a spectroscopy theorem)

Because **`ω'(118) = 2`** and **`IE(H) = 2 · (6798961)`** after clearing denominators, the
ω'-weighted synthetic micro-eV lands on an **exact integer multiple** of the **tabulated**
hydrogen IE — a numerological closure of the rational anchor, **not** evidence about Og.
-/

theorem og118_synthetic_eq_236_mul_hydrogen_tabulated_ie :
    omegaWeightedSyntheticIonizationMicroEv og118Row =
      236 * hydrogenTabulatedFirstIonizationMicroEv := by
  native_decide

theorem og118_harmonic_multiplier_unique {k : Nat}
    (hk :
      omegaWeightedSyntheticIonizationMicroEv og118Row =
        k * hydrogenTabulatedFirstIonizationMicroEv) :
    k = 236 := by
  have hsynth236 :
      omegaWeightedSyntheticIonizationMicroEv og118Row =
        236 * hydrogenTabulatedFirstIonizationMicroEv := by
    native_decide
  have hk2 :
      k * hydrogenTabulatedFirstIonizationMicroEv =
        236 * hydrogenTabulatedFirstIonizationMicroEv :=
    hk.symm.trans hsynth236
  exact Nat.eq_of_mul_eq_mul_right hydrogen_tabulated_first_ionization_pos hk2

/-! ## Noble-gas counterexamples to exact hydrogen-IE harmonics (tabulated column)

Indices **Z − 1**: Ne **Z = 10 → 9**, Ar **Z = 18 → 17**.
-/

theorem neon_tabulated_ie_not_integer_multiple_of_hydrogen_tabulated_ie :
    ∀ k : Nat,
      firstIonizationMicroEvAt neonRow ≠ k * hydrogenTabulatedFirstIonizationMicroEv := by
  intro k
  by_cases hk4 : 4 ≤ k
  · intro he
    have hstrict :
        firstIonizationMicroEvAt neonRow < 4 * hydrogenTabulatedFirstIonizationMicroEv := by
      native_decide
    have hmul :
        4 * hydrogenTabulatedFirstIonizationMicroEv ≤ k * hydrogenTabulatedFirstIonizationMicroEv := by
      exact Nat.mul_le_mul_right hydrogenTabulatedFirstIonizationMicroEv hk4
    rw [← he] at hmul
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hstrict hmul)
  · have hklt : k < 4 := Nat.lt_of_not_ge hk4
    match k with
    | 0 =>
      intro h
      exact absurd (by simpa [Nat.zero_mul] using h) (by native_decide : firstIonizationMicroEvAt neonRow ≠ 0)
    | 1 =>
      intro h
      exact absurd (by simpa [Nat.one_mul] using h) (by native_decide)
    | 2 =>
      intro h
      exact absurd (by simpa using h) (by native_decide)
    | 3 =>
      intro h
      exact absurd (by simpa using h) (by native_decide)
    | n + 4 =>
      exact absurd hklt (Nat.not_lt_of_le (Nat.le_add_left 4 n))

theorem argon_tabulated_ie_not_integer_multiple_of_hydrogen_tabulated_ie :
    ∀ k : Nat,
      firstIonizationMicroEvAt argonRow ≠ k * hydrogenTabulatedFirstIonizationMicroEv := by
  intro k
  by_cases hk12 : 12 ≤ k
  · intro he
    have hstrict :
        firstIonizationMicroEvAt argonRow < 12 * hydrogenTabulatedFirstIonizationMicroEv := by
      native_decide
    have hmul :
        12 * hydrogenTabulatedFirstIonizationMicroEv ≤ k * hydrogenTabulatedFirstIonizationMicroEv := by
      exact Nat.mul_le_mul_right hydrogenTabulatedFirstIonizationMicroEv hk12
    rw [← he] at hmul
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hstrict hmul)
  · have hklt : k < 12 := Nat.lt_of_not_ge hk12
    match k with
    | 0 =>
      intro h
      exact absurd (by simpa [Nat.zero_mul] using h) (by native_decide : firstIonizationMicroEvAt argonRow ≠ 0)
    | 1 =>
      intro h
      exact absurd (by simpa [Nat.one_mul] using h) (by native_decide)
    | 2 =>
      intro h
      exact absurd (by simpa using h) (by native_decide)
    | 3 =>
      intro h
      exact absurd (by simpa using h) (by native_decide)
    | 4 =>
      intro h
      exact absurd (by simpa using h) (by native_decide)
    | 5 =>
      intro h
      exact absurd (by simpa using h) (by native_decide)
    | 6 =>
      intro h
      exact absurd (by simpa using h) (by native_decide)
    | 7 =>
      intro h
      exact absurd (by simpa using h) (by native_decide)
    | 8 =>
      intro h
      exact absurd (by simpa using h) (by native_decide)
    | 9 =>
      intro h
      exact absurd (by simpa using h) (by native_decide)
    | 10 =>
      intro h
      exact absurd (by simpa using h) (by native_decide)
    | 11 =>
      intro h
      exact absurd (by simpa using h) (by native_decide)
    | n + 12 =>
      exact absurd hklt (Nat.not_lt_of_le (Nat.le_add_left 12 n))

/-! ## Extension-band braid shadows (**Z** beyond the IUPAC `Fin 118` carrier)

These are **bare arithmetic** on **Z**, not rows in `DiscretePeriodicCarrier`.
-/

theorem prime_factor_count_Z120_matches_user_factor_account :
    primeOmegaFuel 120 24 = 5 := by
  native_decide

theorem sopfr_Z120_matches_user_factor_account :
    sopfrFuel 120 24 = 14 := by
  native_decide

/-! ## Signed “mass debt” vs hydrogen-mass-anchored **`12·Z`** slope

Interpretation beyond **`Int`** subtraction stays outside Init-only physics.
-/

def linearPauliMassScaledMicroU (row : DiscretePeriodicCarrier) : Nat :=
  scaledMicroRelativeMassFromPauliProxy (pauliProxyTwelveZ row)
    PeriodicPauliEvCalibrationData.hydrogenAnchoredMicroRelativeMassPerPauliUnitNumerator
    PeriodicPauliEvCalibrationData.hydrogenAnchoredMicroRelativeMassPerPauliUnitDenominator

/-- Signed gap **`mass_table − linear_mass_slope`** at micro-u resolution. -/
def massDebtSignedMicroU (row : DiscretePeriodicCarrier) : Int :=
  (relativeAtomicMassMicroUAt row : Int) - (linearPauliMassScaledMicroU row : Int)

theorem hydrogen_mass_debt_signed_zero :
    massDebtSignedMicroU { idx := ⟨0, by decide⟩ } = 0 := by
  native_decide

theorem helium_mass_debt_signed_positive :
    0 < massDebtSignedMicroU { idx := ⟨1, by decide⟩ } := by
  native_decide

theorem og118_mass_debt_signed_positive :
    0 < massDebtSignedMicroU og118Row := by
  native_decide

/-! ## Hypothesis bracket hook (no numeric Og band asserted)

Downstream bridges may bundle literature intervals as explicit assumptions without pretending
they are braid consequences.
-/

structure LiteratureFirstIonizationMicroEvBand where
  /-- Lower micro-eV endpoint (inclusive). -/
  lo : Nat
  /-- Upper micro-eV endpoint (inclusive). -/
  hi : Nat
  /-- Sanity: ordered endpoints. -/
  ordered : lo ≤ hi

def syntheticOg118MicroEv : Nat :=
  omegaWeightedSyntheticIonizationMicroEv og118Row

theorem synthetic_og118_microev_positive : 0 < syntheticOg118MicroEv :=
  og118_synthetic_ionization_strictly_positive

end PeriodicPauliEvCalibrationShadows
end Gnosis
