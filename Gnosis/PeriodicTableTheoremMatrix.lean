import Init
import Gnosis.PeriodicAtBridge
import Gnosis.PeriodicBraidMatterJugular

/-!
# Periodic table ↔ theorem matrix (IUPAC Z = 1..118)

Maps every **known** chemical element (atomic number **Z** in **1..118**, Oganesson)
to the **same** structural-hole / complement-weight **theorem cluster** from the
Formal Theorem Ledger. Individual elements do not receive **distinct** Init-only
proofs unless you attach a concrete neighbor lattice (`StructuralHole`) per
substance—that data is **not** formalized here.

## Universal theorem block (every Z in 1..118)

Each row inherits the **non-empirical prediction** isomorphism:

* `THM-MENDELEEV-is-COMPLEMENT`
* `THM-NEI-MENDELEEV`
* `THM-NON-EMPIRICAL-SOLOMONOFF` (`SolomonoffSpace` / `SolomonoffInduction.non_empirical_solomonoff_compose`)
* `THM-NON-EMPIRICAL-PREDICTION-MASTER`
* `THM-LATTICE-PARTITION`
* `THM-INTERPOLATION-BOUNDED`
* `THM-HOLE-POSITIVE-WEIGHT`
* `THM-HOLES-ORDERED`
* `THM-IMPOSSIBLE-ELEMENT`
* `THM-PREDICTION-WITHOUT-OBSERVATION`

Ledger text lives in `open-source/gnosis/THEOREM_LEDGER.md`. Lean carries the
algebra: `Gnosis.NonEmpiricalPrediction` / `Gnosis.NovelInferenceForms` (e.g.
`mendeleev_is_complement`, `nei_mendeleev`), plus the Solomonoff-scale discrete
prior line `Gnosis.SolomonoffSpace` and the compose theorem surfaced again as
`SolomonoffInduction.non_empirical_solomonoff_compose`.

## Historical “predicted elements” (Mendeleev **eka** triple)

The three classic slots filled after **structural** interpolation (Mendeleev **before**
isolation): **Sc (Z=21)**, **Ga (Z=31)**, **Ge (Z=32)**.
These rows carry the same cluster as all others, **plus** the narrative flag
`mendeleevHistoricalHole := true`.

## Braid tower cardinality (structural witness)

The row count **118** coincides with `towerPhaseCount [2, 59]` — see
`iupac_row_count_eq_iupac_braid_phase_cardinality` and
`Gnosis.PeriodicBraidMatterJugular`. Any **`Fin k`** coarse bucket with **`k < 118`**
cannot injectively label every row (`mod_k_bucket_readout_not_injective`); the
dodecagon case is `k = 12` (`twelve_bucket_readout_not_injective`).

## Anti-theorem posture (all 118 rows)

There is **no** per-Z certified link from this matrix to **SI mass, Bohr radius,
or QCD** without a calibration bridge (`Gnosis.PeriodicAtBridge` discipline).
Typed SI-relative hooks: `PeriodicAtBridge.PeriodicCalibrationMorphism`.
Treat “measured mass from Bule score alone” as **refused**—not a contradiction inside
`Nat`, but an **anti-package** to empirical overclaim.

## Remaining unpredicted (extension **beyond 118**)

**Z > 118** targets live in `unpredictedHighZWitnesses` (**119 … 140** here): **no**
rows in `iupacZ118Symbols` until IUPAC assigns **permanent** names for synthesized
nuclides. **119–126** additionally carry **provisional systematic** symbols via
`provisionalSystematicSymbol` (placeholder nomenclature — **not** a discovery claim).

Braid-tower phase products for selected extension **Z** (`119`, `120`, `126`, `140`)
are packaged arithmetically in `Gnosis.PeriodicBraidMatterJugular` and echoed below.
-/

namespace Gnosis
namespace PeriodicTableTheoremMatrix

open Gnosis.BraidedTower (towerPhaseCount)

/-- IUPAC ordering along **Z** (1 = Hydrogen … 118 = Oganesson), one symbol per slot. -/
def iupacZ118Symbols : List String :=
  [
    "H", "He", "Li", "Be", "B", "C", "N", "O", "F", "Ne",
    "Na", "Mg", "Al", "Si", "P", "S", "Cl", "Ar", "K", "Ca",
    "Sc", "Ti", "V", "Cr", "Mn", "Fe", "Co", "Ni", "Cu", "Zn",
    "Ga", "Ge", "As", "Se", "Br", "Kr", "Rb", "Sr", "Y", "Zr",
    "Nb", "Mo", "Tc", "Ru", "Rh", "Pd", "Ag", "Cd", "In", "Sn",
    "Sb", "Te", "I", "Xe", "Cs", "Ba", "La", "Ce", "Pr", "Nd",
    "Pm", "Sm", "Eu", "Gd", "Tb", "Dy", "Ho", "Er", "Tm", "Yb",
    "Lu", "Hf", "Ta", "W", "Re", "Os", "Ir", "Pt", "Au", "Hg",
    "Tl", "Pb", "Bi", "Po", "At", "Rn", "Fr", "Ra", "Ac", "Th",
    "Pa", "U", "Np", "Pu", "Am", "Cm", "Bk", "Cf", "Es", "Fm",
    "Md", "No", "Lr", "Rf", "Db", "Sg", "Bh", "Hs", "Mt", "Ds",
    "Rg", "Cn", "Nh", "Fl", "Mc", "Lv", "Ts", "Og"
  ]

theorem iupacZ118Symbols_length : iupacZ118Symbols.length = 118 := by native_decide

/-- The 118 IUPAC rows match the **`[2, 59]` braided tower** phase cardinality
(`Gnosis.PeriodicBraidMatterJugular`). -/
theorem iupac_row_count_eq_iupac_braid_phase_cardinality :
    iupacZ118Symbols.length = PeriodicBraidMatterJugular.iupacBraidPhaseCardinality := by
  rw [iupacZ118Symbols_length, PeriodicBraidMatterJugular.iupac_braid_phase_cardinality_eq118]

def ledgerClusterEveryElement : List String :=
  [
    "THM-MENDELEEV-is-COMPLEMENT",
    "THM-NEI-MENDELEEV",
    "THM-NON-EMPIRICAL-SOLOMONOFF",
    "THM-NON-EMPIRICAL-PREDICTION-MASTER",
    "THM-LATTICE-PARTITION",
    "THM-INTERPOLATION-BOUNDED",
    "THM-HOLE-POSITIVE-WEIGHT",
    "THM-HOLES-ORDERED",
    "THM-IMPOSSIBLE-ELEMENT",
    "THM-PREDICTION-WITHOUT-OBSERVATION"
  ]

/-- Narrative anti-package: refusing SI mass / continuum radius without a bridge. -/
abbrev antiTheoremSiWithoutBridge : List String :=
  PeriodicAtBridge.refusalCalibrationStrings

/-- Ledger theorem IDs never coincide with periodic-bridge refusal tags. -/
theorem ledger_cluster_disjoint_refusal_calibration_strings (s : String)
    (h : s ∈ ledgerClusterEveryElement) :
    s ∉ PeriodicAtBridge.refusalCalibrationStrings := by
  simp [ledgerClusterEveryElement, PeriodicAtBridge.refusalCalibrationStrings, List.mem_cons] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Mendeleev **eka**-boron / eka-aluminum / eka-silicon slots (pre-isolation prediction). -/
def mendeleevEkaHistoricalZ : List Nat :=
  [21, 31, 32]

theorem mendeleevEkaHistoricalZ_bounded (z : Nat)
    (h : z ∈ mendeleevEkaHistoricalZ) :
    z ≤ 118 := by
  simp [mendeleevEkaHistoricalZ] at h
  rcases h with rfl | rfl | rfl <;> decide

def isMendeleevEkaHistoricalZ (z : Nat) : Bool :=
  z == 21 || z == 31 || z == 32

/-- Index **i : Fin 118** is 0-based; atomic number = `i.val + 1`. -/
def symbolAt (i : Fin 118) : String :=
  iupacZ118Symbols.get ⟨i.val, by rw [iupacZ118Symbols_length]; exact i.isLt⟩

def atomicNumberOf (i : Fin 118) : Nat :=
  i.val + 1

theorem atomicNumber_range (i : Fin 118) :
    1 ≤ atomicNumberOf i ∧ atomicNumberOf i ≤ 118 :=
  And.intro
    (by simp only [atomicNumberOf]; exact Nat.succ_le_succ (Nat.zero_le i.val))
    (by simp only [atomicNumberOf]; exact Nat.succ_le_of_lt i.isLt)

/-- Package **i** as the bridge-module discrete carrier (same `Fin 118` band). -/
def discreteCarrierAt (i : Fin 118) : PeriodicAtBridge.DiscretePeriodicCarrier :=
  ⟨i⟩

@[simp] theorem atomicNumber_agrees_with_bridge (i : Fin 118) :
    PeriodicAtBridge.atomicNumber (discreteCarrierAt i) = atomicNumberOf i :=
  rfl

/-- Contiguous research **Z** band **119 … 140** (inclusive). No ledger rows here:
names stay provisional / unsettled until IUPAC consensus on synthesized nuclides. -/
def unpredictedHighZWitnesses : List Nat :=
  (List.range 22).map fun i => 119 + i

theorem unpredictedHighZ_gt118 (z : Nat) (h : z ∈ unpredictedHighZWitnesses) : 118 < z := by
  simp [unpredictedHighZWitnesses, List.mem_map, List.mem_range] at h
  rcases h with ⟨i, hi, rfl⟩
  exact Nat.lt_of_lt_of_le (by decide : 118 < 119) (Nat.le_add_right 119 i)

theorem unpredictedHighZ_le140 (z : Nat) (h : z ∈ unpredictedHighZWitnesses) : z ≤ 140 := by
  simp [unpredictedHighZWitnesses, List.mem_map, List.mem_range] at h
  rcases h with ⟨i, hi, rfl⟩
  have hi21 : i ≤ 21 := Nat.lt_succ_iff.mp hi
  exact Nat.le_trans (Nat.add_le_add (Nat.le_refl 119) hi21) (by decide : 119 + 21 ≤ 140)

/-- **119–126:** provisional IUPAC systematic symbols only (pre-permanent-name placeholders). -/
def provisionalSystematicZs : List Nat :=
  [119, 120, 121, 122, 123, 124, 125, 126]

/-- Lookup systematic placeholder symbol when present (otherwise `none`). -/
def provisionalSystematicSymbol (z : Nat) : Option String :=
  match z with
  | 119 => some "Uue"
  | 120 => some "Ubn"
  | 121 => some "Ubu"
  | 122 => some "Ubb"
  | 123 => some "Ubt"
  | 124 => some "Ubq"
  | 125 => some "Ubp"
  | 126 => some "Ubh"
  | _ => none

theorem provisional_systematic_symbol_some_gt118 (z : Nat) (sym : String)
    (h : provisionalSystematicSymbol z = some sym) :
    118 < z := by
  unfold provisionalSystematicSymbol at h
  split at h
  · exact by decide
  · exact by decide
  · exact by decide
  · exact by decide
  · exact by decide
  · exact by decide
  · exact by decide
  · exact by decide
  · contradiction

theorem provisionalSystematicZs_subset_extension_band :
    ∀ z ∈ provisionalSystematicZs, z ∈ unpredictedHighZWitnesses := by native_decide

/-- Braid-tower phase-cardinality hits for extension milestones (arithmetic only). -/
theorem extension_band_towers_packaged :
    towerPhaseCount [7, 17] = 119
    ∧ towerPhaseCount [2, 2, 2, 3, 5] = 120
    ∧ towerPhaseCount [2, 7, 9] = 126
    ∧ towerPhaseCount [2, 2, 5, 7] = 140 :=
  ⟨PeriodicBraidMatterJugular.extension_band_z119_tower,
    PeriodicBraidMatterJugular.extension_band_z120_tower,
    PeriodicBraidMatterJugular.extension_band_z126_tower,
    PeriodicBraidMatterJugular.extension_band_z140_tower⟩

/-- Top of the extension band matches the **140** braided tower witness. -/
theorem extension_band_top_eq_braid_tower140 :
    unpredictedHighZWitnesses.getLast? = some 140
    ∧ towerPhaseCount [2, 2, 5, 7] = 140 :=
  And.intro (by native_decide) PeriodicBraidMatterJugular.extension_band_z140_tower

/-- Every row shares the same ledger cluster; dependence on **Z** is **not** in the certificate list. -/
theorem ledger_cluster_independent_of_index (_i : Fin 118) :
    ledgerClusterEveryElement = ledgerClusterEveryElement :=
  rfl

end PeriodicTableTheoremMatrix
end Gnosis
