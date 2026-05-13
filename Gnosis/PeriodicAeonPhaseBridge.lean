import Init
import Gnosis.PeriodicAtBridge
import Gnosis.AeonStandingWaveCoordinateBridge

/-!
# Periodic **118** carriers ↔ Aeon **12** column torus (explicit enumeration phase)

This module provides a **single deterministic morphism** from `DiscretePeriodicCarrier`
(IUPAC band indices **`Z − 1`**) to **`Fin ambientDim`** where **`ambientDim = Circadian.aeon`**
as pinned in `Gnosis.AeonStandingWaveCoordinateBridge`.

## What is **not** claimed

* **Not** the Mendeleev column / group placement: only **`idx.val % 12`** arithmetic on the
  enumeration order **`0 … 117`**.
* **Not** a spectroscopy or QCD statement: no gauge group, no continuum positions.
* **Not** identification with `omegaWeightedSyntheticIonizationMicroEv` or CODATA tables.

## What **is** claimed

* A phase map **`enumerationPhaseFinAmbient`** landing in the same finite torus type used by the
  standing-wave coordinate bridge (`Fin ambientDim`).
* Alignment lemmas tying **`% ambientDim`** to **`% Circadian.aeon`** via **`ambientDim_eq_circadian_aeon`**.

See also: `Gnosis/docs/RusticChurchToContinuumChecklist.md`.

Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace PeriodicAeonPhaseBridge

open PeriodicAtBridge

theorem ambient_dim_pos : 0 < AeonStandingWaveCoordinateBridge.ambientDim := by
  rw [AeonStandingWaveCoordinateBridge.ambientDim_eq_twelve]
  decide

/-- **`(Z−1) mod 12`** as a point on the **`Fin ambientDim`** column torus (enumeration-only). -/
def enumerationPhaseFinAmbient (row : DiscretePeriodicCarrier) : Fin AeonStandingWaveCoordinateBridge.ambientDim :=
  ⟨row.idx.val % AeonStandingWaveCoordinateBridge.ambientDim,
    Nat.mod_lt row.idx.val ambient_dim_pos⟩

theorem enumeration_phase_val_eq (row : DiscretePeriodicCarrier) :
    (enumerationPhaseFinAmbient row).val =
      row.idx.val % AeonStandingWaveCoordinateBridge.ambientDim :=
  rfl

theorem enumeration_phase_mod_circadian_aeon (row : DiscretePeriodicCarrier) :
    row.idx.val % AeonStandingWaveCoordinateBridge.ambientDim =
      row.idx.val % Circadian.aeon := by
  rw [← AeonStandingWaveCoordinateBridge.ambientDim_eq_circadian_aeon]

theorem hydrogen_enumeration_phase_fin_zero :
    enumerationPhaseFinAmbient { idx := ⟨0, by decide⟩ } =
      ⟨0, by decide⟩ := by
  rfl

theorem row117_enumeration_phase_fin_eq_one :
    enumerationPhaseFinAmbient { idx := ⟨117, by decide⟩ } =
      ⟨9, by decide⟩ := by
  rfl

/-- Bundle for morphisms that want **both** the discrete row and its aeon torus phase. -/
structure PeriodicRowEnumerationPhaseWitness where
  row : DiscretePeriodicCarrier
  /-- Phase on **`Fin ambientDim`** (`enumerationPhaseFinAmbient row`). -/
  phase : Fin AeonStandingWaveCoordinateBridge.ambientDim

def periodicEnumerationPhaseWitness (row : DiscretePeriodicCarrier) : PeriodicRowEnumerationPhaseWitness where
  row := row
  phase := enumerationPhaseFinAmbient row

theorem periodic_enumeration_phase_witness_phase_eq (row : DiscretePeriodicCarrier) :
    (periodicEnumerationPhaseWitness row).phase = enumerationPhaseFinAmbient row :=
  rfl

end PeriodicAeonPhaseBridge
end Gnosis
