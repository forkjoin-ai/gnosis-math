import Init
import Gnosis.PeriodicAtBridge
import Gnosis.AeonStandingWaveCoordinateBridge
import Gnosis.AeonCycleTwelveShadow
import Gnosis.AeonTwelveCarrierList

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
* A **lawful chart** **`finAmbientToTwelve` / `finTwelveToAmbient`** (mutual inverse maps, inverse lemmas)
  identifying **`Fin ambientDim`** with **`Fin twelve`** from `AeonCycleTwelveShadow`, so periodic phases share the
  **`iteratedCyclicSucc h12`** carrier.
* **`enumerationPhaseFinTwelve`**, transporting enumeration phase to **`Fin twelve`**, agrees with
  **`iteratedCyclicSucc h12 (row.idx.val)`** applied at the cycle origin (**closed timelike step**
  story in `DiscreteClosedTimelikeStep`).
* **Stride ticks** (**`AeonTwelveCarrierList`** convention): **`k`** ticks with stride **`s`** aggregate as
  **`iteratedCyclicSucc h12 (k * s)`**. Residue arithmetic **`Nat.mod_add_div`** makes **`phase ∘ (+ k·s)`**
  match **`(+ k·s) ∘ idx`** at **`% twelve`** (square lemma **`enumeration_phase_stride_square_val`**).
  Gcd **return time** at **`twelveCycleOrigin`** is packaged as **`stride_origin_return_at_twelve_cycle_origin`**.

See also: `Gnosis/docs/RusticChurchToContinuumChecklist.md`.

Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace PeriodicAeonPhaseBridge

open PeriodicAtBridge
open Gnosis.DiscreteClosedTimelikeStep
open Gnosis.AeonCycleTwelveShadow (finZero h12 twelve)

theorem ambient_dim_pos : 0 < AeonStandingWaveCoordinateBridge.ambientDim := by
  rw [AeonStandingWaveCoordinateBridge.ambientDim_eq_twelve]
  decide

/-- `ambientDim` matches `AeonCycleTwelveShadow.twelve` (**12**). -/
theorem ambient_dim_eq_shadow_twelve :
    AeonStandingWaveCoordinateBridge.ambientDim = AeonCycleTwelveShadow.twelve := by
  rw [AeonStandingWaveCoordinateBridge.ambientDim_eq_twelve]
  rfl

/-! ## Enumeration phase on **`Fin ambientDim`** -/

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

theorem enumeration_phase_val_mod_twelve (row : DiscretePeriodicCarrier) :
    (enumerationPhaseFinAmbient row).val =
      row.idx.val % AeonCycleTwelveShadow.twelve := by
  rw [enumeration_phase_val_eq, ambient_dim_eq_shadow_twelve]

/-! ## Lawful chart (**mutual inverse maps**) **`Fin ambientDim` ↔ `Fin twelve`**

`Init` alone does not expose a convenient **`Equiv`** namespace here; we package the same data as
explicit maps plus inverse lemmas (`fin_twelve_ambient_roundtrip`, `ambient_twelve_roundtrip`).
-/

/-- Canonical origin on the twelve-cycle carrier (`Gnosis.AeonCycleTwelveShadow`). -/
abbrev twelveCycleOrigin : Fin AeonCycleTwelveShadow.twelve :=
  ⟨0, AeonCycleTwelveShadow.twelve_pos⟩

/-- Project **`Fin ambientDim`** to **`Fin twelve`** (same underlying `.val`). -/
def finAmbientToTwelve (x : Fin AeonStandingWaveCoordinateBridge.ambientDim) : Fin AeonCycleTwelveShadow.twelve :=
  ⟨x.val, by rw [← ambient_dim_eq_shadow_twelve]; exact x.isLt⟩

/-- Embed **`Fin twelve`** into **`Fin ambientDim`** (same underlying `.val`). -/
def finTwelveToAmbient (x : Fin AeonCycleTwelveShadow.twelve) : Fin AeonStandingWaveCoordinateBridge.ambientDim :=
  ⟨x.val, by rw [ambient_dim_eq_shadow_twelve]; exact x.isLt⟩

theorem fin_twelve_ambient_roundtrip (x : Fin AeonStandingWaveCoordinateBridge.ambientDim) :
    finTwelveToAmbient (finAmbientToTwelve x) = x :=
  Fin.ext rfl

theorem ambient_twelve_roundtrip (x : Fin AeonCycleTwelveShadow.twelve) :
    finAmbientToTwelve (finTwelveToAmbient x) = x :=
  Fin.ext rfl

theorem fin_ambient_to_twelve_val (x : Fin AeonStandingWaveCoordinateBridge.ambientDim) :
    (finAmbientToTwelve x).val = x.val :=
  rfl

/-- Enumeration phase transported to **`Fin twelve`** (same `.val` as modulo **`twelve`**). -/
def enumerationPhaseFinTwelve (row : DiscretePeriodicCarrier) : Fin AeonCycleTwelveShadow.twelve :=
  finAmbientToTwelve (enumerationPhaseFinAmbient row)

theorem enumeration_phase_fin_twelve_val (row : DiscretePeriodicCarrier) :
    (enumerationPhaseFinTwelve row).val =
      row.idx.val % AeonCycleTwelveShadow.twelve := by
  simp [enumerationPhaseFinTwelve, fin_ambient_to_twelve_val, enumeration_phase_val_mod_twelve]

/-- Closed-loop dynamics from **`twelveCycleOrigin`** reaches **`enumerationPhaseFinTwelve`** in
**`row.idx.val`** ticks (**enumeration index**, not atomic **Z**). -/
theorem enumeration_phase_fin_twelve_eq_iterated_cyclic_succ_from_origin (row : DiscretePeriodicCarrier) :
    enumerationPhaseFinTwelve row =
      iteratedCyclicSucc AeonCycleTwelveShadow.h12 row.idx.val twelveCycleOrigin := by
  apply Fin.ext
  rw [enumeration_phase_fin_twelve_val,
    iteratedCyclicSucc_val AeonCycleTwelveShadow.h12 row.idx.val twelveCycleOrigin]
  dsimp [twelveCycleOrigin]
  rw [Nat.zero_add]

/-- Twelve ticks from **`twelveCycleOrigin`** close the discrete loop (`DiscreteClosedTimelikeStep`). -/
theorem iterate_twelve_from_origin_is_period :
    iteratedCyclicSucc AeonCycleTwelveShadow.h12 AeonCycleTwelveShadow.twelve twelveCycleOrigin =
      twelveCycleOrigin :=
  iteratedCyclicSucc_period AeonCycleTwelveShadow.h12 twelveCycleOrigin

/-! ## Stride exponent **`k * s`** (`AeonTwelveCarrierList` convention) vs **`% twelve`** residue -/

/-- Bridge carrier origin matches **`finZero`** (`AeonCycleTwelveShadow`). -/
theorem twelve_cycle_origin_eq_finZero : twelveCycleOrigin = finZero :=
  Fin.ext rfl

/-- **`stride_origin_return`** restated at **`twelveCycleOrigin`** (same vertex as **`finZero`**). -/
theorem stride_origin_return_at_twelve_cycle_origin (s : Nat) :
    iteratedCyclicSucc h12 ((twelve / Nat.gcd twelve s) * s) twelveCycleOrigin =
      twelveCycleOrigin := by
  rw [twelve_cycle_origin_eq_finZero]
  exact AeonTwelveCarrierList.stride_origin_return s

/-- **`(a + k·s) % 12`** depends on **`a`** only through **`a % 12`** (coefficient for **`twelve`** drops mod **`twelve`**). -/
theorem nat_mod_twelve_add_stride_pull_residue (a k s : Nat) :
    (a + k * s) % twelve = ((a % twelve) + k * s) % twelve := by
  have hel :
      a + k * s = (a % twelve + k * s) + twelve * (a / twelve) := by
    rw [congrArg (fun t => t + k * s) (Eq.symm (Nat.mod_add_div a twelve))]
    rw [Nat.add_assoc]
    rw [Nat.add_comm (twelve * (a / twelve)) (k * s)]
    rw [← Nat.add_assoc]
  rw [hel, Nat.mul_comm twelve (a / twelve), Nat.add_mul_mod_self_right]

theorem iterated_stride_val (x : Fin twelve) (k s : Nat) :
    (iteratedCyclicSucc h12 (k * s) x).val = (x.val + k * s) % twelve :=
  iteratedCyclicSucc_val h12 (k * s) x

/-- **`k`** stride ticks from **`twelveCycleOrigin`**: dot lands at **`(k·s) % 12`**. -/
theorem iterated_stride_from_twelve_cycle_origin_val (k s : Nat) :
    (iteratedCyclicSucc h12 (k * s) twelveCycleOrigin).val = (k * s) % twelve := by
  rw [iteratedCyclicSucc_val]
  dsimp [twelveCycleOrigin]
  rw [Nat.zero_add]

/-- Main square (**value-level**): advancing **`k`** stride ticks from **enumeration phase** matches
adding **`k·s`** to the raw **`idx.val`** before **`% twelve`**.

Not a functor on **`DiscretePeriodicCarrier`** (no induced row map)—only modular arithmetic alignment.
-/
theorem enumeration_phase_stride_square_val (row : DiscretePeriodicCarrier) (k s : Nat) :
    (iteratedCyclicSucc h12 (k * s) (enumerationPhaseFinTwelve row)).val =
      (row.idx.val + k * s) % twelve := by
  rw [iterated_stride_val, enumeration_phase_fin_twelve_val]
  exact (nat_mod_twelve_add_stride_pull_residue row.idx.val k s).symm

theorem hydrogen_enumeration_phase_fin_zero :
    enumerationPhaseFinAmbient { idx := ⟨0, by decide⟩ } =
      ⟨0, by decide⟩ := by
  rfl

/-- Row **`idx = 117`** (**Z = 118**): enumeration residue **`9`** on **`Fin ambientDim`**. -/
theorem row117_enumeration_phase_fin_eq_nine :
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
