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
* **Not** identification of **`enumerationPhaseFinAmbient`** with any particular Plücker chart face; **`AeonStandingWaveCoordinateBridge`** packages multiple certified **`coordinatePlane`** lifts (**`aeonCoordinatePlane`** / **`aeonAuxiliaryCoordinatePlane`**) without changing the **`idx.val % ambientDim`** torus map defined here.

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
* **Chart factorization:** **`enumerationPhaseFinAmbient`** refactors as **`finTwelveToAmbient (enumerationPhaseFinTwelve row)`**
  (**`enumeration_phase_fin_ambient_eq_fin_twelve_to_ambient`**); stride residues match **`fin_twelve_to_ambient_after_stride`**.
* **Discrete closure:** **`iterated_cyclic_succ_period_ambient`** / **`iterate_ambient_from_origin_is_period`** on **`Fin ambientDim`**, matching **`iterate_twelve_from_origin_is_period`** on **`Fin twelve`**. Bridge chains: **`iterate_twelve_from_origin_is_period_via_ambient`** (**`fin_ambient_to_twelve_iterate_cyclic_succ`**), **`iterate_ambient_from_origin_via_twelve_period`** (**`fin_twelve_to_ambient_iterate_cyclic_succ`**). Single-step chart: **`DiscreteClosedTimelikeStep.iteratedCyclicSucc_one_eq_cyclicSucc`**, **`fin_ambient_to_twelve_cyclic_succ`**, **`fin_twelve_to_ambient_cyclic_succ`**.
* **Stride ticks** (**`AeonTwelveCarrierList`** convention): **`k`** ticks with stride **`s`** aggregate as
  **`iteratedCyclicSucc h12 (k * s)`**. Residue arithmetic **`Nat.mod_add_div`** makes **`phase ∘ (+ k·s)`**
  match **`(+ k·s) ∘ idx`** at **`% twelve`**: same modulus story on **`Fin ambientDim`** via **`enumeration_phase_stride_square_ambient`**
  (**`iteratedCyclicSucc ambient_dim_pos`**), bridge lemmas **`fin_ambient_to_twelve_iterate_cyclic_succ`** /
  **`enumeration_phase_fin_twelve_iterate_via_ambient_carrier`**, and **`Fin twelve`** packaging **`enumeration_phase_stride_square`** /
  **`enumerationPhaseFinTwelveAfterStride`** / **`enumerationPhaseFinAmbientAfterStride`**, chart lemmas **`fin_ambient_to_twelve_after_stride`** /
  **`fin_twelve_to_ambient_after_stride`**, chart-applied formulation **`enumeration_phase_stride_square_via_ambient_chart`**, value projection **`enumeration_phase_stride_square_val`**).
  Gcd **return time** at **`twelveCycleOrigin`** is packaged as **`stride_origin_return_at_twelve_cycle_origin`**.

See also: `Gnosis/docs/RusticChurchToContinuumChecklist.md`.

Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace PeriodicAeonPhaseBridge

open PeriodicAtBridge
open Gnosis.DiscreteClosedTimelikeStep
open Gnosis.AeonCycleTwelveShadow (finZero h12 twelve twelve_pos)

theorem ambient_dim_pos : 0 < AeonStandingWaveCoordinateBridge.ambientDim := by
  rw [AeonStandingWaveCoordinateBridge.ambientDim_eq_twelve]
  decide

/-- `ambientDim` matches `AeonCycleTwelveShadow.twelve` (**12**). -/
theorem ambient_dim_eq_shadow_twelve :
    AeonStandingWaveCoordinateBridge.ambientDim = AeonCycleTwelveShadow.twelve := by
  rw [AeonStandingWaveCoordinateBridge.ambientDim_eq_twelve]
  rfl

/-- **`(a + k·s) % n`** depends on **`a`** only through **`a % n`** (`Nat.mod_add_div` peel). -/
theorem nat_mod_n_add_stride_pull_residue {n : Nat} (_hn : 0 < n) (a k s : Nat) :
    (a + k * s) % n = ((a % n) + k * s) % n := by
  have hel : a + k * s = (a % n + k * s) + n * (a / n) := by
    rw [congrArg (fun t => t + k * s) (Eq.symm (Nat.mod_add_div a n))]
    rw [Nat.add_assoc]
    rw [Nat.add_comm (n * (a / n)) (k * s)]
    rw [← Nat.add_assoc]
  rw [hel, Nat.mul_comm n (a / n), Nat.add_mul_mod_self_right]

/-- **`(a + k·s) % 12`** depends on **`a`** only through **`a % 12`**. -/
theorem nat_mod_twelve_add_stride_pull_residue (a k s : Nat) :
    (a + k * s) % twelve = ((a % twelve) + k * s) % twelve :=
  nat_mod_n_add_stride_pull_residue twelve_pos a k s

theorem nat_mod_ambient_add_stride_pull_residue (a k s : Nat) :
    (a + k * s) % AeonStandingWaveCoordinateBridge.ambientDim =
      ((a % AeonStandingWaveCoordinateBridge.ambientDim) + k * s) %
        AeonStandingWaveCoordinateBridge.ambientDim :=
  nat_mod_n_add_stride_pull_residue ambient_dim_pos a k s

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

/-- Enumeration residue after **`k`** stride ticks with stride **`s`**, on **`Fin ambientDim`** (same **`%`** convention as **`enumerationPhaseFinAmbient`**). -/
def enumerationPhaseFinAmbientAfterStride (row : DiscretePeriodicCarrier) (k s : Nat) :
    Fin AeonStandingWaveCoordinateBridge.ambientDim :=
  ⟨(row.idx.val + k * s) % AeonStandingWaveCoordinateBridge.ambientDim,
    Nat.mod_lt _ ambient_dim_pos⟩

theorem enumeration_phase_fin_ambient_after_stride_val (row : DiscretePeriodicCarrier) (k s : Nat) :
    (enumerationPhaseFinAmbientAfterStride row k s).val =
      (row.idx.val + k * s) % AeonStandingWaveCoordinateBridge.ambientDim :=
  rfl

theorem enumeration_phase_fin_ambient_after_stride_val_mod_twelve (row : DiscretePeriodicCarrier)
    (k s : Nat) :
    (enumerationPhaseFinAmbientAfterStride row k s).val =
      (row.idx.val + k * s) % twelve := by
  rw [enumeration_phase_fin_ambient_after_stride_val, ambient_dim_eq_shadow_twelve]

/-- Stride square purely on **`Fin ambientDim`** (`DiscreteClosedTimelikeStep` at **`ambient_dim_pos`**). -/
theorem enumeration_phase_stride_square_ambient (row : DiscretePeriodicCarrier) (k s : Nat) :
    iteratedCyclicSucc ambient_dim_pos (k * s) (enumerationPhaseFinAmbient row) =
      enumerationPhaseFinAmbientAfterStride row k s :=
  Fin.ext (by
    rw [iteratedCyclicSucc_val ambient_dim_pos (k * s) (enumerationPhaseFinAmbient row),
      enumeration_phase_val_eq, enumeration_phase_fin_ambient_after_stride_val]
    exact (nat_mod_ambient_add_stride_pull_residue row.idx.val k s).symm)

/-! ## Lawful chart (**mutual inverse maps**) **`Fin ambientDim` ↔ `Fin twelve`**

`Init` alone does not expose a convenient **`Equiv`** namespace here; we package the same data as
explicit maps plus inverse lemmas (`fin_twelve_ambient_roundtrip`, `ambient_twelve_roundtrip`).
-/

/-- Canonical origin on the twelve-cycle carrier (`Gnosis.AeonCycleTwelveShadow`). -/
abbrev twelveCycleOrigin : Fin AeonCycleTwelveShadow.twelve :=
  ⟨0, AeonCycleTwelveShadow.twelve_pos⟩

/-- Canonical origin on **`Fin ambientDim`** (**`0`**, same numeric label as **`twelveCycleOrigin`**). -/
abbrev ambientCycleOrigin : Fin AeonStandingWaveCoordinateBridge.ambientDim :=
  ⟨0, ambient_dim_pos⟩

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

/-- **`iteratedCyclicSucc`** agrees across the chart: same underlying modulus (**`ambientDim = twelve`**). -/
theorem fin_ambient_to_twelve_iterate_cyclic_succ (k : Nat)
    (x : Fin AeonStandingWaveCoordinateBridge.ambientDim) :
    finAmbientToTwelve (iteratedCyclicSucc ambient_dim_pos k x) =
      iteratedCyclicSucc h12 k (finAmbientToTwelve x) := by
  apply Fin.ext
  simp only [fin_ambient_to_twelve_val, iteratedCyclicSucc_val]
  exact congrArg (fun m => (x.val + k) % m) ambient_dim_eq_shadow_twelve

/-- **`cyclicSucc`** agrees across **`finAmbientToTwelve`** (**`k = 1`** slice of **`fin_ambient_to_twelve_iterate_cyclic_succ`**). -/
theorem fin_ambient_to_twelve_cyclic_succ (x : Fin AeonStandingWaveCoordinateBridge.ambientDim) :
    finAmbientToTwelve (cyclicSucc ambient_dim_pos x) = cyclicSucc h12 (finAmbientToTwelve x) := by
  simpa [iteratedCyclicSucc_one_eq_cyclicSucc] using fin_ambient_to_twelve_iterate_cyclic_succ 1 x

/-- Chart sends **`ambientCycleOrigin`** to **`twelveCycleOrigin`**. -/
theorem fin_ambient_to_twelve_ambient_cycle_origin :
    finAmbientToTwelve ambientCycleOrigin = twelveCycleOrigin :=
  Fin.ext rfl

/-- Inverse chart: **`twelveCycleOrigin`** lands on **`ambientCycleOrigin`**. -/
theorem fin_twelve_to_ambient_twelve_cycle_origin :
    finTwelveToAmbient twelveCycleOrigin = ambientCycleOrigin :=
  Fin.ext rfl

/-- Inverse iterate lemma (**`fin_twelve_ambient_roundtrip`** after **`fin_ambient_to_twelve_iterate_cyclic_succ`**). -/
theorem fin_twelve_to_ambient_iterate_cyclic_succ (k : Nat) (z : Fin twelve) :
    finTwelveToAmbient (iteratedCyclicSucc h12 k z) =
      iteratedCyclicSucc ambient_dim_pos k (finTwelveToAmbient z) := by
  calc finTwelveToAmbient (iteratedCyclicSucc h12 k z)
      _ = finTwelveToAmbient (finAmbientToTwelve (iteratedCyclicSucc ambient_dim_pos k (finTwelveToAmbient z))) :=
            congrArg finTwelveToAmbient (fin_ambient_to_twelve_iterate_cyclic_succ k (finTwelveToAmbient z)).symm
      _ = iteratedCyclicSucc ambient_dim_pos k (finTwelveToAmbient z) :=
            fin_twelve_ambient_roundtrip _

/-- Inverse **`cyclicSucc`** chart (**`k = 1`** slice of **`fin_twelve_to_ambient_iterate_cyclic_succ`**). -/
theorem fin_twelve_to_ambient_cyclic_succ (z : Fin twelve) :
    finTwelveToAmbient (cyclicSucc h12 z) = cyclicSucc ambient_dim_pos (finTwelveToAmbient z) := by
  simpa [iteratedCyclicSucc_one_eq_cyclicSucc] using fin_twelve_to_ambient_iterate_cyclic_succ 1 z

/-- Enumeration phase transported to **`Fin twelve`** (same `.val` as modulo **`twelve`**). -/
def enumerationPhaseFinTwelve (row : DiscretePeriodicCarrier) : Fin AeonCycleTwelveShadow.twelve :=
  finAmbientToTwelve (enumerationPhaseFinAmbient row)

theorem enumeration_phase_fin_twelve_val (row : DiscretePeriodicCarrier) :
    (enumerationPhaseFinTwelve row).val =
      row.idx.val % AeonCycleTwelveShadow.twelve := by
  simp [enumerationPhaseFinTwelve, fin_ambient_to_twelve_val, enumeration_phase_val_mod_twelve]

/-- **`enumerationPhaseFinAmbient`** is **`finTwelveToAmbient`** applied to the **`Fin twelve`** phase
(**inverse chart** after projecting with **`finAmbientToTwelve`**). Same modulus story as
**`ambient_dim_eq_shadow_twelve`**; does not introduce a second Grassmannian chart beyond the existing
**`Fin ambientDim ↔ Fin twelve`** identification. -/
theorem enumeration_phase_fin_ambient_eq_fin_twelve_to_ambient (row : DiscretePeriodicCarrier) :
    enumerationPhaseFinAmbient row =
      finTwelveToAmbient (enumerationPhaseFinTwelve row) := by
  simpa [enumerationPhaseFinTwelve] using
    (fin_twelve_ambient_roundtrip (enumerationPhaseFinAmbient row)).symm

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

/-- **`ambientDim`** full turns revisit every **`Fin ambientDim`** event (`DiscreteClosedTimelikeStep`). -/
theorem iterated_cyclic_succ_period_ambient (x : Fin AeonStandingWaveCoordinateBridge.ambientDim) :
    iteratedCyclicSucc ambient_dim_pos AeonStandingWaveCoordinateBridge.ambientDim x = x :=
  iteratedCyclicSucc_period ambient_dim_pos x

/-- Closed loop at **`ambientCycleOrigin`** (ambient carrier). -/
theorem iterate_ambient_from_origin_is_period :
    iteratedCyclicSucc ambient_dim_pos AeonStandingWaveCoordinateBridge.ambientDim ambientCycleOrigin =
      ambientCycleOrigin :=
  iteratedCyclicSucc_period ambient_dim_pos ambientCycleOrigin

/-- Same statement as **`iterate_twelve_from_origin_is_period`**, recovered from ambient period + chart iterate lemma. -/
theorem iterate_twelve_from_origin_is_period_via_ambient :
    iteratedCyclicSucc h12 twelve twelveCycleOrigin = twelveCycleOrigin := by
  have h :=
    (fin_ambient_to_twelve_iterate_cyclic_succ AeonStandingWaveCoordinateBridge.ambientDim
        ambientCycleOrigin).symm
  rw [iterate_ambient_from_origin_is_period] at h
  simpa [fin_ambient_to_twelve_ambient_cycle_origin, ambient_dim_eq_shadow_twelve] using h

/-- Same statement as **`iterate_ambient_from_origin_is_period`**, recovered from **`Fin twelve`** closure + inverse iterate lemma. -/
theorem iterate_ambient_from_origin_via_twelve_period :
    iteratedCyclicSucc ambient_dim_pos AeonStandingWaveCoordinateBridge.ambientDim ambientCycleOrigin =
      ambientCycleOrigin := by
  calc iteratedCyclicSucc ambient_dim_pos AeonStandingWaveCoordinateBridge.ambientDim ambientCycleOrigin
      _ = iteratedCyclicSucc ambient_dim_pos AeonStandingWaveCoordinateBridge.ambientDim (finTwelveToAmbient twelveCycleOrigin) :=
            congrArg (iteratedCyclicSucc ambient_dim_pos AeonStandingWaveCoordinateBridge.ambientDim)
              fin_twelve_to_ambient_twelve_cycle_origin.symm
      _ = finTwelveToAmbient (iteratedCyclicSucc h12 AeonStandingWaveCoordinateBridge.ambientDim twelveCycleOrigin) :=
            (fin_twelve_to_ambient_iterate_cyclic_succ AeonStandingWaveCoordinateBridge.ambientDim twelveCycleOrigin).symm
      _ = finTwelveToAmbient (iteratedCyclicSucc h12 twelve twelveCycleOrigin) :=
            congrArg finTwelveToAmbient (congrArg (fun kk => iteratedCyclicSucc h12 kk twelveCycleOrigin)
              ambient_dim_eq_shadow_twelve)
      _ = finTwelveToAmbient twelveCycleOrigin := by rw [iterate_twelve_from_origin_is_period]
      _ = ambientCycleOrigin :=
            fin_twelve_to_ambient_twelve_cycle_origin

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

theorem iterated_stride_val (x : Fin twelve) (k s : Nat) :
    (iteratedCyclicSucc h12 (k * s) x).val = (x.val + k * s) % twelve :=
  iteratedCyclicSucc_val h12 (k * s) x

/-- **`k`** stride ticks from **`twelveCycleOrigin`**: dot lands at **`(k·s) % 12`**. -/
theorem iterated_stride_from_twelve_cycle_origin_val (k s : Nat) :
    (iteratedCyclicSucc h12 (k * s) twelveCycleOrigin).val = (k * s) % twelve := by
  rw [iteratedCyclicSucc_val]
  dsimp [twelveCycleOrigin]
  rw [Nat.zero_add]

/-- Residue **`(row.idx.val + k·s) % 12`** as canonical **`Fin twelve`** (enumeration stride target). -/
def enumerationPhaseFinTwelveAfterStride (row : DiscretePeriodicCarrier) (k s : Nat) : Fin twelve :=
  ⟨(row.idx.val + k * s) % twelve, Nat.mod_lt _ twelve_pos⟩

/-- Value projection of **`enumeration_phase_stride_square`**. -/
theorem enumeration_phase_stride_square_val (row : DiscretePeriodicCarrier) (k s : Nat) :
    (iteratedCyclicSucc h12 (k * s) (enumerationPhaseFinTwelve row)).val =
      (row.idx.val + k * s) % twelve := by
  rw [iterated_stride_val, enumeration_phase_fin_twelve_val]
  exact (nat_mod_twelve_add_stride_pull_residue row.idx.val k s).symm

/-- Main square (**`Fin twelve`**): **`k`** stride ticks from **enumeration phase** land on the
canonical residue point **`enumerationPhaseFinTwelveAfterStride`**.

Not a functor on **`DiscretePeriodicCarrier`** (no induced row map)—only modular arithmetic alignment.
-/
theorem enumeration_phase_stride_square (row : DiscretePeriodicCarrier) (k s : Nat) :
    iteratedCyclicSucc h12 (k * s) (enumerationPhaseFinTwelve row) =
      enumerationPhaseFinTwelveAfterStride row k s :=
  Fin.ext (enumeration_phase_stride_square_val row k s)

/-- Carry **`iteratedCyclicSucc h12`** through **`finAmbientToTwelve`** from **`Fin ambientDim`**. -/
theorem enumeration_phase_fin_twelve_iterate_via_ambient_carrier (row : DiscretePeriodicCarrier)
    (k s : Nat) :
    iteratedCyclicSucc h12 (k * s) (enumerationPhaseFinTwelve row) =
      finAmbientToTwelve (iteratedCyclicSucc ambient_dim_pos (k * s) (enumerationPhaseFinAmbient row)) :=
  (fin_ambient_to_twelve_iterate_cyclic_succ (k * s) (enumerationPhaseFinAmbient row)).symm

/-- Chart identifies **`enumerationPhaseFinAmbientAfterStride`** with **`enumerationPhaseFinTwelveAfterStride`**. -/
theorem fin_ambient_to_twelve_after_stride (row : DiscretePeriodicCarrier) (k s : Nat) :
    finAmbientToTwelve (enumerationPhaseFinAmbientAfterStride row k s) =
      enumerationPhaseFinTwelveAfterStride row k s :=
  Fin.ext (by
    simp [fin_ambient_to_twelve_val, enumeration_phase_fin_ambient_after_stride_val_mod_twelve,
      enumerationPhaseFinTwelveAfterStride])

/-- Inverse chart (**`Fin twelve` → `Fin ambientDim`**) for stride residues. -/
theorem fin_twelve_to_ambient_after_stride (row : DiscretePeriodicCarrier) (k s : Nat) :
    finTwelveToAmbient (enumerationPhaseFinTwelveAfterStride row k s) =
      enumerationPhaseFinAmbientAfterStride row k s := by
  rw [← fin_ambient_to_twelve_after_stride row k s]
  exact fin_twelve_ambient_roundtrip (enumerationPhaseFinAmbientAfterStride row k s)

/-- Stride square stated on **`Fin ambientDim`** phase data (bundles **`enumeration_phase_stride_square_ambient`** through **`finAmbientToTwelve`**). -/
theorem enumeration_phase_stride_square_via_ambient_chart (row : DiscretePeriodicCarrier) (k s : Nat) :
    iteratedCyclicSucc h12 (k * s) (finAmbientToTwelve (enumerationPhaseFinAmbient row)) =
      finAmbientToTwelve (enumerationPhaseFinAmbientAfterStride row k s) := by
  change iteratedCyclicSucc h12 (k * s) (enumerationPhaseFinTwelve row) =
      finAmbientToTwelve (enumerationPhaseFinAmbientAfterStride row k s)
  rw [enumeration_phase_fin_twelve_iterate_via_ambient_carrier row k s]
  exact congrArg finAmbientToTwelve (enumeration_phase_stride_square_ambient row k s)

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
