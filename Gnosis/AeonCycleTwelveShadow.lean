import Init
import Gnosis.CircadianGnosisAlignment
import Gnosis.DiscreteClosedTimelikeStep
import Gnosis.AmplituhedronGrassmannian

namespace Gnosis
namespace AeonCycleTwelveShadow

/-!
# Twelve-cycle shadow: chords, **66** pairs, Plücker count, modular fixes

Modulus **`n = Circadian.aeon = 12`** with rotation from `DiscreteClosedTimelikeStep`.

## Chord

`circChordAux` is **rot-invariant** (`circChordAux_rot`) — shadow of **translation on `ℤ/12ℤ`**.

## **66** (different sets, same cardinal)

* `pairsIJ` — unordered **`i < j`**, length **66**.
* `kSubsets 2 12` — ordered Plücker labels, length **66**.

## Distance classes

`shortChord` on `pairsIJ` yields per-class counts **12,12,12,12,12,6**.

## Modular return

`iteratedCyclicSucc h12 m` is the **identity map** on **`Fin 12`** iff **`12 ∣ m`**
(`iterate_all_fixed_iff_dvd`).
-/

def twelve : Nat :=
  12

theorem twelve_pos : 0 < twelve :=
  Nat.succ_pos _

abbrev h12 : 0 < twelve :=
  twelve_pos

theorem twelve_eq_aeon : twelve = Circadian.aeon :=
  rfl

open Gnosis.DiscreteClosedTimelikeStep
open AmplituhedronAttention.Grassmannian

abbrev rot : Fin twelve → Fin twelve :=
  cyclicSucc h12

def cwSpan (a b : Fin twelve) : Nat :=
  (b.val + twelve - a.val) % twelve

def circChordAux (a b : Fin twelve) : Nat :=
  let f := cwSpan a b
  min f (twelve - f)

theorem circChordAux_rot : ∀ a b : Fin twelve,
    circChordAux a b = circChordAux (rot a) (rot b) := by
  native_decide

theorem circChordAux_pos {a b : Fin twelve} (hab : a ≠ b) : 0 < circChordAux a b := by
  revert a b hab
  native_decide

def pairsIJ : List (Nat × Nat) :=
  (List.range twelve).flatMap fun i : Nat =>
    (List.range twelve).filterMap fun j : Nat =>
      if i < j then some (i, j) else none

theorem pairsIJ_length : pairsIJ.length = 66 := by
  native_decide

theorem kSubsets_two_twelve_length : (kSubsets 2 twelve).length = 66 := by
  native_decide

theorem pluckerLabelCount_eq_pairsIJ : (kSubsets 2 twelve).length = pairsIJ.length := by
  rw [kSubsets_two_twelve_length, pairsIJ_length]

theorem pairsIJ_fst_lt_snd (p : Nat × Nat) (hp : p ∈ pairsIJ) : p.1 < p.2 := by
  revert p hp
  native_decide

def shortChord (p : Nat × Nat) : Nat :=
  let d := p.2 - p.1
  min d (twelve - d)

theorem countChord_eq_one : (pairsIJ.filter (fun p => shortChord p = 1)).length = 12 := by
  native_decide

theorem countChord_eq_two : (pairsIJ.filter (fun p => shortChord p = 2)).length = 12 := by
  native_decide

theorem countChord_eq_three : (pairsIJ.filter (fun p => shortChord p = 3)).length = 12 := by
  native_decide

theorem countChord_eq_four : (pairsIJ.filter (fun p => shortChord p = 4)).length = 12 := by
  native_decide

theorem countChord_eq_five : (pairsIJ.filter (fun p => shortChord p = 5)).length = 12 := by
  native_decide

theorem countChord_eq_six : (pairsIJ.filter (fun p => shortChord p = 6)).length = 6 := by
  native_decide

theorem distClass_counts_sum : 12 + 12 + 12 + 12 + 12 + 6 = 66 :=
  rfl

def finZero : Fin twelve :=
  ⟨0, Nat.zero_lt_succ 11⟩

theorem iterate_zero_fixed_iff_dvd (m : Nat) :
    iteratedCyclicSucc h12 m finZero = finZero ↔ twelve ∣ m := by
  constructor
  · intro h
    have hv : (iteratedCyclicSucc h12 m finZero).val = finZero.val :=
      congrArg Fin.val h
    rw [iteratedCyclicSucc_val] at hv
    rw [show finZero.val = (0 : Nat) from rfl, Nat.zero_add] at hv
    rwa [Nat.dvd_iff_mod_eq_zero]
  · intro hm
    rw [Nat.dvd_iff_mod_eq_zero] at hm
    apply Fin.ext
    rw [iteratedCyclicSucc_val, show finZero.val = (0 : Nat) from rfl, Nat.zero_add]
    exact hm

theorem dvd_iterate_fixed (x : Fin twelve) (m : Nat) (hm : twelve ∣ m) :
    iteratedCyclicSucc h12 m x = x := by
  rcases hm with ⟨k, rfl⟩
  apply Fin.ext
  rw [iteratedCyclicSucc_val]
  simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.isLt]

theorem iterate_all_fixed_iff_dvd (m : Nat) :
    (∀ x : Fin twelve, iteratedCyclicSucc h12 m x = x) ↔ twelve ∣ m := by
  constructor
  · intro hall
    have hz := hall finZero
    exact (iterate_zero_fixed_iff_dvd m).1 hz
  · intro hm x
    exact dvd_iterate_fixed x m hm

end AeonCycleTwelveShadow
end Gnosis
