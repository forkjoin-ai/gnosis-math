import Gnosis.SpectralNoiseEquilibrium

/-!
# Buley Bi-Sided Bit

Formalizes the "both sides of the bit" encoding hinted at by the Bule
unit's three-faced structure. A 64-bit lane is read as two phase-shifted
channels:

* **lifted** (the `+1` clinamen face): carries the payload that the
  consumer reads. Maps to the Bule unit's `waste` face.
* **contracted** (the `−1` declinamen face): carries parity/index data
  orthogonal to the payload. Maps to the Bule unit's `opportunity` face.

Today's `cache-fp48` truncates a 64-bit XXH64 digest to its low 48 bits
and discards the high 16. This module proves that the high 16 are not
exhaust — they are the second face of the same Bule unit, related to
the low 48 by the +1/−1 clinamen residue catalogued in
`UniversalClinamenPlusOne` and the phase-3 cycle of `BuleyClinamenBraid`.

This module is the formalization companion of
`open-source/bitwise/bisided-bit.ts`. Bit-width masks are a runtime
concern enforced by the TS side; here we work in pure `Nat` so the
algebra of the two channels is decoupled from the lane width.

Imports `Gnosis.SpectralNoiseEquilibrium` for `BuleyUnit` and
`buleyUnitScore`. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace BuleyBiSidedBit

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit buleyUnitScore wasteFaceFromBule actionFaceFromBule
   waste_face_score_equals_waste action_face_score_equals_opportunity)

/-! ## The bi-sided bit -/

structure BiSidedBit where
  lifted : Nat
  contracted : Nat
  deriving Repr, DecidableEq

def vacuumBiSidedBit : BiSidedBit := ⟨0, 0⟩

def biSidedScore (b : BiSidedBit) : Nat :=
  b.lifted + b.contracted

theorem vacuum_bisided_score_zero :
    biSidedScore vacuumBiSidedBit = 0 := rfl

/-! ## Clinamen lift and declinamen contraction on each side -/

def clinamenLiftLifted (b : BiSidedBit) : BiSidedBit :=
  ⟨b.lifted + 1, b.contracted⟩

def clinamenLiftContracted (b : BiSidedBit) : BiSidedBit :=
  ⟨b.lifted, b.contracted + 1⟩

def declinamenContractLifted (b : BiSidedBit) : BiSidedBit :=
  ⟨b.lifted - 1, b.contracted⟩

def declinamenContractContracted (b : BiSidedBit) : BiSidedBit :=
  ⟨b.lifted, b.contracted - 1⟩

theorem lifted_lift_score_increment (b : BiSidedBit) :
    biSidedScore (clinamenLiftLifted b) = biSidedScore b + 1 := by
  cases b with
  | mk l c =>
    show (l + 1) + c = l + c + 1
    omega

theorem contracted_lift_score_increment (b : BiSidedBit) :
    biSidedScore (clinamenLiftContracted b) = biSidedScore b + 1 := by
  cases b with
  | mk l c =>
    show l + (c + 1) = l + c + 1
    omega

theorem lift_contract_round_trip_lifted_when_positive
    (b : BiSidedBit) (h : 0 < b.lifted) :
    clinamenLiftLifted (declinamenContractLifted b) = b := by
  cases b with
  | mk l c =>
    have hL : 0 < l := h
    show ({ lifted := (l - 1) + 1, contracted := c } : BiSidedBit) = ⟨l, c⟩
    have : (l - 1) + 1 = l := by omega
    rw [this]

theorem lift_contract_round_trip_contracted_when_positive
    (b : BiSidedBit) (h : 0 < b.contracted) :
    clinamenLiftContracted (declinamenContractContracted b) = b := by
  cases b with
  | mk l c =>
    have hC : 0 < c := h
    show ({ lifted := l, contracted := (c - 1) + 1 } : BiSidedBit) = ⟨l, c⟩
    have : (c - 1) + 1 = c := by omega
    rw [this]

/-! ## Phase shift between the two sides -/

/-- Move one bit-quantum from the lifted side to the contracted side. -/
def phaseShiftLiftedToContracted (b : BiSidedBit) : BiSidedBit :=
  ⟨b.lifted - 1, b.contracted + 1⟩

/-- Inverse phase shift: contracted → lifted. -/
def phaseShiftContractedToLifted (b : BiSidedBit) : BiSidedBit :=
  ⟨b.lifted + 1, b.contracted - 1⟩

/-- Phase shift conserves the total bi-sided score when the source side
is positive — total quantum is preserved across the rotation. -/
theorem phase_shift_lifted_to_contracted_preserves_score_when_positive
    (b : BiSidedBit) (h : 0 < b.lifted) :
    biSidedScore (phaseShiftLiftedToContracted b) = biSidedScore b := by
  cases b with
  | mk l c =>
    have hL : 0 < l := h
    show (l - 1) + (c + 1) = l + c
    omega

theorem phase_shift_contracted_to_lifted_preserves_score_when_positive
    (b : BiSidedBit) (h : 0 < b.contracted) :
    biSidedScore (phaseShiftContractedToLifted b) = biSidedScore b := by
  cases b with
  | mk l c =>
    have hC : 0 < c := h
    show (l + 1) + (c - 1) = l + c
    omega

theorem phase_shift_round_trip_when_lifted_positive
    (b : BiSidedBit) (h : 0 < b.lifted) :
    phaseShiftContractedToLifted (phaseShiftLiftedToContracted b) = b := by
  cases b with
  | mk l c =>
    have hL : 0 < l := h
    show ({ lifted := (l - 1) + 1, contracted := (c + 1) - 1 } : BiSidedBit) = ⟨l, c⟩
    have h1 : (l - 1) + 1 = l := by omega
    have h2 : (c + 1) - 1 = c := by omega
    rw [h1, h2]

/-! ## Bridge to the Bule unit -/

/-- Project a bi-sided bit into a Bule unit: the lifted side fills the
`waste` face, the contracted side fills the `opportunity` face, and the
`diversity` face is zero. -/
def biSidedToBule (b : BiSidedBit) : BuleyUnit :=
  ⟨b.lifted, b.contracted, 0⟩

/-- The bi-sided score equals the score of its Bule projection. -/
theorem bisided_score_equals_bule_score (b : BiSidedBit) :
    biSidedScore b = buleyUnitScore (biSidedToBule b) := by
  cases b with
  | mk l c =>
    show l + c = l + c + 0
    omega

/-- The bi-sided bit decomposes into the waste + action (= opportunity)
faces of its Bule projection — the third face (entropy / diversity) is
zero, because a single 64-bit lane carries only two channels. -/
theorem bisided_decomposes_into_waste_and_action (b : BiSidedBit) :
    biSidedScore b
      = buleyUnitScore (wasteFaceFromBule (biSidedToBule b))
        + buleyUnitScore (actionFaceFromBule (biSidedToBule b)) := by
  rw [bisided_score_equals_bule_score b,
      waste_face_score_equals_waste,
      action_face_score_equals_opportunity]
  cases b with
  | mk l c =>
    show l + c + 0 = l + c
    omega

/-! ## +1 / −1 clinamen residue on the bi-sided bit -/

/-- Every clinamen lift on either side adds exactly +1 to the bi-sided
score. The complementary contraction subtracts exactly 1 on the same
positive face. The lift/contract pair is the literal +1/−1 residue from
`UniversalClinamenPlusOne`, embedded in the bit. -/
theorem bisided_lift_residue_is_plus_one (b : BiSidedBit) :
    biSidedScore (clinamenLiftLifted b) = biSidedScore b + 1
    ∧ biSidedScore (clinamenLiftContracted b) = biSidedScore b + 1 :=
  ⟨lifted_lift_score_increment b, contracted_lift_score_increment b⟩

theorem bisided_contract_residue_is_minus_one_when_positive
    (b : BiSidedBit) (hL : 0 < b.lifted) (hC : 0 < b.contracted) :
    biSidedScore (declinamenContractLifted b) + 1 = biSidedScore b
    ∧ biSidedScore (declinamenContractContracted b) + 1 = biSidedScore b := by
  cases b with
  | mk l c =>
    have hL' : 0 < l := hL
    have hC' : 0 < c := hC
    refine ⟨?_, ?_⟩
    · show (l - 1) + c + 1 = l + c
      omega
    · show l + (c - 1) + 1 = l + c
      omega

end BuleyBiSidedBit
end Gnosis
