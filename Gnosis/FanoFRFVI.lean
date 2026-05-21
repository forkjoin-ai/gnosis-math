import Init
import Gnosis.FanoIncidence

namespace Gnosis
namespace FanoFRFVI

/-!
# Fano carrier for Fork/Race/Fold/Vent/Interfere

This module gives the finite, discrete reading of the FRF-VI carrier.  The
claim proved here is deliberately structural: the seven scheduler coordinates
are embedded in the seven visible points of the Fano plane, and every distinct
pair has a unique third point whose XOR parity closes back to the root.
-/

open FanoIncidence

/-- Seven FRF-VI coordinates: five operational primitives plus the two extra
axes needed to close the projective carrier. -/
inductive FRFVIPoint where
  | fork
  | race
  | fold
  | vent
  | interfereConstructive
  | interfereDestructive
  | clinamen
  deriving DecidableEq, Repr

open FRFVIPoint

/-- Embed the seven FRF-VI coordinates into the visible Fano carrier. -/
def toFanoPoint : FRFVIPoint → FanoPoint
  | fork => .b001
  | race => .b010
  | fold => .b011
  | vent => .b100
  | interfereConstructive => .b101
  | interfereDestructive => .b110
  | clinamen => .b111

/-- Recover the FRF-VI coordinate named by a visible Fano point. -/
def ofFanoPoint : FanoPoint → FRFVIPoint
  | .b001 => fork
  | .b010 => race
  | .b011 => fold
  | .b100 => vent
  | .b101 => interfereConstructive
  | .b110 => interfereDestructive
  | .b111 => clinamen

theorem of_to_fano_point (p : FRFVIPoint) :
    ofFanoPoint (toFanoPoint p) = p := by
  cases p <;> rfl

theorem to_of_fano_point (p : FanoPoint) :
    toFanoPoint (ofFanoPoint p) = p := by
  cases p <;> rfl

theorem toFanoPoint_injective :
    Function.Injective toFanoPoint := by
  intro a b h
  have h' := congrArg ofFanoPoint h
  simpa [of_to_fano_point] using h'

/-- The explicit seven-coordinate FRF-VI carrier. -/
def frfviCarrier : List FRFVIPoint :=
  [ fork
  , race
  , fold
  , vent
  , interfereConstructive
  , interfereDestructive
  , clinamen
  ]

theorem frfvi_carrier_has_seven_points :
    frfviCarrier.length = 7 :=
  rfl

/-- Complete a distinct pair of FRF-VI coordinates by taking the Fano third
point and translating it back to the FRF-VI naming layer. -/
def thirdPoint (a b : FRFVIPoint) : FRFVIPoint :=
  ofFanoPoint (completePair (toFanoPoint a) (toFanoPoint b))

/-- Incidence relation for the FRF-VI carrier, inherited from Fano incidence. -/
def frfviLine (a b c : FRFVIPoint) : Prop :=
  a ≠ b ∧ c = thirdPoint a b

theorem distinct_frfvi_pair_has_unique_third_point
    (a b : FRFVIPoint) (hab : a ≠ b) :
    thirdPoint a b ≠ a ∧
    thirdPoint a b ≠ b ∧
    frfviLine a b (thirdPoint a b) ∧
    ∀ c, c ≠ a → c ≠ b → frfviLine a b c → c = thirdPoint a b := by
  have hFanoDistinct : toFanoPoint a ≠ toFanoPoint b := by
    intro h
    exact hab (toFanoPoint_injective h)
  have h := distinct_pair_unique_completion
    (toFanoPoint a) (toFanoPoint b) hFanoDistinct
  refine ⟨?_, ?_, ⟨hab, rfl⟩, ?_⟩
  · intro hEq
    apply h.1
    calc
      completePair (toFanoPoint a) (toFanoPoint b)
          = toFanoPoint (thirdPoint a b) := by
              simp [thirdPoint, to_of_fano_point]
      _ = toFanoPoint a := congrArg toFanoPoint hEq
  · intro hEq
    apply h.2.1
    calc
      completePair (toFanoPoint a) (toFanoPoint b)
          = toFanoPoint (thirdPoint a b) := by
              simp [thirdPoint, to_of_fano_point]
      _ = toFanoPoint b := congrArg toFanoPoint hEq
  · intro c _ _ hLine
    exact hLine.2

/-- The FRF-VI line closure is the same zero-XOR parity law as the underlying
Fano plane. -/
theorem frfvi_third_point_zero_parity
    (a b : FRFVIPoint) (hab : a ≠ b) :
    collide
      (collide (toFanoPoint a).state (toFanoPoint b).state)
      (toFanoPoint (thirdPoint a b)).state =
    godPosition := by
  have hFanoDistinct : toFanoPoint a ≠ toFanoPoint b := by
    intro h
    exact hab (toFanoPoint_injective h)
  simpa [thirdPoint, to_of_fano_point] using
    completePair_xor_parity_zero (toFanoPoint a) (toFanoPoint b) hFanoDistinct

/-- Concrete Fork/Race closure: the Fano third point is Fold. -/
theorem fork_race_closes_to_fold :
    thirdPoint fork race = fold :=
  rfl

/-- Concrete Fork/Vent closure: the constructive interference axis closes the
line. -/
theorem fork_vent_closes_to_constructive_interference :
    thirdPoint fork vent = interfereConstructive :=
  rfl

/-- Concrete Race/Vent closure: the destructive interference axis closes the
line. -/
theorem race_vent_closes_to_destructive_interference :
    thirdPoint race vent = interfereDestructive :=
  rfl

/-- Concrete Fork/destructive-interference closure: the clinamen closes the
line. -/
theorem fork_destructive_interference_closes_to_clinamen :
    thirdPoint fork interfereDestructive = clinamen :=
  rfl

end FanoFRFVI
end Gnosis
