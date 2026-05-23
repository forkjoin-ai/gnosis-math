import Init
import Gnosis.Body.FixedPoint

/-!
# Joint Constraints

Hinge / ball / fixed joints with a closed angular range `[minAngle, maxAngle]`
(angles are signed fixed-point `Int`). The motor controller clamps requested
angles into the admissible range; `clampAngle_admissible` proves the clamp can
never produce an out-of-range angle for a well-formed joint.
-/

namespace Gnosis.Body.Joints

open Gnosis.Body.FixedPoint

/-- Mechanical degrees of freedom of a joint. -/
inductive JointKind where
  | hinge   -- 1 rotational DOF (knee, elbow)
  | ball    -- 3 rotational DOF (hip, shoulder)
  | fixed   -- 0 DOF (welded)
  deriving Repr, DecidableEq

/-- A joint with a closed angular range. -/
structure Joint where
  kind : JointKind
  angle : Int
  minAngle : Int
  maxAngle : Int
  deriving Repr

/-- Limits are coherent: the lower bound does not exceed the upper bound. -/
def Joint.wellFormed (j : Joint) : Prop := j.minAngle ≤ j.maxAngle

/-- An angle lies within the joint's admissible range. -/
def Joint.admissible (j : Joint) (a : Int) : Prop :=
  j.minAngle ≤ a ∧ a ≤ j.maxAngle

/-- Clamp a requested angle into `[minAngle, maxAngle]`. -/
def clampAngle (j : Joint) (a : Int) : Int :=
  if a < j.minAngle then j.minAngle
  else if a > j.maxAngle then j.maxAngle
  else a

/-- **Clamping is admissible**: for any well-formed joint and requested angle,
    `clampAngle` yields an angle inside the joint's range. -/
theorem clampAngle_admissible (j : Joint) (a : Int) (h : j.wellFormed) :
    j.admissible (clampAngle j a) := by
  unfold Joint.admissible clampAngle
  unfold Joint.wellFormed at h
  by_cases h1 : a < j.minAngle
  · rw [if_pos h1]
    exact ⟨Int.le_refl j.minAngle, h⟩
  · rw [if_neg h1]
    by_cases h2 : a > j.maxAngle
    · rw [if_pos h2]
      exact ⟨h, Int.le_refl j.maxAngle⟩
    · rw [if_neg h2]
      exact ⟨Int.not_lt.mp h1, Int.not_lt.mp h2⟩

/-- Clamping an already-admissible angle is the identity. -/
theorem clampAngle_id_of_admissible (j : Joint) (a : Int) (h : j.admissible a) :
    clampAngle j a = a := by
  unfold clampAngle
  unfold Joint.admissible at h
  rw [if_neg (Int.not_lt.mpr h.left), if_neg (Int.not_lt.mpr h.right)]

end Gnosis.Body.Joints
