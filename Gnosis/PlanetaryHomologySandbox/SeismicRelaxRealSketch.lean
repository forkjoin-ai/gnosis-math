/-!
# Seismic Relaxation Sketch

Init-only bounded-transfer replacement for the historical real-valued
two-patch relaxation theorem.

The executable TypeScript uses a real interpolation parameter `κ`; this
module records the exact conservation invariant in Nat form: transferring a
bounded amount of loaded stress from one patch to the other preserves the
total loaded stress.
-/

namespace PlanetaryHomologySandbox

/-- Two loaded stress patches. -/
structure TwoPatchStress where
  left : Nat
  right : Nat
deriving Repr, DecidableEq

/--
Transfer `delta` units from the right patch to the left patch.

The proof obligations are represented by the Nat expression `right - delta`;
the conservation theorem below requires `delta ≤ right`.
-/
def relaxRightToLeft (stress : TwoPatchStress) (delta : Nat) : TwoPatchStress :=
  { left := stress.left + delta
    right := stress.right - delta }

/-- Total loaded stress across both patches. -/
def totalLoadedStress (stress : TwoPatchStress) : Nat :=
  stress.left + stress.right

/-- Bounded transfer from right to left preserves total loaded stress. -/
theorem relaxRightToLeft_conserves_total
    (stress : TwoPatchStress)
    (delta : Nat)
    (hDelta : delta ≤ stress.right) :
    totalLoadedStress (relaxRightToLeft stress delta) =
      totalLoadedStress stress := by
  unfold totalLoadedStress relaxRightToLeft
  rw [Nat.add_assoc]
  rw [Nat.add_sub_of_le hDelta]

/-- Transfer `delta` units from the left patch to the right patch. -/
def relaxLeftToRight (stress : TwoPatchStress) (delta : Nat) : TwoPatchStress :=
  { left := stress.left - delta
    right := stress.right + delta }

/-- Bounded transfer from left to right preserves total loaded stress. -/
theorem relaxLeftToRight_conserves_total
    (stress : TwoPatchStress)
    (delta : Nat)
    (hDelta : delta ≤ stress.left) :
    totalLoadedStress (relaxLeftToRight stress delta) =
      totalLoadedStress stress := by
  unfold totalLoadedStress relaxLeftToRight
  rw [Nat.add_comm (stress.left - delta) (stress.right + delta)]
  rw [Nat.add_assoc]
  rw [Nat.add_sub_of_le hDelta]
  rw [Nat.add_comm stress.right stress.left]

end PlanetaryHomologySandbox
