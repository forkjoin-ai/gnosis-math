import Gnosis.CalatravaBridge

/-
  RippledHelixMemory.lean
  ========================

  A finite memory sketch for the stair/bridge unification: ports index helix
  lanes, ripple positions index local up/down states, and folding pairs each
  lane with its opposite check lane. The two-port bridge slice remains the
  pathologic case; increasing ports and ripples gives the address surface used
  by the visual ramp bundle.

  Init-only surface: closed arithmetic uses `decide`; structural equalities use
  `rfl`; no Mathlib, no `omega`.
-/

namespace GnosisMath
namespace RippledHelixMemory

open GnosisMath.CalatravaBridge

/-- A helix lane is a bridge boundary port used as a memory lane. -/
abbrev HelixLane (ports : Nat) := BoundaryPort ports

/-- A ripple slot is one up/down position along a lane. -/
abbrev RippleSlot (ripples : Nat) := Fin ripples

/-- A finite memory coordinate on a rippled helix. -/
structure RippleAddress (ports ripples : Nat) where
  lane : HelixLane ports
  slot : RippleSlot ripples

/-- The pathologic memory slice: two lanes and two ripple slots. -/
abbrev PathologicMemoryAddress := RippleAddress 2 2

/-- Concrete high-port/high-ripple playground used by the visual prototype. -/
def highPortCount : Nat := 9
def highRippleCount : Nat := 12

/-- Address capacity of the finite rippled helix carrier. -/
def addressCapacity (ports ripples : Nat) : Nat := ports * ripples

/-- Opposite-lane folding used for redundant check paths. -/
def foldLane {ports : Nat} (h : 0 < ports) (lane : HelixLane ports) : HelixLane ports :=
  ⟨(lane.val + ports / 2) % ports, Nat.mod_lt _ h⟩

/-- A folded address keeps the same ripple slot and moves to the check lane. -/
def foldAddress {ports ripples : Nat} (h : 0 < ports)
    (addr : RippleAddress ports ripples) : RippleAddress ports ripples where
  lane := foldLane h addr.lane
  slot := addr.slot

/-- The two-lane pathologic case folds lane zero to lane one. -/
theorem two_lane_zero_folds_to_one :
    foldLane (by decide : 0 < 2) (0 : HelixLane 2) = (1 : HelixLane 2) := by decide

/-- The two-lane pathologic case folds lane one back to lane zero. -/
theorem two_lane_one_folds_to_zero :
    foldLane (by decide : 0 < 2) (1 : HelixLane 2) = (0 : HelixLane 2) := by decide

/-- Folding preserves the ripple slot in the two-lane pathologic case. -/
theorem two_lane_fold_preserves_slot (slot : RippleSlot 2) :
    (foldAddress (by decide : 0 < 2)
      ({ lane := (0 : HelixLane 2), slot := slot } : PathologicMemoryAddress)).slot = slot := rfl

/-- High ports and high ripples give a 108-coordinate address surface. -/
theorem high_helix_capacity_closed :
    addressCapacity highPortCount highRippleCount = 108 := by decide

/-- The pathologic two-by-two slice has only four coordinates. -/
theorem pathologic_capacity_closed :
    addressCapacity 2 2 = 4 := by decide

/-- The high rippled helix strictly exceeds the pathologic slice. -/
theorem high_helix_exceeds_pathologic :
    addressCapacity 2 2 < addressCapacity highPortCount highRippleCount := by decide

/--
  Rippled-helix memory certificate: the bridge/stair carrier can be read as a
  finite address surface where lanes are ports, slots are ripples, and the fold
  operation supplies the check lane for the smallest two-port case.
-/
theorem rippled_helix_memory_bundle :
    foldLane (by decide : 0 < 2) (0 : HelixLane 2) = (1 : HelixLane 2) ∧
    foldLane (by decide : 0 < 2) (1 : HelixLane 2) = (0 : HelixLane 2) ∧
    addressCapacity 2 2 = 4 ∧
    addressCapacity highPortCount highRippleCount = 108 ∧
    addressCapacity 2 2 < addressCapacity highPortCount highRippleCount :=
  ⟨two_lane_zero_folds_to_one, two_lane_one_folds_to_zero,
   pathologic_capacity_closed, high_helix_capacity_closed,
   high_helix_exceeds_pathologic⟩

end RippledHelixMemory
end GnosisMath
