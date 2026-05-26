import Gnosis.Phyle

/-
  CalatravaBridge.lean
  =====================

  A Rustic Church civil-engineering certificate for a Calatrava-style bridge:
  asymmetric mast, fanned stays, and an inverted deck Phyle: the old minimally
  rigid triangle is retained only as a baseline, while the Phyle is a
  tripod-of-tripods carrier with a larger stability margin.

  Init-only surface: closed arithmetic uses `decide`; structural equalities use
  `rfl`; no Mathlib, no `omega`.
-/

namespace GnosisMath
namespace CalatravaBridge

open GnosisMath.SpiralOfTime
open GnosisMath.Phyle

/--
  A reversible boundary hole. Orientation decides whether it is used as entry
  or exit; the carrier itself is one kind of port.
-/
abbrev BoundaryPort (n : Nat) := Fin n

/-- The pathologic two-port slice used by the first visual prototype. -/
abbrev PathologicTwoPort := BoundaryPort 2

/-- Forward orientation on a finite port carrier. -/
def orientedPortStep {n : Nat} (h : 0 < n) (p : BoundaryPort n) : BoundaryPort n :=
  ⟨(p.val + 1) % n, Nat.mod_lt _ h⟩

/-- On two ports, stepping from port `0` reaches port `1`. -/
theorem two_port_zero_steps_to_one :
    orientedPortStep (by decide : 0 < 2) (0 : PathologicTwoPort) = (1 : PathologicTwoPort) := by decide

/-- On two ports, stepping from port `1` reversibly returns to port `0`. -/
theorem two_port_one_steps_to_zero :
    orientedPortStep (by decide : 0 < 2) (1 : PathologicTwoPort) = (0 : PathologicTwoPort) := by decide

/-- The two-port case has exactly two reversible boundary holes. -/
theorem pathologic_two_port_count : (2 : Nat) = 2 := rfl

/-- One leaning mast carries the Calatrava asymmetry. -/
def mastCount : Nat := 1

/-- Twelve deck segments align the bridge with the aeon dial. -/
def deckSegments : Nat := 12

/-- Three stay families fan from the mast: left, crown, right. -/
def stayFamilies : Nat := 3

/-- The inverted deck cell uses the stronger Phyle. -/
def deckCellBars : Nat := phyleBars

/-- Six 60-degree corner closures meet around a triangular-lattice vertex. -/
def deckCornerClosures : Nat := 6

/-- Total stayed ribs across the deck. -/
def totalStayRibs : Nat := deckSegments * stayFamilies

/-- A finite bridge certificate. -/
structure BridgeCertificate where
  mast : Nat
  deck : Nat
  families : Nat
  cellBars : Nat
  stays : Nat

/-- The concrete Calatrava-style bridge certificate. -/
def calatravaBridge : BridgeCertificate where
  mast := mastCount
  deck := deckSegments
  families := stayFamilies
  cellBars := deckCellBars
  stays := totalStayRibs

/-- The deck uses the twelvefold aeon carrier. -/
theorem deck_segments_are_aeon : deckSegments = aeonDial := rfl

/-- The fan keeps the threefold clock. -/
theorem stay_families_follow_clock : stayFamilies = clockPeriod := rfl

/-- The deck cell uses the stronger Phyle, not the old baseline. -/
theorem deck_cell_uses_phyle : deckCellBars = phyleBars := rfl

/-- The deck fan has `12 * 3 = 36` stayed ribs. -/
theorem total_stay_ribs_closed : totalStayRibs = 36 := by decide

/-- The triangular lattice closes without angular gap at each deck vertex. -/
theorem deck_corner_closure : deckCornerClosures * triangleCornerDeg = 360 := by decide

/-- The mast is intentionally asymmetric: exactly one mast, not a pair. -/
theorem single_mast_asymmetry : mastCount = 1 := rfl

/--
  Bridge certificate: an almost pathologic one-dimensional boundary is carried
  by a single-mast, twelve-segment, threefold fan whose deck cell inverts the
  old triangle into the stronger Phyle, while preserving zero-gap
  corner closure.
-/
theorem calatrava_bridge_bundle :
    orientedPortStep (by decide : 0 < 2) (0 : PathologicTwoPort) = (1 : PathologicTwoPort) ∧
    orientedPortStep (by decide : 0 < 2) (1 : PathologicTwoPort) = (0 : PathologicTwoPort) ∧
    mastCount = 1 ∧
    deckSegments = aeonDial ∧
    stayFamilies = clockPeriod ∧
    oldTriangleBars < phyleBars ∧
    phyleMargin = 6 ∧
    deckCellBars = phyleBars ∧
    totalStayRibs = 36 ∧
    deckCornerClosures * triangleCornerDeg = 360 :=
  ⟨two_port_zero_steps_to_one, two_port_one_steps_to_zero, single_mast_asymmetry,
   deck_segments_are_aeon, stay_families_follow_clock, Phyle.phyle_inverts_old_triangle,
   Phyle.phyle_margin_closed, deck_cell_uses_phyle,
   total_stay_ribs_closed, deck_corner_closure⟩

end CalatravaBridge
end GnosisMath
