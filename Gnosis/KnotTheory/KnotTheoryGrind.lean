import Gnosis.KnotComplexityAsBuleCost

namespace Gnosis
namespace KnotTheoryGrind

/-!
# Knot Theory Grind

Finite theorem grind over the existing knot/Bule accounting core.  The old
cross-pollination file mixed unavailable spiral and scheduler APIs; this
restoration keeps the reusable knot-token invariants that already compile in
the Init-only package.
-/

open KnotComplexityAsBuleCost
open Gnosis.SpectralNoiseEquilibrium (BuleyUnit BuleyFace swerveLift)

def connectedSum (left right : KnotDiagram) : KnotDiagram :=
  mkKnot (left.crossing_count + right.crossing_count)

@[simp] theorem connected_sum_crossing_count
    (left right : KnotDiagram) :
    (connectedSum left right).crossing_count =
      left.crossing_count + right.crossing_count := by
  rfl

theorem connected_sum_identity_left (knot : KnotDiagram) :
    (connectedSum unknot knot).crossing_count = knot.crossing_count := by
  exact Nat.zero_add knot.crossing_count

theorem connected_sum_identity_right (knot : KnotDiagram) :
    (connectedSum knot unknot).crossing_count = knot.crossing_count := by
  exact Nat.add_zero knot.crossing_count

theorem connected_sum_associative
    (a b c : KnotDiagram) :
    (connectedSum (connectedSum a b) c).crossing_count =
      (connectedSum a (connectedSum b c)).crossing_count := by
  exact Nat.add_assoc a.crossing_count b.crossing_count c.crossing_count

theorem connected_sum_commutative
    (a b : KnotDiagram) :
    (connectedSum a b).crossing_count =
      (connectedSum b a).crossing_count := by
  exact Nat.add_comm a.crossing_count b.crossing_count

theorem connected_sum_cost_additive
    (a b : KnotDiagram) :
    bule_cost_of_knot (connectedSum a b) =
      bule_cost_of_knot a + bule_cost_of_knot b := by
  rfl

theorem connected_sum_never_simpler_left
    (a b : KnotDiagram) :
    a.crossing_count ≤ (connectedSum a b).crossing_count := by
  exact Nat.le_add_right _ _

theorem connected_sum_never_simpler_right
    (a b : KnotDiagram) :
    b.crossing_count ≤ (connectedSum a b).crossing_count := by
  exact Nat.le_add_left _ _

def chainKnots (knot : KnotDiagram) : Nat -> KnotDiagram
  | 0 => unknot
  | n + 1 => connectedSum knot (chainKnots knot n)

theorem chain_knots_crossing_count
    (knot : KnotDiagram)
    (n : Nat) :
    (chainKnots knot n).crossing_count = n * knot.crossing_count := by
  induction n with
  | zero =>
      exact (Nat.zero_mul knot.crossing_count).symm
  | succ n ih =>
      simp [chainKnots, connectedSum, ih, Nat.succ_mul, Nat.add_comm]

theorem chain_knots_cost
    (knot : KnotDiagram)
    (n : Nat) :
    bule_cost_of_knot (chainKnots knot n) =
      n * bule_cost_of_knot knot := by
  exact chain_knots_crossing_count knot n

theorem session_ledger_decomposes_as_connected_sum :
    (connectedSum
        (connectedSum
          (connectedSum
            (connectedSum f1_falsification_knot f2_falsification_knot)
            f3_falsification_knot)
          f4_falsification_knot)
        f5_falsification_knot).crossing_count = 5 := by
  decide

theorem swerve_lift_connected_sum_with_one_crossing
    (bule : BuleyUnit)
    (face : BuleyFace) :
    knot_of_buley_unit (swerveLift bule face) =
      connectedSum (knot_of_buley_unit bule) (mkKnot 1) := by
  apply congrArg mkKnot
  exact swerve_lift_adds_one_crossing bule face

theorem swerve_lift_cost_is_connected_sum_cost
    (bule : BuleyUnit)
    (face : BuleyFace) :
    bule_cost_of_knot (knot_of_buley_unit (swerveLift bule face)) =
      bule_cost_of_knot
        (connectedSum (knot_of_buley_unit bule) (mkKnot 1)) := by
  rw [swerve_lift_connected_sum_with_one_crossing]

theorem two_crossing_self_sum_even (knot : KnotDiagram) :
    ∃ half : Nat, (connectedSum knot knot).crossing_count = 2 * half := by
  exact ⟨knot.crossing_count, (Nat.two_mul knot.crossing_count).symm⟩

theorem nontrivial_chain_pays_positive_tax
    (knot : KnotDiagram)
    (hKnot : knot.crossing_count ≠ 0)
    (n : Nat)
    (hN : 0 < n) :
    0 < bule_cost_of_knot (chainKnots knot n) := by
  rw [chain_knots_cost]
  exact Nat.mul_pos hN (Nat.pos_of_ne_zero hKnot)

end KnotTheoryGrind
end Gnosis
