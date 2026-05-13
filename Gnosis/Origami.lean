import Init

namespace GnosisMath
namespace Origami

/-!
## Maekawa's Theorem
At any vertex in a flat-foldable crease pattern, the number of mountain folds (M)
and valley folds (V) differ by exactly 2.
-/

structure CreaseVertex where
  mountains : Nat
  valleys : Nat

def satisfiesMaekawa (v : CreaseVertex) : Prop :=
  ((v.mountains : Int) - (v.valleys : Int) = 2) ∨ ((v.valleys : Int) - (v.mountains : Int) = 2)

theorem int_sub_eq_two_implies_nat_eq_add_two (M V : Nat) (h : (M : Int) - (V : Int) = 2) : M = V + 2 := by
  have h1 : (M : Int) - (V : Int) + (V : Int) = 2 + (V : Int) := congrArg (· + (V : Int)) h
  rw [Int.sub_add_cancel] at h1
  have h2 : (M : Int) = ((V + 2 : Nat) : Int) := by
    rw [h1, Int.add_comm]
    exact (Int.natCast_add V 2).symm
  exact Int.ofNat_inj.mp h2

-- A corollary: the total degree (M + V) must be even.
theorem degree_is_even_if_maekawa (v : CreaseVertex) (h : satisfiesMaekawa v) : (v.mountains + v.valleys) % 2 = 0 := by
  cases h with
  | inl hM =>
    have eq : v.mountains = v.valleys + 2 := int_sub_eq_two_implies_nat_eq_add_two v.mountains v.valleys hM
    rw [eq]
    have h3 : v.valleys + 2 + v.valleys = 2 * (v.valleys + 1) := by
      rw [Nat.two_mul]
      ac_rfl
    rw [h3]
    exact Nat.mul_mod_right 2 (v.valleys + 1)
  | inr hV =>
    have eq : v.valleys = v.mountains + 2 := int_sub_eq_two_implies_nat_eq_add_two v.valleys v.mountains hV
    rw [eq]
    have h3 : v.mountains + (v.mountains + 2) = 2 * (v.mountains + 1) := by
      rw [Nat.two_mul]
      ac_rfl
    rw [h3]
    exact Nat.mul_mod_right 2 (v.mountains + 1)

/-!
## Kawasaki's Theorem
The sum of alternating angles around a flat-foldable vertex is 180 degrees.
-/

structure VertexAngles where
  n : Nat -- Number of pairs of angles (total 2n angles)
  alphaOddSum : Nat
  alphaEvenSum : Nat
  sum_is_360 : alphaOddSum + alphaEvenSum = 360

def satisfiesKawasaki (v : VertexAngles) : Prop :=
  v.alphaOddSum = 180 ∧ v.alphaEvenSum = 180

theorem kawasaki_implies_360 (v : VertexAngles) (h : satisfiesKawasaki v) : v.alphaOddSum + v.alphaEvenSum = 360 := by
  rw [h.left, h.right]

/-!
## Huzita-Hatori Axioms
Abstract geometric axioms of origami constructions.
-/

axiom Point : Type
axiom Line : Type

abbrev Fold := Line

axiom passesThrough : Fold → Point → Prop
axiom placesPointOnPoint : Fold → Point → Point → Prop
axiom placesLineOnLine : Fold → Line → Line → Prop
axiom perpendicular : Line → Line → Prop
axiom placesPointOnLine : Fold → Point → Line → Prop

axiom huzita_hatori_1 (p1 p2 : Point) : ∃ f : Fold, passesThrough f p1 ∧ passesThrough f p2
axiom huzita_hatori_2 (p1 p2 : Point) : ∃ f : Fold, placesPointOnPoint f p1 p2
axiom huzita_hatori_3 (l1 l2 : Line) : ∃ f : Fold, placesLineOnLine f l1 l2
axiom huzita_hatori_4 (p1 : Point) (l1 : Line) : ∃ f : Fold, perpendicular f l1 ∧ passesThrough f p1
axiom huzita_hatori_5 (p1 p2 : Point) (l1 : Line) : ∃ f : Fold, placesPointOnLine f p1 l1 ∧ passesThrough f p2
axiom huzita_hatori_6 (p1 p2 : Point) (l1 l2 : Line) : ∃ f : Fold, placesPointOnLine f p1 l1 ∧ placesPointOnLine f p2 l2
axiom huzita_hatori_7 (p1 : Point) (l1 l2 : Line) : ∃ f : Fold, perpendicular f l2 ∧ placesPointOnLine f p1 l1

/-!
## Layer Ordering and Non-Penetration
Two-Colorability and Layering
-/

axiom Face : Type
axiom adjacent : Face → Face → Prop

inductive Color
| Black
| White

def oppositeColor : Color → Color
  | Color.Black => Color.White
  | Color.White => Color.Black

theorem oppositeColor_involution (c : Color) : oppositeColor (oppositeColor c) = c := by
  cases c <;> rfl

axiom faceColor : Face → Color

axiom two_colorability (f1 f2 : Face) : adjacent f1 f2 → faceColor f1 = oppositeColor (faceColor f2)

axiom StackOrder : Face → Face → Prop
axiom stack_irreflexive (f : Face) : ¬ StackOrder f f
axiom stack_transitive (f1 f2 f3 : Face) : StackOrder f1 f2 → StackOrder f2 f3 → StackOrder f1 f3
axiom stack_asymmetric (f1 f2 : Face) : StackOrder f1 f2 → ¬ StackOrder f2 f1

end Origami
end GnosisMath
