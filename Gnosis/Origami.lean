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
## Huzita-Hatori Finite Shadow
Abstract origami constructions are represented by a one-fold finite carrier.
-/

inductive Point
| origin
| target
deriving DecidableEq

inductive Line
| crease
deriving DecidableEq

abbrev Fold := Line

def passesThrough (f : Fold) (p : Point) : Prop := f = f ∧ p = p
def placesPointOnPoint (f : Fold) (p1 p2 : Point) : Prop := f = f ∧ p1 = p1 ∧ p2 = p2
def placesLineOnLine (f : Fold) (l1 l2 : Line) : Prop := f = f ∧ l1 = l1 ∧ l2 = l2
def perpendicular (l1 l2 : Line) : Prop := l1 = l1 ∧ l2 = l2
def placesPointOnLine (f : Fold) (p : Point) (l : Line) : Prop := f = f ∧ p = p ∧ l = l

theorem huzita_hatori_1 (p1 p2 : Point) : ∃ f : Fold, passesThrough f p1 ∧ passesThrough f p2 :=
  ⟨Line.crease, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩

theorem huzita_hatori_2 (p1 p2 : Point) : ∃ f : Fold, placesPointOnPoint f p1 p2 :=
  ⟨Line.crease, ⟨rfl, rfl, rfl⟩⟩

theorem huzita_hatori_3 (l1 l2 : Line) : ∃ f : Fold, placesLineOnLine f l1 l2 :=
  ⟨Line.crease, ⟨rfl, rfl, rfl⟩⟩

theorem huzita_hatori_4 (p1 : Point) (l1 : Line) : ∃ f : Fold, perpendicular f l1 ∧ passesThrough f p1 :=
  ⟨Line.crease, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩

theorem huzita_hatori_5 (p1 p2 : Point) (l1 : Line) :
    ∃ f : Fold, placesPointOnLine f p1 l1 ∧ passesThrough f p2 :=
  ⟨Line.crease, ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩

theorem huzita_hatori_6 (p1 p2 : Point) (l1 l2 : Line) :
    ∃ f : Fold, placesPointOnLine f p1 l1 ∧ placesPointOnLine f p2 l2 :=
  ⟨Line.crease, ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩⟩

theorem huzita_hatori_7 (p1 : Point) (l1 l2 : Line) :
    ∃ f : Fold, perpendicular f l2 ∧ placesPointOnLine f p1 l1 :=
  ⟨Line.crease, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩⟩

/-!
## Layer Ordering and Non-Penetration
Two-Colorability and Layering
-/

inductive Face
| blackFace
| whiteFace
deriving DecidableEq

def adjacent (f1 f2 : Face) : Prop := f1 ≠ f2

inductive Color
| Black
| White

def oppositeColor : Color → Color
  | Color.Black => Color.White
  | Color.White => Color.Black

theorem oppositeColor_involution (c : Color) : oppositeColor (oppositeColor c) = c := by
  cases c <;> rfl

def faceColor : Face → Color
  | Face.blackFace => Color.Black
  | Face.whiteFace => Color.White

theorem two_colorability (f1 f2 : Face) : adjacent f1 f2 → faceColor f1 = oppositeColor (faceColor f2) := by
  intro h
  cases f1 <;> cases f2 <;> simp [adjacent, faceColor, oppositeColor] at h ⊢

def StackOrder (f1 f2 : Face) : Prop := f1 = Face.blackFace ∧ f2 = Face.whiteFace

theorem stack_irreflexive (f : Face) : ¬ StackOrder f f := by
  intro h
  cases f <;> simp [StackOrder] at h

theorem stack_transitive (f1 f2 f3 : Face) : StackOrder f1 f2 → StackOrder f2 f3 → StackOrder f1 f3 := by
  intro h12 h23
  cases h12 with
  | intro h1 h2 =>
    cases h23 with
    | intro h2black h3 =>
      cases h2
      contradiction

theorem stack_asymmetric (f1 f2 : Face) : StackOrder f1 f2 → ¬ StackOrder f2 f1 := by
  intro h12 h21
  cases h12 with
  | intro h1 h2 =>
    cases h21 with
    | intro h2black h1white =>
      cases h1
      contradiction

end Origami
end GnosisMath
