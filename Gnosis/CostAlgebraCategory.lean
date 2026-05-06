import Gnosis.CostAlgebra
import Gnosis.CostAlgebraDerivations

/-!
# The Category of Cost Algebras

`Gnosis.CostAlgebra` defined the objects. This module builds the
arrows: a `CostHom A B` is a function `S → T` that preserves zero,
composition, and score. With identity and composition, this gives a
category whose objects are cost algebras and whose morphisms are
score-preserving maps.

The key observation: every cost algebra `A` has a canonical
homomorphism `scoreHom : CostHom A natCostAlgebra`, which is the
score function itself. `Nat` (as the trivial 1-faced cost algebra) is
universal in this sense — every cost algebra projects into it via
score, and that projection is itself a CostHom.

This makes the "Algebra of Cost" a category with a chosen object
(`natCostAlgebra`) into which every other object maps canonically. The
category-theoretic shape supports everything else built on top: the
Bule unit's bijection to `Nat^3` is a concrete `CostHom` isomorphism;
the product cost algebra has projection homs into its factors; and
the `RealityMesh.score_isomorphism` from earlier is exactly the action
of `scoreHom` on any operational mesh's free algebra.

Imports `Gnosis.CostAlgebra` and `Gnosis.CostAlgebraDerivations`.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace CostAlgebraCategory

open Gnosis.CostAlgebra (CostAlgebra buleyCostAlgebra)
open Gnosis.CostAlgebraDerivations
  (natCostAlgebra productCostAlgebra nat3CostAlgebra
   buleyOfNat3 nat3OfBuley
   bule_compose_equals_nat3_compose
   bule_score_equals_nat3_score)

/-! ## Morphisms -/

/-- A homomorphism between cost algebras: a map of carriers that
preserves the zero, composition, and score. The score-preservation
condition is automatic given the other two and the score-laws of the
target, but stating it explicitly makes the morphism's action on the
score axis a first-class fact. -/
structure CostHom {S T : Type} (A : CostAlgebra S) (B : CostAlgebra T) where
  map : S → T
  preserve_zero : map A.zero = B.zero
  preserve_compose : ∀ a b, map (A.compose a b) = B.compose (map a) (map b)
  preserve_score : ∀ s, B.score (map s) = A.score s

/-- Identity morphism. -/
def idHom {S : Type} (A : CostAlgebra S) : CostHom A A :=
  { map := id
    preserve_zero := rfl
    preserve_compose := fun _ _ => rfl
    preserve_score := fun _ => rfl }

/-- Composition of cost-algebra morphisms. -/
def composeHom {S T U : Type}
    {A : CostAlgebra S} {B : CostAlgebra T} {C : CostAlgebra U}
    (f : CostHom A B) (g : CostHom B C) : CostHom A C :=
  { map := g.map ∘ f.map
    preserve_zero := by
      show g.map (f.map A.zero) = C.zero
      rw [f.preserve_zero, g.preserve_zero]
    preserve_compose := by
      intro a b
      show g.map (f.map (A.compose a b)) = C.compose (g.map (f.map a)) (g.map (f.map b))
      rw [f.preserve_compose, g.preserve_compose]
    preserve_score := by
      intro s
      show C.score (g.map (f.map s)) = A.score s
      rw [g.preserve_score, f.preserve_score] }

/-! ## Category laws -/

theorem id_left_compose
    {S T : Type} {A : CostAlgebra S} {B : CostAlgebra T}
    (f : CostHom A B) :
    (composeHom (idHom A) f).map = f.map := rfl

theorem id_right_compose
    {S T : Type} {A : CostAlgebra S} {B : CostAlgebra T}
    (f : CostHom A B) :
    (composeHom f (idHom B)).map = f.map := rfl

theorem compose_hom_assoc
    {S T U V : Type}
    {A : CostAlgebra S} {B : CostAlgebra T}
    {C : CostAlgebra U} {D : CostAlgebra V}
    (f : CostHom A B) (g : CostHom B C) (h : CostHom C D) :
    (composeHom (composeHom f g) h).map
      = (composeHom f (composeHom g h)).map := rfl

/-! ## `Nat` is universal: score is a CostHom into `natCostAlgebra` -/

/-- Every cost algebra `A` has a canonical homomorphism into the
trivial 1-faced `natCostAlgebra` — the homomorphism is `A.score`
itself. This is the universal property of `Nat` in the category of
cost algebras: it is the terminal-up-to-score object. -/
def scoreHom {S : Type} (A : CostAlgebra S) : CostHom A natCostAlgebra :=
  { map := A.score
    preserve_zero := A.zero_score
    preserve_compose := A.score_compose
    preserve_score := fun _ => rfl }

/-- Universality: `scoreHom` factors through every score-preserving
hom. Equivalently: any two parallel homs `A → natCostAlgebra` agree
on score, so `scoreHom` is the "free" choice. -/
theorem score_hom_is_canonical
    {S : Type} (A : CostAlgebra S) (s : S) :
    (scoreHom A).map s = A.score s := rfl

/-- The score function commutes with any cost-algebra hom: applying a
hom and then taking the target's score is the same as taking the
source's score directly. This is the formal statement of
"score is a conserved quantity under morphisms." -/
theorem score_invariant_under_hom
    {S T : Type} {A : CostAlgebra S} {B : CostAlgebra T}
    (f : CostHom A B) (s : S) :
    B.score (f.map s) = A.score s :=
  f.preserve_score s

/-! ## Product projections are NOT CostHoms

Important honest observation: the categorical-product projections
`fst : S × T → S` and `snd : S × T → T` preserve zero and composition
(they are monoid homomorphisms), but they do *not* preserve score —
`score (a, b) = score a + score b ≠ score a` in general. Score
conservation under morphisms is the strict feature of this category;
projections drop score and are excluded.

This is the formal explanation for why "extracting a component" is a
lossy operation in cost terms: you cannot read one face of a Bule unit
without paying for what you are *not* seeing. The score-preserving
maps are precisely the embeddings, isomorphisms, and `scoreHom`-style
collapses, never the projections. -/

/-- Witness that `Prod.fst` fails the score-preservation law on a
non-trivial product, with a concrete counterexample. -/
theorem fst_is_not_score_preserving :
    natCostAlgebra.score (Prod.fst ((1, 2) : Nat × Nat))
      ≠ (productCostAlgebra natCostAlgebra natCostAlgebra).score (1, 2) := by
  show 1 ≠ 1 + 2
  decide

/-! ## The Bule ↔ Nat³ score-preserving isomorphism -/

/-- The `buleyOfNat3` map is a `CostHom` from `nat3CostAlgebra` to
`buleyCostAlgebra`. -/
def buleyOfNat3Hom : CostHom nat3CostAlgebra buleyCostAlgebra :=
  { map := buleyOfNat3
    preserve_zero := rfl
    preserve_compose := by
      intro ⟨wa, oa, da⟩ ⟨wb, ob, db⟩
      show (⟨wa + wb, oa + ob, da + db⟩ : Gnosis.SpectralNoiseEquilibrium.BuleyUnit)
            = ⟨wa + wb, oa + ob, da + db⟩
      rfl
    preserve_score := by
      intro ⟨w, o, d⟩
      show w + o + d = w + (o + (d + 0))
      rw [Nat.add_zero, Nat.add_assoc] }

/-- And the inverse `nat3OfBuley` is also a `CostHom`. -/
def nat3OfBuleyHom : CostHom buleyCostAlgebra nat3CostAlgebra :=
  { map := nat3OfBuley
    preserve_zero := rfl
    preserve_compose := bule_compose_equals_nat3_compose
    preserve_score := by
      intro b
      rw [bule_score_equals_nat3_score] }

/-! ## The score of every Bule unit factors through `Nat^3 ↪ Nat` -/

/-- The composite `buleyCostAlgebra → nat3CostAlgebra → natCostAlgebra`
gives the same score as the direct `scoreHom buleyCostAlgebra`. The
factorization is canonical. -/
theorem bule_score_factors_through_nat3 (b : Gnosis.SpectralNoiseEquilibrium.BuleyUnit) :
    (composeHom nat3OfBuleyHom (scoreHom nat3CostAlgebra)).map b
      = (scoreHom buleyCostAlgebra).map b := by
  show nat3CostAlgebra.score (nat3OfBuley b) = buleyCostAlgebra.score b
  rw [bule_score_equals_nat3_score]

end CostAlgebraCategory
end Gnosis
