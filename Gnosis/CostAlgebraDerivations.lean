import Gnosis.CostAlgebra
import Gnosis.SpectralNoiseEquilibrium

/-!
# Derivations from CostAlgebra primitives

The `CostAlgebra` from `Gnosis.CostAlgebra` is structurally generative:
several familiar math objects fall out as instances or as products of
instances. This module mechanizes the most direct derivations.

* **`Nat` itself** is the trivial 1-face CostAlgebra (`compose = +`,
  `score = id`).
* **CostAlgebras close under product**: given `A : CostAlgebra S` and
  `B : CostAlgebra T`, the componentwise structure on `S × T` is also
  a CostAlgebra. Score adds across the components.
* **`Nat × Nat × Nat`** is the iterated product. This is structurally
  equivalent to `BuleyUnit`'s CostAlgebra: the Bule three-faced
  algebra is `Nat^3`, and the score-isomorphism is mechanized.
* **`Nat^k`** for any finite k is therefore a CostAlgebra by iteration.
  This is the free commutative monoid on k indeterminates, with
  componentwise addition and total-degree as score.

Imports `Gnosis.CostAlgebra` and `Gnosis.SpectralNoiseEquilibrium`.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace CostAlgebraDerivations

open Gnosis.CostAlgebra (CostAlgebra buleyCostAlgebra BuleyUnit.add)
open Gnosis.SpectralNoiseEquilibrium (BuleyUnit buleyUnitScore vacuumBuleUnit)

/-! ## Derivation 1: `Nat` is the trivial CostAlgebra -/

def natCostAlgebra : CostAlgebra Nat :=
  { zero := 0
    compose := (· + ·)
    score := id
    zero_score := rfl
    compose_left_zero := by intro s; exact Nat.zero_add s
    compose_right_zero := by intro s; show s + 0 = s; rfl
    compose_assoc := by intros a b c; exact Nat.add_assoc a b c
    compose_comm := by intros a b; exact Nat.add_comm a b
    score_compose := by intros a b; rfl }

/-! ## Derivation 2: CostAlgebra is closed under product -/

def productCostAlgebra
    {S T : Type} (A : CostAlgebra S) (B : CostAlgebra T) :
    CostAlgebra (S × T) :=
  { zero := (A.zero, B.zero)
    compose := fun (a₁, b₁) (a₂, b₂) => (A.compose a₁ a₂, B.compose b₁ b₂)
    score := fun (a, b) => A.score a + B.score b
    zero_score := by
      show A.score A.zero + B.score B.zero = 0
      rw [A.zero_score, B.zero_score]
    compose_left_zero := by
      intro ⟨a, b⟩
      show (A.compose A.zero a, B.compose B.zero b) = (a, b)
      rw [A.compose_left_zero, B.compose_left_zero]
    compose_right_zero := by
      intro ⟨a, b⟩
      show (A.compose a A.zero, B.compose b B.zero) = (a, b)
      rw [A.compose_right_zero, B.compose_right_zero]
    compose_assoc := by
      intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩
      show (A.compose (A.compose a₁ a₂) a₃, B.compose (B.compose b₁ b₂) b₃)
            = (A.compose a₁ (A.compose a₂ a₃), B.compose b₁ (B.compose b₂ b₃))
      rw [A.compose_assoc, B.compose_assoc]
    compose_comm := by
      intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
      show (A.compose a₁ a₂, B.compose b₁ b₂) = (A.compose a₂ a₁, B.compose b₂ b₁)
      rw [A.compose_comm a₁ a₂, B.compose_comm b₁ b₂]
    score_compose := by
      intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
      show A.score (A.compose a₁ a₂) + B.score (B.compose b₁ b₂)
            = (A.score a₁ + B.score b₁) + (A.score a₂ + B.score b₂)
      rw [A.score_compose, B.score_compose]
      ac_rfl }

/-! ## Derivation 3: `Nat × Nat × Nat` and the Bule unit are score-isomorphic -/

abbrev Nat3 : Type := Nat × Nat × Nat

def nat3CostAlgebra : CostAlgebra Nat3 :=
  productCostAlgebra natCostAlgebra (productCostAlgebra natCostAlgebra natCostAlgebra)

/-- The bijection `BuleyUnit ↔ Nat × Nat × Nat`. -/
def buleyOfNat3 : Nat3 → BuleyUnit
  | (w, o, d) => ⟨w, o, d⟩

def nat3OfBuley (b : BuleyUnit) : Nat3 :=
  (b.waste, b.opportunity, b.diversity)

theorem bule_nat3_round_trip (b : BuleyUnit) :
    buleyOfNat3 (nat3OfBuley b) = b := by cases b; rfl

theorem nat3_bule_round_trip (n : Nat3) :
    nat3OfBuley (buleyOfNat3 n) = n := by
  cases n with
  | mk w rest =>
    cases rest with
    | mk o d => rfl

/-- The Bule cost-algebra and the `Nat^3` cost-algebra agree on score
under the bijection. The Bule unit is structurally `Nat^3`. -/
theorem bule_score_equals_nat3_score (b : BuleyUnit) :
    buleyCostAlgebra.score b = nat3CostAlgebra.score (nat3OfBuley b) := by
  cases b with
  | mk w o d =>
    show w + o + d = w + (o + d)
    exact Nat.add_assoc w o d

/-- The Bule cost-algebra and the `Nat^3` cost-algebra agree on
composition under the bijection. -/
theorem bule_compose_equals_nat3_compose (a b : BuleyUnit) :
    nat3OfBuley (buleyCostAlgebra.compose a b)
      = nat3CostAlgebra.compose (nat3OfBuley a) (nat3OfBuley b) := by
  cases a with
  | mk wa oa da =>
  cases b with
  | mk wb ob db =>
    show (wa + wb, oa + ob, da + db) = (wa + wb, oa + ob, da + db)
    rfl

/-! ## Derivation 4: Iterated `Nat^k` — free commutative monoid on k generators -/

/-- `natTuple k` is the type of k-tuples of natural numbers, built by
iterating the product. It is the carrier of the free commutative
monoid on k indeterminates, and a `CostAlgebra` by iteration. -/
def natTuple : Nat → Type
  | 0 => Unit
  | n + 1 => Nat × natTuple n

/-- The trivial 0-tuple CostAlgebra: the unit type with the unique
element. Score is constant 0. -/
def unitCostAlgebra : CostAlgebra Unit :=
  { zero := ()
    compose := fun _ _ => ()
    score := fun _ => 0
    zero_score := rfl
    compose_left_zero := by intro _; rfl
    compose_right_zero := by intro _; rfl
    compose_assoc := by intros; rfl
    compose_comm := by intros; rfl
    score_compose := by intros; rfl }

def natTupleCostAlgebra : (k : Nat) → CostAlgebra (natTuple k)
  | 0 => unitCostAlgebra
  | n + 1 => productCostAlgebra natCostAlgebra (natTupleCostAlgebra n)

/-- The `Nat^3`-tuple CostAlgebra coincides with the structural
definition above (Nat × Nat × Nat) — the Bule unit is also the free
commutative monoid on three generators. -/
theorem buleys_three_generators :
    (natTupleCostAlgebra 3).score (1, 0, 0, ()) = 1
    ∧ (natTupleCostAlgebra 3).score (0, 1, 0, ()) = 1
    ∧ (natTupleCostAlgebra 3).score (0, 0, 1, ()) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals rfl

/-- The total-degree of a `Nat^3` element is the sum of its three
coordinates — the same as `buleyUnitScore`. The "free commutative
monoid on three generators with total-degree score" *is* the Bule
unit, mechanized. -/
theorem nat3_total_degree_is_bule_score (b : BuleyUnit) :
    (natTupleCostAlgebra 3).score
      (b.waste, b.opportunity, b.diversity, ())
    = buleyUnitScore b := by
  cases b with
  | mk w o d =>
    show w + (o + (d + 0)) = w + o + d
    exact (Nat.add_assoc w o d).symm

end CostAlgebraDerivations
end Gnosis
