/-
  PredictiveSandwich.lean
  =======================

  Formalizes the "Predictive Sandwich" shape: the topological containment
  where a Gnot manifold is squeezed between Structural Necessity (Lower Bound)
  and Pleromatic Density (Upper Bound).

  The "Perfect Poem" is the unique fixed point where Friction (φ) and
  Collapse (γ) both reach zero residue.

  The former `perfect_sandwich_fixed_point` sketch carried `sorry` debt; the
  reusable algebraic step — summing clause syllables when every clause is
  exactly `3` — is proved here Init-only. A full fixed-point theorem needs the
  same friction/collapse lemmas as `GnotTopology` and is left as a thin
  corollary layer once those hooks are stable.
-/

import Gnosis.GnotTopology

namespace Gnosis
namespace PredictiveSandwich

open GnotTopology

/-- The "Lower Bread": The minimal syllables required for existence (Header + 3 parts) -/
def LowerBound (b : GnotBlock) : Nat :=
  b.kind_syllables + b.name_syllables + b.params_syllables + b.yields_syllables + (block_fold b * 3)

/-- The "Upper Bread": The Pleromatic Constant for the given folding level -/
def UpperBound (parts : Nat) : Nat :=
  match parts with
  | 3 => 17
  | 6 => 34
  | 9 => 51
  | _ => 0 -- Undefined for non-canonical folds

/-- The "Sandwich": The poem is structurally valid and density-contained -/
structure TheSandwich (b : GnotBlock) where
  parts : Nat
  h_fold : block_fold b = parts
  h_canonical : parts ∈ [3, 6, 9]
  h_lower : LowerBound b ≤ block_syllables b
  h_upper : block_syllables b ≤ UpperBound parts

private theorem foldl_clause_sum_acc (L : List GnotClause) (acc : Nat)
    (h₃ : ∀ c ∈ L, clause_syllables c = 3) :
    L.foldl (fun a c => a + clause_syllables c) acc = acc + 3 * L.length := by
  induction L generalizing acc with
  | nil =>
    simp [List.foldl, List.length, Nat.mul_zero, Nat.add_zero]
  | cons x xs ih =>
    have hx : clause_syllables x = 3 :=
      h₃ x (List.Mem.head _)
    have hrest : ∀ c ∈ xs, clause_syllables c = 3 := fun c hc =>
      h₃ c (List.Mem.tail _ hc)
    simp [List.foldl, hx]
    rw [ih (acc + 3) hrest, Nat.mul_succ 3 xs.length, Nat.add_assoc acc 3 (3 * xs.length),
      Nat.add_comm 3 (3 * xs.length)]

/-- THM-SANDWICH-BODY-SUM: If every clause has weight `3`, the folded clause
    sum is exactly `3 * length` (hence `3 * parts` when `parts = block_fold b`). -/
theorem foldl_clause_sum_eq_three_mul_length (L : List GnotClause)
    (h₃ : ∀ c ∈ L, clause_syllables c = 3) :
    L.foldl (fun acc c => acc + clause_syllables c) 0 = 3 * L.length := by
  simpa [Nat.zero_add] using foldl_clause_sum_acc L 0 h₃

/-- Corollary for a sandwiched block: body sum pins to `3 * parts`. -/
theorem sandwich_body_sum_three (b : GnotBlock) (s : TheSandwich b)
    (h₃ : ∀ c ∈ b.clauses, clause_syllables c = 3) :
    b.clauses.foldl (fun acc c => acc + clause_syllables c) 0 = 3 * s.parts := by
  have hlen : b.clauses.length = s.parts := s.h_fold
  rw [← hlen]
  exact foldl_clause_sum_eq_three_mul_length b.clauses h₃

end PredictiveSandwich
end Gnosis
