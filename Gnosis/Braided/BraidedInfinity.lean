import Init

namespace Gnosis
namespace BraidedInfinity

structure BraidedAsymptote where
  phaseCount : Nat
  descriptors : List String
deriving Repr

/-- Iterate the clinamen `n` times starting at `i`. -/
def iterateSucc (phaseCount : Nat) : Nat → Nat → Nat
  | 0,     i => i
  | n + 1, i => iterateSucc phaseCount n ((i + 1) % phaseCount)

/-- 
  The Fundamental Lemma of Braided Iteration:
  For n > 0, iterating 'n' times starting at 'i' is equivalent to (i + n) mod k.
-/
theorem iterate_succ_positive (k n i : Nat) (hk : k > 0) (hn : n > 0) :
    iterateSucc k n i = (i + n) % k := by
  sorry

/-! 
  The Braided Infinity is defined on the phase ring Fin k.
-/

theorem iterate_returns_decidable (k i : Nat) : 
    (k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 10 ∨ k = 12 ∨ k = 360) → 
    iterateSucc k k i = i % k := by
  intro _
  sorry

end BraidedInfinity
end Gnosis
