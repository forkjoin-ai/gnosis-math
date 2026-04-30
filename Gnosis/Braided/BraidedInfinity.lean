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

private theorem mod_add_left (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private theorem iterateSucc_succ_eq_addMod (n : Nat) :
    ∀ m i, iterateSucc n (m + 1) i = (i + 1 + m) % n := by
  intro m
  induction m with
  | zero =>
    intro i
    show (i + 1) % n = (i + 1 + 0) % n
    congr 1
  | succ k ih =>
    intro i
    show iterateSucc n (k + 1) ((i + 1) % n) = (i + 1 + (k + 1)) % n
    rw [ih ((i + 1) % n)]
    have h1 : (i + 1) % n + 1 + k = (i + 1) % n + (1 + k) := by omega
    rw [h1, mod_add_left]
    congr 1
    omega

/-- 
  The Fundamental Lemma of Braided Iteration:
  For n > 0, iterating 'n' times starting at 'i' is equivalent to (i + n) mod k.
-/
theorem iterate_succ_positive (k n i : Nat) (_hk : k > 0) (hn : n > 0) :
    iterateSucc k n i = (i + n) % k := by
  have hn_succ : n = (n - 1) + 1 := by omega
  rw [hn_succ]
  rw [iterateSucc_succ_eq_addMod k (n - 1) i]
  congr 1
  omega

/-! 
  The Braided Infinity is defined on the phase ring Fin k.
-/

theorem iterate_returns_decidable (k i : Nat) : 
    (k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 10 ∨ k = 12 ∨ k = 360) → 
    iterateSucc k k i = i % k := by
  intro hkCases
  have hkpos : k > 0 := by
    rcases hkCases with h | h | h | h | h | h <;> subst h <;> decide
  have hiter := iterate_succ_positive k k i hkpos hkpos
  rw [hiter]
  exact Nat.add_mod_right i k

end BraidedInfinity
end Gnosis
