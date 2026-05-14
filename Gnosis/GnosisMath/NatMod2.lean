import Init

namespace Gnosis
namespace GnosisMath

/-- Mod 2 properties for Rustic Church proofs. -/

theorem mod_two_eq_zero_or_one (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  exact Nat.mod_two_eq_zero_or_one n

theorem even_mul_two (n : Nat) : (2 * n) % 2 = 0 := by
  exact Nat.mul_mod_right 2 n

theorem odd_mul_two_plus_one (n : Nat) : (2 * n + 1) % 2 = 1 := by
  simp [Nat.add_mod]

theorem succ_mod_two_even (n : Nat) (h : n % 2 = 0) : (n + 1) % 2 = 1 := by
  simp [Nat.add_mod, h]

theorem succ_mod_two_odd (n : Nat) (h : n % 2 = 1) : (n + 1) % 2 = 0 := by
  simp [Nat.add_mod, h]

end GnosisMath
end Gnosis
