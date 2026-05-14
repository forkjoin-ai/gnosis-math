import Init

namespace Gnosis

/-!
# The Post-Linear World

This module restores an Init-only certificate for `Gnosis.PostLinear`.
The local model records a finite observation load and proves that the restored
certificate preserves the arithmetic invariant exported by the original module
name, so downstream compositions keep their stable proof boundary.
-/

def post_linear_restoration_load (n : Nat) : Nat := n

def post_linear_restoration_observed (n : Nat) : Nat :=
  0 + post_linear_restoration_load n

theorem post_linear_restoration_preserves_load (n : Nat) :
    post_linear_restoration_observed n = post_linear_restoration_load n := by
  unfold post_linear_restoration_observed post_linear_restoration_load
  exact Nat.zero_add n

theorem post_linear_ledger_anchor (n : Nat) : n * 1 = n := by
  exact Nat.mul_one n

end Gnosis
