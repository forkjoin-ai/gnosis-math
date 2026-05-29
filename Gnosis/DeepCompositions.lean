import Init

namespace Gnosis

/-!
# Deep Compositions

This file records a small Init-only composition law that can survive the Gnosis
house gate without relying on `Mathlib` or proof automation.
-/

theorem deep_compositions_add_assoc (a b c : Nat) :
    (a + b) + c = a + (b + c) := by
  exact Nat.add_assoc a b c

end Gnosis
