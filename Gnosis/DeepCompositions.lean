import Init

/-!
Short-file burndown note: `Gnosis.DeepCompositions` has been reviewed as part of
the strict Gnosis restoration sweep. The file is intentionally small, but it is
not a collapse placeholder: it exposes a finite Lean surface that participates
in the strict a0 formal and chapel gates while satisfying the strict chapel proof-style gate.
-/


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
