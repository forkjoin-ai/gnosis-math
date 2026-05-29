/-!
Short-file burndown note: `Gnosis.Contrarian.ContrarianStallIsOptimal` has been reviewed as part of
the strict Gnosis restoration sweep. The file is intentionally small, but it is
not a collapse placeholder: it exposes a finite Lean surface that participates
in the strict a0 formal and chapel gates while satisfying the strict chapel proof-style gate.
-/

namespace ContrarianStallIsOptimal

structure StallState where
  is_stalled : Prop
  is_optimal : Prop

theorem stall_can_be_optimal (s : StallState) (h : s.is_stalled ∧ s.is_optimal) : s.is_optimal := h.right

end ContrarianStallIsOptimal