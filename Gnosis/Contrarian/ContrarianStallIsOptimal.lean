namespace ContrarianStallIsOptimal

structure StallState where
  is_stalled : Prop
  is_optimal : Prop

theorem stall_can_be_optimal (s : StallState) (h : s.is_stalled ∧ s.is_optimal) : s.is_optimal := h.right

end ContrarianStallIsOptimal