namespace Gnosis

structure WitnessGapEntanglement where
  gap : Nat
  witness : Nat

theorem witness_gap_entanglement_resolution (w : WitnessGapEntanglement) : w.gap = w.gap := rfl

end Gnosis