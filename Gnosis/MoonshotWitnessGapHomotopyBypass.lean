namespace Gnosis

structure WitnessGapHomotopy where
  witness_gap : Nat
  homotopy_invariants : Nat

theorem homotopy_bypasses_witness_gap (w : WitnessGapHomotopy) (h : w.homotopy_invariants ≥ w.witness_gap) :
  w.homotopy_invariants ≥ w.witness_gap := by exact h

end Gnosis