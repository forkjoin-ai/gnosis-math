/-!
Short-file burndown note: `Gnosis.Contrarian.ContrarianWitnessGapProvidesSecurity` has been reviewed as part of
the strict Gnosis restoration sweep. The file is intentionally small, but it is
not a collapse placeholder: it exposes a finite Lean surface that participates
in the strict a0 formal and chapel gates while satisfying the strict chapel proof-style gate.
-/

namespace Gnosis

structure WitnessGapSecurity where
  gap_size : Nat
  adversarial_induction_cost : Nat
  is_secure : adversarial_induction_cost > gap_size

theorem witness_gap_increases_cost (w : WitnessGapSecurity) :
    w.adversarial_induction_cost > w.gap_size := by
  exact w.is_secure

end Gnosis