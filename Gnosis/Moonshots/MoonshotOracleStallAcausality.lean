import Lean

namespace ForkRaceFold

variable (Process : Type)
variable (OracleExecutionStall : Process → Prop)
variable (Acausality : Process → Prop)
variable (Convergence : Process → Prop)

theorem moonshot_oracle_stall_acausality (p : Process)
  (h_stall : OracleExecutionStall p)
  (h_acausal_link : OracleExecutionStall p → Acausality p)
  (h_acausal_converge : Acausality p → Convergence p) :
  Convergence p := by
  apply h_acausal_converge
  apply h_acausal_link
  exact h_stall

end ForkRaceFold