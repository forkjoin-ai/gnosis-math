
namespace Gnosis

structure MoonshotOracleBypassAssumptions where
  oracleExecutionStalled : Prop
  bypassActive : Prop
  stallForcesBypass : oracleExecutionStalled -> bypassActive

theorem moonshot_oracle_bypass (assumptions : MoonshotOracleBypassAssumptions) :
    assumptions.oracleExecutionStalled -> assumptions.bypassActive := by
  intro hStalled
  exact assumptions.stallForcesBypass hStalled

end Gnosis