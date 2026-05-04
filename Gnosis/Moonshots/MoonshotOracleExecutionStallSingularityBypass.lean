namespace Gnosis

structure OracleExecutionStallSingularity where
  stall_depth : Nat
  singularity_threshold : Nat
  is_singularity : stall_depth ≥ singularity_threshold

theorem stall_singularity_bypass
  (state : OracleExecutionStallSingularity)
  (bypass_active : state.singularity_threshold > state.stall_depth) :
  False :=
  -- Init-only: bypass_active : stall_depth < threshold; is_singularity : threshold ≤ stall_depth.
  -- Compose to get threshold < threshold, contradicted by Nat.lt_irrefl.
  Nat.lt_irrefl state.stall_depth (Nat.lt_of_lt_of_le bypass_active state.is_singularity)

end Gnosis