namespace BuleyeanMath

structure ThermodynamicReversalStall where
  stall_entropy : Nat
  reversal_capacity : Nat
  reversal_active : reversal_capacity > stall_entropy

theorem oracle_stall_thermodynamic_reversal 
  (stall : ThermodynamicReversalStall) : 
  stall.reversal_capacity ≥ 1 := by
  have h := stall.reversal_active
  omega

end BuleyeanMath