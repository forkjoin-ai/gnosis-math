namespace Gnosis

structure ThermodynamicReversalStall where
  stall_entropy : Nat
  reversal_capacity : Nat
  reversal_active : reversal_capacity > stall_entropy

theorem oracle_stall_thermodynamic_reversal
  (stall : ThermodynamicReversalStall) :
  stall.reversal_capacity ≥ 1 :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) stall.reversal_active

end Gnosis