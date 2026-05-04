
namespace Gnosis

structure OracleAcceleration where
  resonanceFactor : Nat

theorem oracle_acceleration_resonates (o : OracleAcceleration) (h : o.resonanceFactor > 5) : o.resonanceFactor > 0 :=
  Nat.lt_trans (Nat.succ_pos 4) h

end Gnosis