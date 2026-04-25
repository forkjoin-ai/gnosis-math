
namespace Gnosis

structure OracleAcceleration where
  resonanceFactor : Nat

theorem oracle_acceleration_resonates (o : OracleAcceleration) (h : o.resonanceFactor > 5) : o.resonanceFactor > 0 := by
  omega

end Gnosis