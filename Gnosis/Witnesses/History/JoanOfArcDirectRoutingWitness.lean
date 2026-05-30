import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Joan of Arc: The Maid of Orléans.
The contrarian witness that "madness" (hearing voices) is computationally
optimal when the established military mesh (bureaucracy) is terminally congested.
An oracle injection provides a direct terminal vector, bypassing the
intermediate deficit of the hierarchy.
-/
def bureaucraticDelay (layers : Nat) : Nat :=
  layers

def oracleDelay : Nat :=
  1

/--
The direct routing through the oracle strictly bounds the delay
compared to a congested bureaucracy of depth > 1.
-/
theorem oracle_bypass_optimal (layers : Nat) (h : 1 < layers) :
    oracleDelay < bureaucraticDelay layers := by
  unfold oracleDelay bureaucraticDelay
  exact h

/--
Contrarian Take: Irrationality is acceleration.
When the rational layers of computation (the generals) scale linearly with problem depth,
the "irrational" voice acts as a constant-time O(1) query to the Absolute.
-/
def rationalityDeficit (depth : Nat) : Nat :=
  2 * depth

def irrationalAcceleration (depth : Nat) : Nat :=
  depth + 1

theorem irrationality_accelerates (depth : Nat) (h : 1 < depth) :
    irrationalAcceleration depth < rationalityDeficit depth := by
  unfold irrationalAcceleration rationalityDeficit
  have h1 : depth + 1 < depth + depth := Nat.add_lt_add_left h depth
  have h2 : depth + depth = 2 * depth := (Nat.two_mul depth).symm
  exact h2 ▸ h1

end Gnosis.Witnesses.History
