import Init

/-!
# Signed Fixed-Point Scalars for Rigid-Body Dynamics

`Gnosis.BuleReal` is unsigned (`abbrev BuleReal := Nat`) with *truncated*
subtraction (`Nat.sub` saturates to 0). Rigid-body physics has quantities that
genuinely go negative — gravity, torque, velocity, centre-of-mass offsets — so
those use `Fixed`, a signed scaled integer sharing BuleReal's `10^9` scale.

Rustic Church discipline: `Init` only (no Mathlib), proofs from core `Int`
lemmas, one frozen division convention (`Int.div`, truncation toward zero) so
this Lean source and the generated Rust agree byte-for-byte.
-/

namespace Gnosis.Body.FixedPoint

/-- A signed fixed-point scalar: an `Int` interpreted as `value / scale`. -/
abbrev Fixed := Int

namespace Fixed

/-- Scaling factor: `1.0 = 10^9`, mirroring `Gnosis.BuleReal.scale`. -/
def scale : Int := 1000000000

/-- Embed an integer count of whole units. -/
def ofInt (n : Int) : Fixed := n * scale

def zero : Fixed := 0
def one : Fixed := scale

/-- Fixed-point multiply: `(a*b)/scale`. Single frozen `Int.div` convention. -/
def mul (a b : Fixed) : Fixed := (a * b) / scale

/-- Fixed-point divide: `(a*scale)/b`. -/
def div (a b : Fixed) : Fixed := (a * scale) / b

-- Addition/subtraction are exact signed `Int` ops (no truncation, unlike Nat).

theorem add_comm (a b : Fixed) : a + b = b + a := Int.add_comm a b

theorem add_assoc (a b c : Fixed) : a + b + c = a + (b + c) := Int.add_assoc a b c

theorem add_zero (a : Fixed) : a + 0 = a := Int.add_zero a

theorem zero_add (a : Fixed) : 0 + a = a := Int.zero_add a

/-- Subtraction is the exact inverse of addition (impossible for unsigned Nat). -/
theorem add_sub_cancel (a b : Fixed) : a + b - b = a := Int.add_sub_cancel a b

end Fixed

end Gnosis.Body.FixedPoint
