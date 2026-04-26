import Gnosis.Real

/-!
# Buleyean Arithmetic: Sovereign Lemmas

A collection of foundational arithmetic identities for the Gnosis kernel.
By centralizing these proofs, we enable Zero-Sorry sovereignty across the 
1500+ ForkRaceFold modules without relying on Mathlib's tactic-heavy machinery.
-/

namespace Gnosis.Arithmetic

-- Basic Commutativity & Associativity
theorem add_comm (a b : Nat) : a + b = b + a := Nat.add_comm a b
theorem mul_comm (a b : Nat) : Nat.mul a b = Nat.mul b a := Nat.mul_comm a b
theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := Nat.add_assoc a b c
theorem mul_assoc (a b c : Nat) : Nat.mul (Nat.mul a b) c = Nat.mul a (Nat.mul b c) := Nat.mul_assoc a b c

-- Distribution
theorem mul_add (a b c : Nat) : Nat.mul a (b + c) = Nat.mul a b + Nat.mul a c := Nat.mul_add a b c
theorem add_mul (a b c : Nat) : Nat.mul (a + b) c = Nat.mul a c + Nat.mul b c := Nat.add_mul a b c

-- Subtraction & Cancellation
theorem sub_add_cancel {a b : Nat} (h : b <= a) : a - b + b = a := Nat.sub_add_cancel h
theorem add_sub_cancel (a b : Nat) : a + b - b = a := Nat.add_sub_cancel a b
theorem mul_sub (a b c : Nat) : Nat.mul a (b - c) = Nat.mul a b - Nat.mul a c := Nat.mul_sub_left_distrib a b c

-- BuleReal specific identities (Scale: 10^9)
def one : Gnosis.BuleReal := Gnosis.BuleReal.scale
def zero : Gnosis.BuleReal := 0

theorem scale_pos : 0 < Gnosis.BuleReal.scale := by native_decide

theorem ofNat_monotone {a b : Nat} (h : a <= b) :
    Gnosis.BuleReal.ofNat a <= Gnosis.BuleReal.ofNat b := by
  exact Nat.mul_le_mul_right Gnosis.BuleReal.scale h

end Gnosis.Arithmetic
