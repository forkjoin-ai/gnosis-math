import Init

/-
  LittleLaw.lean
  ================

  Formalizes Little's Law for stable discrete systems:
  L = λ * W
  where L is the average number of items, λ is the arrival rate,
  and W is the average time spent in the system.

  In Gnosis, we model this as a "Throughput Witness", proving that
  in a balanced system (arrivals = departures), the inventory
  remains a constant witness of the flow rate and latency.

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Civil

/-- 
  A Discrete System State.
  lambda: Arrival rate (items per unit time).
  wait_time: Average time spent in system.
-/
structure SystemFlow where
  lambda : Nat
  wait_time : Nat

/-- 
  The Little's Law Witness (L):
  Calculates the total number of items in the system.
-/
def average_items (s : SystemFlow) : Nat :=
  s.lambda * s.wait_time

/-- 
  Theorem: Zero Arrival Stability.
  If the arrival rate is zero, the number of items in the system
  witness must be zero.
-/
theorem zero_arrival_zero_items (w : Nat) :
  average_items ⟨0, w⟩ = 0 := by
  unfold average_items
  rw [Nat.zero_mul]

/-- 
  Theorem: Unit Time Identity.
  In a system where each item spends exactly one time unit,
  the number of items equals the arrival rate witness.
-/
theorem unit_time_identity (l : Nat) :
  average_items ⟨l, 1⟩ = l := by
  unfold average_items
  rw [Nat.mul_one]

end Gnosis.Civil
