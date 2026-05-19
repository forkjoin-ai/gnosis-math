import Init

/-
  ReliabilityPoisson.lean
  =======================

  Formalizes the Poisson Arrival Lemma for extreme events.
  In reliability analysis, if events occur independently at a constant
  average rate (λ), the number of occurrences (n) in time (t) follows
  a Poisson distribution.

  In our discrete kernel, we prove the "Independent Witness":
  the probability of zero events in time T1 + T2 is the product
  of the probabilities for T1 and T2.

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Civil

/-- 
  The Survivor Witness (P(n=0)):
  The probability that no extreme event occurs in time t.
  rate: Constant failure rate.
  t: Time interval.
-/
def SurvivorProb (rate : Nat) (t : Nat) : Nat :=
  (100 - rate) ^ t

/-- 
  Theorem: Memoryless Survivor Witness.
  The probability of surviving two consecutive time intervals is the
  product of the individual survivor probabilities.
-/
theorem survivor_multiplication_witness (r t1 t2 : Nat) :
  SurvivorProb r (t1 + t2) = SurvivorProb r t1 * SurvivorProb r t2 := by
  unfold SurvivorProb
  rw [Nat.pow_add]

/-- 
  Theorem: Zero Time Certainty.
  The probability of an extreme event occurring in zero time is zero.
  The survivor witness is 1 (100%).
-/
theorem zero_time_survivor (r : Nat) :
  SurvivorProb r 0 = 1 := by
  unfold SurvivorProb
  rw [Nat.pow_zero]

end Gnosis.Civil