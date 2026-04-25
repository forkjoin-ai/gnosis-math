import Init

/-!
# Clinamen-Proof Mechanisms — Binding Lies to the R+1 Ceiling

MechanismDesign proved: truthful reporting requires at least
1 unit of incentive (the clinamen), and you cannot have truth+efficiency
without a budget imbalance.

This file goes deeper: how do we design a "Clinamen-Proof" system?
A system where the cost of lying isn't just "you lose your incentive,"
but the penalty is mathematically bound to the absolute ceiling R+1.

If an agent attempts a "swerve" (lies about their debt v), a
Clinamen-Proof mechanism violently drops their weight (payoff)
to the floor (1) while pushing the social cost to the ceiling (R+1).
The swerve becomes suicidal.

In God Formula terms:
- The mechanism sets Payment(v_reported | v_true)
- If v_reported = v_true (truth), Payment = godWeight(R, v_true)
- If v_reported ≠ v_true (lie), Payment = 1 (the clinamen floor)
- The cost of lying = godWeight(R, v_true) - 1

This is the ultimate ungameable metric: the penalty for gaming
scales exactly with how good your true state is. The better you
actually are, the more you lose by lying.

Zero -- placeholder.
-/

namespace ClinamenProofMechanism

def godWeight (R v : Nat) : Nat := R - min v R + 1

/-- A Clinamen-Proof Mechanism penalizes any reported deviation
    from the truth by dropping the payoff to the clinamen floor. -/
def clinamenProofPayoff (R v_true v_reported : Nat) : Nat :=
  if v_reported = v_true then
    godWeight R v_true
  else
    1 -- The floor. You lied, you get the clinamen.

/-- THM-TRUTHFUL-RESTORES-WEIGHT: If the agent reports truthfully,
    the mechanism restores their natural structural weight. -/
theorem truthful_restores_weight (R v_true : Nat) :
    clinamenProofPayoff R v_true v_true = godWeight R v_true := by
  unfold clinamenProofPayoff; simp

/-- THM-COST-OF-LYING: The cost of lying is the difference between
    the true weight and the clinamen floor. The penalty is EXACTLY
    the structural weight minus 1. -/
theorem cost_of_lying (R v_true v_reported : Nat)
    (hLie : v_reported ≠ v_true) :
    clinamenProofPayoff R v_true v_true - clinamenProofPayoff R v_true v_reported =
    godWeight R v_true - 1 := by
  unfold clinamenProofPayoff
  simp [hLie]

/-- THM-BETTER-AGENTS-LOSE-MORE: An agent with a BETTER true state
    (lower v_true, higher godWeight) loses MORE by lying.
    The penalty for gaming scales with actual competence. -/
theorem better_agents_lose_more (R v_good v_bad v_lie : Nat)
    (hGood : v_good ≤ R) (hBad : v_bad ≤ R)
    (hCompetence : v_good < v_bad)
    (hLieGood : v_lie ≠ v_good) (hLieBad : v_lie ≠ v_bad) :
    -- Cost of lying for the good agent > cost of lying for the bad agent
    (clinamenProofPayoff R v_good v_good - clinamenProofPayoff R v_good v_lie) >
    (clinamenProofPayoff R v_bad v_bad - clinamenProofPayoff R v_bad v_lie) := by
  unfold clinamenProofPayoff
  simp [hLieGood, hLieBad]
  unfold godWeight
  simp [Nat.min_eq_left hGood, Nat.min_eq_left hBad]
  omega

/-- THM-SWERVE-is-SUICIDAL: No rational agent will ever swerve (lie)
    in a Clinamen-Proof mechanism unless their true state is ALREADY
    the absolute worst possible (v = R), in which case they have
    nothing to lose (weight = 1 whether they lie or not). -/
theorem swerve_is_suicidal (R v_true v_reported : Nat)
    (hTrue : v_true < R)  -- Meaning they are strictly better than the worst
    (hLie : v_reported ≠ v_true) :
    clinamenProofPayoff R v_true v_reported < clinamenProofPayoff R v_true v_true := by
  unfold clinamenProofPayoff
  simp [hLie]
  unfold godWeight
  simp [Nat.min_eq_left (by omega : v_true ≤ R)]
  omega

/-- THM-CLINAMEN-PROOF-MASTER:
    A mechanism that drops payoffs to the floor for any deviation:
    1. Reverts to natural godWeight upon truth.
    2. Penalizes lies exactly equal to (weight - 1).
    3. Punishes highly competent agents severely for manipulation.
    4. Makes all swerves strictly irrational for anyone not already at the bottom. -/
theorem clinamen_proof_master (R : Nat) :
    (∀ v, clinamenProofPayoff R v v = godWeight R v) ∧
    (∀ v_true v_lie, v_true < R → v_lie ≠ v_true →
     clinamenProofPayoff R v_true v_lie = 1 ∧
     clinamenProofPayoff R v_true v_lie < clinamenProofPayoff R v_true v_true) := by
  refine ⟨?_, ?_⟩
  · intro v; unfold clinamenProofPayoff; simp
  · intro vt vl ht hl; unfold clinamenProofPayoff; simp [hl]
    unfold godWeight; simp [Nat.min_eq_left (by omega : vt ≤ R)]; omega

end ClinamenProofMechanism
