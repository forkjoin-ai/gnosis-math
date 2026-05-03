import Gnosis.GodFormula

/-!
# Nash Equilibrium — The Stable Topological Knot

Game Theory enters the God Formula: the Nash Equilibrium is
a stable topological knot where no agent can "swerve" (deviate)
without incurring a thermodynamic penalty (increasing $v$).

Nash Equilibrium (NE): A strategy profile where no player
has an incentive to unilaterally deviate. If they do, their
payoff goes down (or stays the same).

In God Formula terms:
- R = the total payoff budget (max possible utility)
- v_i = agent i's "deviation debt" (how far they are from optimal)
- godWeight(R, v_i) = agent i's realized payoff

At Nash Equilibrium, v_i reaches a LOCAL MINIMUM with respect to
agent i's possible actions. Any deviation increases v_i (adds
debt), REDUCING godWeight(R, v_i). The NE is a topological knot
because it's a mutual local minimum in the strategy space —
tightly bound by the clinamen on all sides.

Zero -- placeholder.
-/

namespace NashEquilibrium

open Gnosis (godWeight)

/-- A Game State from Agent i's perspective. -/
structure GameState where
  budget : Nat      -- R: max possible payoff
  debt : Nat        -- v: current regret/loss from optimal
  bounded : debt ≤ budget

/-- A Strategy Profile represents the current state of the game. -/
structure StrategyProfile where
  budget : Nat
  agentAdebt : Nat
  agentBdebt : Nat
  boundA : agentAdebt ≤ budget
  boundB : agentBdebt ≤ budget

/-- Agent A's payoff. -/
def payoffA (s : StrategyProfile) : Nat := godWeight s.budget s.agentAdebt
/-- Agent B's payoff. -/
def payoffB (s : StrategyProfile) : Nat := godWeight s.budget s.agentBdebt

/-- THM-NE-is-DEVIATION-PENALTY: At Nash Equilibrium, any deviation
    by Agent A (changing their strategy unilaterally) results in
    a new state where Agent A's debt increases (or stays the same),
    thus reducing (or maintaining) their payoff. -/
theorem ne_deviation_penalty (R v_ne v_deviate : Nat)
    (hNE : v_ne ≤ R) (hDeviate : v_deviate ≤ R)
    (hPenalty : v_deviate > v_ne) : -- Deviation strictly increases debt
    godWeight R v_deviate < godWeight R v_ne := by
  have h := Gnosis.godWeight_antitone R v_ne v_deviate hNE hDeviate (Nat.le_of_lt hPenalty)
  unfold godWeight at h ⊢
  rw [Nat.min_eq_left hNE, Nat.min_eq_left hDeviate] at h ⊢
  omega

/-- THM-STABLE-KNOT: A strict Nash Equilibrium is a local maximum
    for all agents' payoffs (local minimum for their debts). It's
    topologically stable because any movement encounters the
    "walls" of increased debt. -/
theorem stable_knot (R vA_ne vB_ne vA_dev vB_dev : Nat)
    (hA : vA_ne ≤ R) (hB : vB_ne ≤ R)
    (hAd : vA_dev ≤ R) (hBd : vB_dev ≤ R)
    (hStrictA : vA_dev > vA_ne) (hStrictB : vB_dev > vB_ne) :
    godWeight R vA_dev < godWeight R vA_ne ∧
    godWeight R vB_dev < godWeight R vB_ne := by
  constructor
  · exact ne_deviation_penalty R vA_ne vA_dev hA hAd hStrictA
  · exact ne_deviation_penalty R vB_ne vB_dev hB hBd hStrictB

/-- THM-PARETO-VS-NASH: Prisoner's Dilemma. The Nash Equilibrium
    is NOT always Pareto optimal. The global budget R might be
    suboptimally utilized, but unilaterally deviating still hurts.
    The knot is stable even if it's placed poorly in the global space. -/
theorem prisoners_dilemma :
    -- Pareto optimal state (Cooperate/Cooperate): R=10, vA=2, vB=2 -> Payoff=9
    godWeight 10 2 = 9 ∧
    -- Nash Equilibrium (Defect/Defect): R=10, vA=8, vB=8 -> Payoff=3
    godWeight 10 8 = 3 ∧
    -- Deviating from NE (Cooperate when other Defects): vA=10 (Sucker) -> Payoff=1
    godWeight 10 10 = 1 ∧
    -- The NE is stable because modifying unilaterally drops payoff (3 -> 1)
    godWeight 10 10 < godWeight 10 8 ∧
    -- But the NE is Pareto inferior to Mutual Cooperation (3 < 9)
    godWeight 10 8 < godWeight 10 2 := by
  unfold godWeight
  native_decide

/-- THM-NASH-MASTER: Nash Equilibrium is formalized as the condition
    where any unilateral strategy change increases a player's
    thermodynamic debt v_i. -/
theorem nash_master (R : Nat) :
    (∀ v_ne v_dev, v_ne ≤ R → v_dev ≤ R → v_dev > v_ne →
     godWeight R v_dev < godWeight R v_ne) ∧
    (godWeight 10 10 < godWeight 10 8) ∧
    (godWeight 10 8 < godWeight 10 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro vn vd hn hd hgt; exact ne_deviation_penalty R vn vd hn hd hgt
  · unfold godWeight; native_decide
  · unfold godWeight; native_decide

end NashEquilibrium
