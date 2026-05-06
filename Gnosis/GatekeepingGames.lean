/-
  GatekeepingGames.lean
  =====================

  Embeds gatekeeping in the existing God-formula / Nash game layer and ties it to
  the Skyrms convention layer.

  Nash (individual): each side chooses `allow` (cooperate / soften) or `refuse`
  (defect / strict). Debts `v` match the numeric witnesses in `NashEquilibrium.prisoners_dilemma`.

  Skyrms (collective): the same pair maps to a `Gatekeeping.StagHuntConvention`
  adoption rate, hence to `GateMetrics` via `metricsFromStagConvention`. Gate
  effectiveness is a *Skyrms-level* judgment on `(Gate, GateMetrics)` — it is not
  determined by Nash debts alone.

  Nash → Skyrms “issue” (stated honestly): mutual `refuse` is a stable Nash
  profile (Pareto-dominated), while mutual `allow` is payoff-better but not a Nash
  equilibrium in this PD-shaped toy; moving the *convention* toward `allow`
  requires coordinated / Skyrms-scale dynamics. Effective gatekeeping (high
  verified bottleneck + good metrics) witnesses one coordinated outcome; rent-shaped
  ineffective usage witnesses another at the same Nash lock.

  Imports `Gnosis.NashEquilibrium`, `Gnosis.Gatekeeping`, `Gnosis.NashSkyrmsBuleyGodLadder`,
  `Gnosis.GameTheoreticProtocolDeficit`. Zero `sorry`, zero new `axiom`.
-/

import Gnosis.NashEquilibrium
import Gnosis.Gatekeeping
import Gnosis.NashSkyrmsBuleyGodLadder
import Gnosis.GameTheoreticProtocolDeficit

namespace GatekeepingGames

open Gnosis (game_theoretic_protocol_isomorphism godWeight protocolDeficit priceOfAnarchyNash)
open Gnosis.NashSkyrmsBuleyGodLadder (nashLevel skyrmsLevel)
open NashEquilibrium
open Gatekeeping

/-! ## Individual strategies (Nash layer) -/

/-- `allow` = cooperate / soften gate; `refuse` = defect / strict gate. -/
inductive IndividualGate : Type where
  | allow
  | refuse
  deriving DecidableEq, Repr

/-! ## God-formula strategy profiles (numeric PD witnesses) -/

/-- Mutual allow: Pareto-good debts from `prisoners_dilemma` (v = 2). -/
def profileAdmitAdmit : NashEquilibrium.StrategyProfile where
  budget := 10
  agentAdebt := 2
  agentBdebt := 2
  boundA := by decide
  boundB := by decide

/-- Mutual refuse: Nash debts from `prisoners_dilemma` (v = 8). -/
def profileRefuseRefuse : NashEquilibrium.StrategyProfile where
  budget := 10
  agentAdebt := 8
  agentBdebt := 8
  boundA := by decide
  boundB := by decide

/-- A cooperates, B defects: sucker / temptation shape (vA = 10, vB = 6). -/
def profileAdmitRefuse : NashEquilibrium.StrategyProfile where
  budget := 10
  agentAdebt := 10
  agentBdebt := 6
  boundA := by decide
  boundB := by decide

def profileRefuseAdmit : NashEquilibrium.StrategyProfile where
  budget := 10
  agentAdebt := 6
  agentBdebt := 10
  boundA := by decide
  boundB := by decide

def profileOfPair (a b : IndividualGate) : NashEquilibrium.StrategyProfile :=
  match a, b with
  | .allow, .allow => profileAdmitAdmit
  | .refuse, .refuse => profileRefuseRefuse
  | .allow, .refuse => profileAdmitRefuse
  | .refuse, .allow => profileRefuseAdmit

/-! ## Payoff witnesses (unpack God weights at the PD numerals) -/

theorem payoff_mutual_allow : payoffA profileAdmitAdmit = 9 ∧ payoffB profileAdmitAdmit = 9 := by
  refine ⟨?_, ?_⟩
  · unfold payoffA profileAdmitAdmit godWeight; native_decide
  · unfold payoffB profileAdmitAdmit godWeight; native_decide

theorem payoff_mutual_refuse : payoffA profileRefuseRefuse = 3 ∧ payoffB profileRefuseRefuse = 3 := by
  refine ⟨?_, ?_⟩
  · unfold payoffA profileRefuseRefuse godWeight; native_decide
  · unfold payoffB profileRefuseRefuse godWeight; native_decide

theorem pareto_gap_allow_over_refuse :
    payoffA profileAdmitAdmit > payoffA profileRefuseRefuse ∧
      payoffB profileAdmitAdmit > payoffB profileRefuseRefuse := by
  simp only [payoffA, payoffB, profileAdmitAdmit, profileRefuseRefuse, godWeight]
  constructor <;> native_decide

/-- Unilateral allow while the other refuses strictly lowers the allowing side’s payoff
    versus mutual refuse (the PD sucker line in `prisoners_dilemma`). -/
theorem unilateral_allow_hurts_against_refuse :
    payoffA profileAdmitRefuse < payoffA profileRefuseRefuse := by
  unfold payoffA profileAdmitRefuse profileRefuseRefuse godWeight
  native_decide

theorem prisoners_dilemma_restates_unilateral_penalty :
    godWeight 10 10 < godWeight 10 8 ∧ godWeight 10 8 < godWeight 10 2 := by
  constructor <;> unfold godWeight <;> native_decide

/-! ## Skyrms convention dial from the same pair -/

/-- High adoption only on mutual allow; hare-lock floor on mutual refuse. -/
def stagAdoptionOfPair (a b : IndividualGate) : Nat :=
  match a, b with
  | .allow, .allow => 95
  | .refuse, .refuse => 22
  | _, _ => 48

def conventionOfPair (a b : IndividualGate) : StagHuntConvention :=
  ⟨stagAdoptionOfPair a b⟩

def metricsOfAdmissionPair (a b : IndividualGate) : GateMetrics :=
  metricsFromStagConvention (conventionOfPair a b)

/-! ## Gates: “no audited bottleneck” vs coordinated safety capacity -/

def gateNashLockNoAudit : Gate where
  carrier := GateCarrier.risk
  episteme := { repeated := true, asymmetricInfo := true }
  style := GateStyle.costlySignal
  strictness := 70
  opacity := 30
  appealPath := true
  bottleneck := 0

def gateSkyrmsCoordinatedSafety : Gate where
  carrier := GateCarrier.risk
  episteme := { repeated := true, asymmetricInfo := true }
  style := GateStyle.publishedThreshold
  strictness := 60
  opacity := 12
  appealPath := true
  bottleneck := 75

/-! ## Nash → Skyrms ladder witness (numeric ordering) -/

theorem nash_level_strictly_below_skyrms_level : nashLevel < skyrmsLevel := by
  decide

/-! ## Gate effectiveness tracks Skyrms metrics, not Nash debts alone -/

theorem mutual_refuse_metrics_rent_ineffective :
    IsIneffectiveUsage gateNashLockNoAudit (metricsOfAdmissionPair .refuse .refuse) := by
  left
  refine ⟨rfl, ?_, ?_⟩
  · decide
  · decide

theorem mutual_allow_metrics_balanced_effective :
    IsEffectiveBalanced gateSkyrmsCoordinatedSafety (metricsOfAdmissionPair .allow .allow) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · right; decide
    · constructor
      · decide
      · intro; decide
  · decide
  · decide

/-- Same Nash-layer `refuse/refuse` debts as the PD Nash equilibrium profile. -/
theorem refuse_refuse_profile_matches_pd_nash_debts :
    (profileOfPair .refuse .refuse).agentAdebt = 8 ∧
      (profileOfPair .refuse .refuse).agentBdebt = 8 ∧
      (profileOfPair .refuse .refuse).budget = 10 := by
  native_decide

theorem mutual_refuse_payoff_eq_prisoners_nash : payoffA profileRefuseRefuse = 3 := by
  exact payoff_mutual_refuse.1

/-! ## Protocol / PoA hook (same numerals as `game_theoretic_protocol_isomorphism`) -/

theorem gate_metrics_protocol_deficit_is_price_of_anarchy_named (a b : IndividualGate)
    (hle : (metricsOfAdmissionPair a b).legitThroughput ≤ nominalLegitDemand) :
    protocolDeficit nominalLegitDemand (metricsOfAdmissionPair a b).legitThroughput =
      priceOfAnarchyNash nominalLegitDemand (metricsOfAdmissionPair a b).legitThroughput :=
  game_theoretic_protocol_isomorphism nominalLegitDemand (metricsOfAdmissionPair a b).legitThroughput
    nominalLegitDemand (metricsOfAdmissionPair a b).legitThroughput rfl rfl hle

end GatekeepingGames
