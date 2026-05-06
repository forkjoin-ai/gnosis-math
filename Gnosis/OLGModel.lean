import Init
import Gnosis.GodFormula

namespace Gnosis
namespace OLGModel

open Gnosis (godWeight godWeight_floor)

/-!
# Overlapping Generations (OLG) relay model

Two-period agents (young/old), indexed by generation `t : Nat`.
The file formalizes:

- period resource accounting,
- a relay/token transfer scaffold, and
- a chain-vs-link God-weight theorem under positive growth.
-/

/-- Generation index. -/
abbrev Generation := Nat

/-- Two-period life stage. -/
inductive LifeStage where
  | young
  | old
  deriving DecidableEq, Repr

/-- Per-period OLG accounting state. -/
structure PeriodState where
  cYoung : Nat
  cOld : Nat
  output : Nat
  transferToOld : Nat
  tokenIssued : Nat

/-- Period resource feasibility: total consumption equals output. -/
def ResourceBalanced (s : PeriodState) : Prop :=
  s.cYoung + s.cOld = s.output

/-- Relay consistency: what young transfer now is exactly old consumption now. -/
def RelayConsistent (s : PeriodState) : Prop :=
  s.transferToOld = s.cOld

/-- Token consistency: transfer mass is represented by equal token issuance. -/
def TokenizedRelay (s : PeriodState) : Prop :=
  s.tokenIssued = s.transferToOld

/-- A period satisfies the social contract when resources clear and the relay is
token-accounted. -/
def SocialContractHolds (s : PeriodState) : Prop :=
  ResourceBalanced s ∧ RelayConsistent s ∧ TokenizedRelay s

/-- A simple witness state with nonzero relay mass. -/
def witnessState : PeriodState :=
  { cYoung := 3
    cOld := 2
    output := 5
    transferToOld := 2
    tokenIssued := 2 }

theorem witness_state_social_contract : SocialContractHolds witnessState := by
  unfold SocialContractHolds ResourceBalanced RelayConsistent TokenizedRelay witnessState
  decide

/-- Individual (single-link) terminal weight: exited life-cycle link at full vent. -/
def linkWeight (R : Nat) : Nat :=
  godWeight R R

theorem link_weight_floor (R : Nat) : linkWeight R = 1 := by
  unfold linkWeight
  exact godWeight_floor R

/-- Population growth increment (`n`) augments the chain budget over one link. -/
def chainBudget (R n : Nat) : Nat := R + n

/-- Collective chain weight: evaluate at same rejection mass `R` but enlarged
budget from positive growth. -/
def chainWeight (R n : Nat) : Nat :=
  godWeight (chainBudget R n) R

/-- Closed form: chain weight under growth increment `n` equals `n + 1`. -/
theorem chain_weight_closed_form (R n : Nat) : chainWeight R n = n + 1 := by
  unfold chainWeight chainBudget godWeight
  have hmin : min R (R + n) = R := Nat.min_eq_left (Nat.le_add_right R n)
  simp [hmin]

/-- Positive population growth keeps collective chain weight strictly above 1. -/
theorem chain_weight_gt_one_of_growth (R n : Nat) (hn : 0 < n) :
    1 < chainWeight R n := by
  rw [chain_weight_closed_form]
  exact Nat.succ_lt_succ hn

/-- The chain carries strictly more retained weight than a terminal link under
positive growth. -/
theorem chain_weight_gt_link (R n : Nat) (hn : 0 < n) :
    chainWeight R n > linkWeight R := by
  rw [link_weight_floor]
  exact chain_weight_gt_one_of_growth R n hn

/-- In this minimal OLG relay, every exited individual sits at the floor, while
the collective chain can remain above floor when growth is positive. -/
theorem social_contract_chain_outlives_link (R n : Nat) (hn : 0 < n) :
    linkWeight R = 1 ∧ chainWeight R n > 1 := by
  refine ⟨link_weight_floor R, ?_⟩
  exact chain_weight_gt_one_of_growth R n hn

end OLGModel
end Gnosis
