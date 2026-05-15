import Gnosis.MechanismDesign
import Gnosis.QueueStability
import Gnosis.UniversalIntelligenceSSM
import Gnosis.InferenceVacuumSSM
import Gnosis.Gatekeeping

/-!
# Skyrms Energy Tax

A chapel-grade mechanism for network energy redistribution.

The construction combines four existing surfaces:

* `MechanismDesign`: externality pricing and the nonzero clinamen floor.
* `VibesCoaseBargaining`: attention-vote side payments as bargaining power.
* `UniversalIntelligenceSSM`: successful routing earns energy.
* `InferenceVacuumSSM`: unresolved future debt is a pull against the network.

The first layer proves local arithmetic invariants: the tax is exactly the
marginal externality plus one, lower externality strictly lowers tax, lower tax
strictly lowers payable burden when subtraction does not saturate, and a
two-node rebate certificate conserves the taxed pool.
-/

namespace Gnosis
namespace SkyrmsEnergyTax

open Gnosis.UniversalIntelligenceSSM

/-- Per-node state for the dynamic energy market.

`attentionValue` is the attention-market signal; `routingWaste`,
`congestionLoad`, `failedAttention`, and `unresolvedDebt` are the priced
externalities. `truthScore` and `diversityContribution` feed the rebate
weight rather than the tax. -/
structure EnergyNode where
  usefulWork : Nat
  attentionValue : Nat
  routingWaste : Nat
  congestionLoad : Nat
  failedAttention : Nat
  unresolvedDebt : Nat
  truthScore : Nat
  diversityContribution : Nat
  deriving Repr, DecidableEq

/-- Gross local contribution before mechanism settlement. -/
def grossContribution (node : EnergyNode) : Nat :=
  node.usefulWork + node.attentionValue

/-- The externality a node imposes on the network energy surface. -/
def externality (node : EnergyNode) : Nat :=
  node.routingWaste + node.congestionLoad +
    node.failedAttention + node.unresolvedDebt

/-- The Skyrms tax prices marginal externality and includes the clinamen floor. -/
def skyrmsTax (node : EnergyNode) : Nat :=
  externality node + 1

/-- Rebate weight: useful work, attention value, truth, and diversity. -/
def rebateWeight (node : EnergyNode) : Nat :=
  grossContribution node + node.truthScore + node.diversityContribution

/-- Payable burden after rebate. This is the part of the tax not cleared by the
attention-market redistribution channel. -/
def payableBurden (node : EnergyNode) (rebate : Nat) : Nat :=
  skyrmsTax node - rebate

/-- Dynamic-energy objective: minimize priced externality after crediting
verified contribution. -/
def energyObjective (node : EnergyNode) (rebate : Nat) : Nat :=
  payableBurden node rebate

/-- The tax decomposes into externality plus the one-unit clinamen incentive. -/
theorem skyrms_tax_is_externality_plus_clinamen (node : EnergyNode) :
    skyrmsTax node = externality node + 1 := by
  rfl

/-- The mechanism has a nonzero participation floor. -/
theorem skyrms_tax_has_clinamen_floor (node : EnergyNode) :
    1 ≤ skyrmsTax node := by
  unfold skyrmsTax
  exact Nat.succ_le_succ (Nat.zero_le (externality node))

/-- Lower externality strictly lowers the tax. -/
theorem lower_externality_strictly_lowers_tax
    {better worse : EnergyNode}
    (h : externality better < externality worse) :
    skyrmsTax better < skyrmsTax worse := by
  unfold skyrmsTax
  exact Nat.succ_lt_succ h

/-- If the same rebate is below both taxes, lower externality strictly lowers
the payable burden. The side condition keeps natural-number subtraction from
saturating at zero. -/
theorem lower_externality_strictly_lowers_payable_burden
    {better worse : EnergyNode} {rebate : Nat}
    (hExternality : externality better < externality worse)
    (hRebate : rebate < skyrmsTax better) :
    payableBurden better rebate < payableBurden worse rebate := by
  unfold payableBurden
  have hTax : skyrmsTax better < skyrmsTax worse :=
    lower_externality_strictly_lowers_tax hExternality
  exact Nat.sub_lt_sub_right (Nat.le_of_lt hRebate) hTax

/-- Two-node certificate that the redistribution rule allocates exactly the
taxed pool. This is the smallest conservation witness for the energy market. -/
structure TwoNodeRedistribution where
  left : EnergyNode
  right : EnergyNode
  leftRebate : Nat
  rightRebate : Nat
  pool : Nat
  pool_eq_taxes : pool = skyrmsTax left + skyrmsTax right
  rebates_exhaust_pool : leftRebate + rightRebate = pool
  deriving Repr

/-- Certified rebates conserve the collected tax pool. -/
theorem two_node_redistribution_conserves_pool
    (cert : TwoNodeRedistribution) :
    cert.leftRebate + cert.rightRebate =
      skyrmsTax cert.left + skyrmsTax cert.right := by
  rw [cert.rebates_exhaust_pool, cert.pool_eq_taxes]

/-- A rebate allocation is attention-aligned when the node with at least as much
rebate weight receives at least as much rebate. -/
def AttentionAlignedRebate (cert : TwoNodeRedistribution) : Prop :=
  rebateWeight cert.right ≤ rebateWeight cert.left →
    cert.rightRebate ≤ cert.leftRebate

/-- A Skyrms energy settlement combines conservation with attention alignment. -/
structure SkyrmsEnergySettlement extends TwoNodeRedistribution where
  attention_aligned : AttentionAlignedRebate toTwoNodeRedistribution

/-- Settlement conservation projects through the stronger Skyrms certificate. -/
theorem settlement_conserves_pool (settlement : SkyrmsEnergySettlement) :
    settlement.leftRebate + settlement.rightRebate =
      skyrmsTax settlement.left + skyrmsTax settlement.right :=
  two_node_redistribution_conserves_pool settlement.toTwoNodeRedistribution

/-- Settlement alignment projects the attention-market ordering. -/
theorem settlement_respects_attention_weight
    (settlement : SkyrmsEnergySettlement)
    (h : rebateWeight settlement.right ≤ rebateWeight settlement.left) :
    settlement.rightRebate ≤ settlement.leftRebate :=
  settlement.attention_aligned h

/-! ## UniversalIntelligenceSSM bridge -/

/-- Project one SSM attention attempt into the dynamic energy market.

Successful attention converts the payload into useful work and receives a
truth-score witness. Failed attention contributes one routing-waste unit and
one failed-attention unit, while unresolved topological debt remains priced in
both cases. -/
def swarmAttemptEnergyNode
    (source target : SwarmNode) (success : Bool) (debt : Nat) : EnergyNode where
  usefulWork := safeFold success source.value
  attentionValue := semanticResonance source.query target.key
  routingWaste := if success then 0 else 1
  congestionLoad := 0
  failedAttention := if success then 0 else 1
  unresolvedDebt := debt
  truthScore := if success then 1 else 0
  diversityContribution := target.dimension

/-- Successful SSM attention has no routing-waste or failed-attention charge;
its externality is exactly the remaining topological debt. -/
theorem successful_swarm_attempt_externality_eq_debt
    (source target : SwarmNode) (debt : Nat) :
    externality (swarmAttemptEnergyNode source target true debt) = debt := by
  unfold externality swarmAttemptEnergyNode
  simp

/-- Failed SSM attention pays the same debt plus one routing-waste unit and one
failed-attention unit. -/
theorem failed_swarm_attempt_externality_eq_debt_plus_two
    (source target : SwarmNode) (debt : Nat) :
    externality (swarmAttemptEnergyNode source target false debt) = debt + 2 := by
  unfold externality swarmAttemptEnergyNode
  simp [Nat.add_comm]

/-- Successful SSM attention pays only the unresolved-debt tax plus the clinamen
floor. -/
theorem successful_swarm_attempt_tax_eq_debt_plus_one
    (source target : SwarmNode) (debt : Nat) :
    skyrmsTax (swarmAttemptEnergyNode source target true debt) = debt + 1 := by
  unfold skyrmsTax
  rw [successful_swarm_attempt_externality_eq_debt]

/-- Failed SSM attention pays debt, the two failure externalities, and the
clinamen floor. -/
theorem failed_swarm_attempt_tax_eq_debt_plus_three
    (source target : SwarmNode) (debt : Nat) :
    skyrmsTax (swarmAttemptEnergyNode source target false debt) = debt + 3 := by
  unfold skyrmsTax
  rw [failed_swarm_attempt_externality_eq_debt_plus_two]

/-- With equal debt, success is strictly cheaper than failure in the Skyrms
energy market. -/
theorem successful_swarm_attempt_strictly_lowers_tax_vs_failure
    (source target : SwarmNode) (debt : Nat) :
    skyrmsTax (swarmAttemptEnergyNode source target true debt) <
      skyrmsTax (swarmAttemptEnergyNode source target false debt) := by
  rw [successful_swarm_attempt_tax_eq_debt_plus_one,
    failed_swarm_attempt_tax_eq_debt_plus_three]
  exact Nat.add_lt_add_left (by decide : 1 < 3) debt

/-- Successful SSM attention has rebate weight equal to payload, attention,
truth, and target diversity. -/
theorem successful_swarm_attempt_rebate_weight_eq
    (source target : SwarmNode) (debt : Nat) :
    rebateWeight (swarmAttemptEnergyNode source target true debt) =
      source.value + semanticResonance source.query target.key + 1 +
        target.dimension := by
  unfold rebateWeight grossContribution swarmAttemptEnergyNode safeFold
  simp

/-- Failed SSM attention keeps attention and diversity weight, but loses useful
work and truth-score weight. -/
theorem failed_swarm_attempt_rebate_weight_eq
    (source target : SwarmNode) (debt : Nat) :
    rebateWeight (swarmAttemptEnergyNode source target false debt) =
      semanticResonance source.query target.key + target.dimension := by
  unfold rebateWeight grossContribution swarmAttemptEnergyNode safeFold
  simp

/-- With equal debt, success strictly raises rebate weight versus failure. -/
theorem successful_swarm_attempt_strictly_raises_rebate_weight_vs_failure
    (source target : SwarmNode) (debt : Nat) :
    rebateWeight (swarmAttemptEnergyNode source target false debt) <
      rebateWeight (swarmAttemptEnergyNode source target true debt) := by
  rw [successful_swarm_attempt_rebate_weight_eq,
    failed_swarm_attempt_rebate_weight_eq]
  have hBase :
      semanticResonance source.query target.key + target.dimension <
        source.value + semanticResonance source.query target.key + 1 +
          target.dimension := by
    have h1 :
        semanticResonance source.query target.key <
          source.value + semanticResonance source.query target.key + 1 := by
      exact Nat.lt_succ_of_le (Nat.le_add_left _ _)
    exact Nat.add_lt_add_right h1 target.dimension
  exact hBase

/-- The existing Hebbian success reward can cover the Skyrms tax whenever the
remaining debt plus clinamen floor is within the 10-unit reward quantum. -/
theorem successful_hebbian_reward_covers_skyrms_tax
    (source target : SwarmNode) (debt : Nat)
    (hDebt : debt + 1 ≤ 10) :
    skyrmsTax (swarmAttemptEnergyNode source target true debt) ≤
      (hebbianReward source true).energy - source.energy := by
  rw [successful_swarm_attempt_tax_eq_debt_plus_one]
  dsimp [hebbianReward]
  rw [Nat.add_sub_cancel_left]
  exact hDebt

/-! ## Finite network aggregate -/

/-- A finite dynamic-energy network is a list of settled energy nodes. -/
structure EnergyNetwork where
  nodes : List EnergyNode
  deriving Repr

/-- Total Skyrms tax over a finite network. -/
def totalSkyrmsTax (network : EnergyNetwork) : Nat :=
  (network.nodes.map skyrmsTax).foldl (· + ·) 0

/-- Total rebate weight over a finite network. -/
def totalRebateWeight (network : EnergyNetwork) : Nat :=
  (network.nodes.map rebateWeight).foldl (· + ·) 0

private theorem nat_foldl_add_shift (xs : List Nat) (s : Nat) :
    xs.foldl (· + ·) s = s + xs.foldl (· + ·) 0 := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (s + x), ih (0 + x), Nat.zero_add, Nat.add_assoc]

/-- Adding one node to the front of a finite network adds exactly that node's
tax to the network total. -/
theorem total_skyrms_tax_cons (node : EnergyNode) (rest : List EnergyNode) :
    totalSkyrmsTax { nodes := node :: rest } =
      skyrmsTax node + totalSkyrmsTax { nodes := rest } := by
  unfold totalSkyrmsTax
  simp only [List.map_cons, List.foldl_cons]
  rw [nat_foldl_add_shift]
  rw [Nat.zero_add]

/-- Adding one node to the front of a finite network adds exactly that node's
rebate weight to the network total. -/
theorem total_rebate_weight_cons (node : EnergyNode) (rest : List EnergyNode) :
    totalRebateWeight { nodes := node :: rest } =
      rebateWeight node + totalRebateWeight { nodes := rest } := by
  unfold totalRebateWeight
  simp only [List.map_cons, List.foldl_cons]
  rw [nat_foldl_add_shift]
  rw [Nat.zero_add]

/-- Replacing a failed SSM attempt with the matching successful attempt, at the
same debt and with the rest of the network fixed, strictly lowers total tax. -/
theorem replacing_failed_attempt_with_success_strictly_lowers_total_tax
    (source target : SwarmNode) (debt : Nat) (rest : List EnergyNode) :
    totalSkyrmsTax
        { nodes := swarmAttemptEnergyNode source target true debt :: rest } <
      totalSkyrmsTax
        { nodes := swarmAttemptEnergyNode source target false debt :: rest } := by
  rw [total_skyrms_tax_cons, total_skyrms_tax_cons]
  exact Nat.add_lt_add_right
    (successful_swarm_attempt_strictly_lowers_tax_vs_failure source target debt)
    (totalSkyrmsTax { nodes := rest })

/-- Replacing a failed SSM attempt with the matching successful attempt, at the
same debt and with the rest of the network fixed, strictly raises total rebate
weight. -/
theorem replacing_failed_attempt_with_success_strictly_raises_total_rebate_weight
    (source target : SwarmNode) (debt : Nat) (rest : List EnergyNode) :
    totalRebateWeight
        { nodes := swarmAttemptEnergyNode source target false debt :: rest } <
      totalRebateWeight
        { nodes := swarmAttemptEnergyNode source target true debt :: rest } := by
  rw [total_rebate_weight_cons, total_rebate_weight_cons]
  exact Nat.add_lt_add_right
    (successful_swarm_attempt_strictly_raises_rebate_weight_vs_failure source target debt)
    (totalRebateWeight { nodes := rest })

/-- A finite settlement certificate for implementation: rebates are represented
as node-index-aligned natural numbers, and the certificate records both pool
conservation and the total attention-market weight used to allocate that pool. -/
structure EnergyNetworkSettlement where
  network : EnergyNetwork
  rebates : List Nat
  rebatePool : Nat
  rebateWeightPool : Nat
  rebate_pool_eq_tax : rebatePool = totalSkyrmsTax network
  rebate_weight_pool_eq : rebateWeightPool = totalRebateWeight network
  rebates_exhaust_pool : rebates.foldl (· + ·) 0 = rebatePool
  deriving Repr

/-- A complete network settlement conserves the Skyrms tax pool. -/
theorem network_settlement_conserves_tax_pool
    (settlement : EnergyNetworkSettlement) :
    settlement.rebates.foldl (· + ·) 0 =
      totalSkyrmsTax settlement.network := by
  rw [settlement.rebates_exhaust_pool, settlement.rebate_pool_eq_tax]

/-- A complete network settlement records the rebate-weight denominator used by
the attention market. -/
theorem network_settlement_records_rebate_weight_pool
    (settlement : EnergyNetworkSettlement) :
    settlement.rebateWeightPool = totalRebateWeight settlement.network :=
  settlement.rebate_weight_pool_eq

/-! ## Integer rebate allocation rule -/

/-- Integer proportional rebate for a single node.

When the network has no rebate weight, allocation is zero. Otherwise the node
receives its floor share of the collected pool. Any residual caused by integer
division is left for a later residual-allocation rule. -/
def proportionalRebate
    (rebatePool rebateWeightPool : Nat) (node : EnergyNode) : Nat :=
  if rebateWeightPool = 0 then
    0
  else
    rebatePool * rebateWeight node / rebateWeightPool

/-- The zero-denominator case allocates no rebate. -/
theorem proportional_rebate_zero_weight_pool
    (rebatePool : Nat) (node : EnergyNode) :
    proportionalRebate rebatePool 0 node = 0 := by
  unfold proportionalRebate
  simp

/-- If a node's rebate weight is bounded by the total rebate weight, its
integer proportional allocation cannot exceed the rebate pool. -/
theorem proportional_rebate_le_pool
    (rebatePool rebateWeightPool : Nat) (node : EnergyNode)
    (hWeight : rebateWeight node ≤ rebateWeightPool) :
    proportionalRebate rebatePool rebateWeightPool node ≤ rebatePool := by
  unfold proportionalRebate
  by_cases hZero : rebateWeightPool = 0
  · simp [hZero]
  · simp [hZero]
    have hMul :
        rebatePool * rebateWeight node ≤ rebatePool * rebateWeightPool :=
      Nat.mul_le_mul_left rebatePool hWeight
    have hDiv :
        rebatePool * rebateWeight node / rebateWeightPool ≤
          rebatePool * rebateWeightPool / rebateWeightPool :=
      Nat.div_le_div_right hMul
    have hPoolPos : 0 < rebateWeightPool := Nat.pos_of_ne_zero hZero
    calc
      rebatePool * rebateWeight node / rebateWeightPool
          ≤ rebatePool * rebateWeightPool / rebateWeightPool := hDiv
      _ = rebatePool := by
        rw [Nat.mul_comm rebatePool rebateWeightPool]
        exact Nat.mul_div_right rebatePool hPoolPos

/-- Concrete proportional settlement generated from a network. This deliberately
does not claim the list exhausts the pool; floor division can leave residual.
The conservation certificate remains `EnergyNetworkSettlement`, which should be
used after residual handling. -/
def proportionalRebates (network : EnergyNetwork) : List Nat :=
  let pool := totalSkyrmsTax network
  let weightPool := totalRebateWeight network
  network.nodes.map (proportionalRebate pool weightPool)

/-! ## Gatekeeping admissibility -/

/-- Gate metrics induced by a finite energy network.

The calibration is intentionally direct:

* false rejects are represented by total priced tax burden;
* false accepts are represented by total rebate weight still available to
  misallocation analysis;
* legitimate throughput is represented by total useful contribution.

Runtime calibration can normalize these values onto the 0-100 dial used by
`Gatekeeping`; this chapel layer records the structural projection. -/
def gateMetricsOfEnergyNetwork (network : EnergyNetwork) : Gatekeeping.GateMetrics where
  falseReject := totalSkyrmsTax network
  falseAccept := totalRebateWeight network
  legitThroughput :=
    (network.nodes.map grossContribution).foldl (· + ·) 0

/-- The canonical gate used by the Skyrms energy tax: public threshold,
attention carrier, repeated interaction, asymmetric information, and an appeal
path for audited settlement traces. -/
def skyrmsEnergyGate (bottleneck : Nat) : Gatekeeping.Gate where
  carrier := Gatekeeping.GateCarrier.attention
  episteme := { repeated := true, asymmetricInfo := true }
  style := Gatekeeping.GateStyle.publishedThreshold
  strictness := bottleneck
  opacity := 0
  appealPath := true
  bottleneck := bottleneck

/-- An admissible Skyrms energy tax is an effective balanced gate over the
network metrics. This is the anti-rent wrapper around the arithmetic tax. -/
def IsAdmissibleSkyrmsEnergyTax
    (network : EnergyNetwork) (bottleneck : Nat) : Prop :=
  Gatekeeping.IsEffectiveBalanced
    (skyrmsEnergyGate bottleneck)
    (gateMetricsOfEnergyNetwork network)

/-- Admissibility projects ordinary Gatekeeping effectiveness. -/
theorem admissible_skyrms_energy_tax_is_effective
    (network : EnergyNetwork) (bottleneck : Nat)
    (h : IsAdmissibleSkyrmsEnergyTax network bottleneck) :
    Gatekeeping.IsEffective
      (skyrmsEnergyGate bottleneck)
      (gateMetricsOfEnergyNetwork network) :=
  Gatekeeping.balanced_effective_implies_effective
    (skyrmsEnergyGate bottleneck)
    (gateMetricsOfEnergyNetwork network)
    h

/-- The canonical Skyrms energy gate is not hidden-criteria gatekeeping. -/
theorem skyrms_energy_gate_is_published_threshold (bottleneck : Nat) :
    (skyrmsEnergyGate bottleneck).style =
      Gatekeeping.GateStyle.publishedThreshold := by
  rfl

/-- The canonical Skyrms energy gate has an appeal path: implementations should
expose settlement traces as the recourse channel. -/
theorem skyrms_energy_gate_has_appeal_path (bottleneck : Nat) :
    (skyrmsEnergyGate bottleneck).appealPath = true := by
  rfl

/-- Under the Gatekeeping admissibility wrapper, the tax burden is bounded by
the effective false-reject cap. This is the formal anti-overblocking guard. -/
theorem admissible_tax_burden_bounded_by_gate_false_reject_cap
    (network : EnergyNetwork) (bottleneck : Nat)
    (h : IsAdmissibleSkyrmsEnergyTax network bottleneck) :
    totalSkyrmsTax network ≤ Gatekeeping.maxFalseRejectEffective := by
  exact Gatekeeping.effective_implies_false_reject_cap
    (skyrmsEnergyGate bottleneck)
    (gateMetricsOfEnergyNetwork network)
    (admissible_skyrms_energy_tax_is_effective network bottleneck h)

/-! ## Minimal complete gate theorem -/

/-- A candidate tax is complete when it prices every declared externality face
and preserves the nonzero clinamen floor in one additive bound.

This avoids pretending optimality is absolute: the theorem is relative to the
declared externality basis and the mandatory one-unit participation floor. -/
def IsCompleteEnergyTax (candidateTax : EnergyNode → Nat) : Prop :=
  ∀ node : EnergyNode,
    node.routingWaste + node.congestionLoad +
      node.failedAttention + node.unresolvedDebt + 1 ≤ candidateTax node

/-- The Skyrms tax itself is complete for the declared externality basis. -/
theorem skyrms_tax_is_complete_energy_tax :
    IsCompleteEnergyTax skyrmsTax := by
  intro node
  unfold skyrmsTax externality
  exact Nat.le_refl _

/-- Any complete candidate tax pointwise dominates the Skyrms tax. -/
theorem complete_energy_tax_dominates_skyrms_tax
    (candidateTax : EnergyNode → Nat)
    (hComplete : IsCompleteEnergyTax candidateTax)
    (node : EnergyNode) :
    skyrmsTax node ≤ candidateTax node := by
  unfold IsCompleteEnergyTax at hComplete
  unfold skyrmsTax externality
  exact hComplete node

/-- Minimal-complete optimality: `externality + 1` is the least pointwise tax
among all complete taxes over the declared externality basis. -/
theorem skyrms_tax_is_minimal_complete_gate
    (candidateTax : EnergyNode → Nat)
    (hComplete : IsCompleteEnergyTax candidateTax) :
    ∀ node : EnergyNode, skyrmsTax node ≤ candidateTax node :=
  complete_energy_tax_dominates_skyrms_tax candidateTax hComplete

/-- No strictly lower candidate can be complete at a node. -/
theorem lower_than_skyrms_tax_is_incomplete_at_node
    (candidateTax : EnergyNode → Nat) (node : EnergyNode)
    (hLower : candidateTax node < skyrmsTax node) :
    ¬ IsCompleteEnergyTax candidateTax := by
  intro hComplete
  have hDominates := complete_energy_tax_dominates_skyrms_tax
    candidateTax hComplete node
  exact Nat.not_lt_of_ge hDominates hLower

/-- A candidate tax is an optimal admissible gate for a concrete network when
it is complete over the declared externality basis and the Skyrms energy gate is
Gatekeeping-admissible for that network's measured bottleneck. -/
def IsOptimalAdmissibleEnergyGate
    (network : EnergyNetwork) (bottleneck : Nat)
    (candidateTax : EnergyNode → Nat) : Prop :=
  IsCompleteEnergyTax candidateTax ∧
  IsAdmissibleSkyrmsEnergyTax network bottleneck

/-- Optimal admissible gates inherit the Gatekeeping anti-rent guard. -/
theorem optimal_admissible_energy_gate_is_gatekeeping_effective
    (network : EnergyNetwork) (bottleneck : Nat)
    (candidateTax : EnergyNode → Nat)
    (h : IsOptimalAdmissibleEnergyGate network bottleneck candidateTax) :
    Gatekeeping.IsEffective
      (skyrmsEnergyGate bottleneck)
      (gateMetricsOfEnergyNetwork network) :=
  admissible_skyrms_energy_tax_is_effective network bottleneck h.right

/-- Optimal admissible gates pointwise dominate the minimal Skyrms tax. -/
theorem optimal_admissible_energy_gate_dominates_skyrms_tax
    (network : EnergyNetwork) (bottleneck : Nat)
    (candidateTax : EnergyNode → Nat)
    (h : IsOptimalAdmissibleEnergyGate network bottleneck candidateTax) :
    ∀ node : EnergyNode, skyrmsTax node ≤ candidateTax node :=
  skyrms_tax_is_minimal_complete_gate candidateTax h.left

/-- Final combined statement: an optimal admissible energy gate is both
Gatekeeping-effective (anti-rent guarded) and bounded below by the minimal
complete Skyrms tax. -/
theorem optimal_admissible_energy_gate_statement
    (network : EnergyNetwork) (bottleneck : Nat)
    (candidateTax : EnergyNode → Nat)
    (h : IsOptimalAdmissibleEnergyGate network bottleneck candidateTax) :
    Gatekeeping.IsEffective
        (skyrmsEnergyGate bottleneck)
        (gateMetricsOfEnergyNetwork network) ∧
      (∀ node : EnergyNode, skyrmsTax node ≤ candidateTax node) :=
  ⟨optimal_admissible_energy_gate_is_gatekeeping_effective
      network bottleneck candidateTax h,
    optimal_admissible_energy_gate_dominates_skyrms_tax
      network bottleneck candidateTax h⟩

end SkyrmsEnergyTax
end Gnosis
