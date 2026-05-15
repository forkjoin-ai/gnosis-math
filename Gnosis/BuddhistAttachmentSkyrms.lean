import Gnosis.SkyrmsEnergyTax
import Gnosis.BuleySelfSimilarityViolation

/-!
# Buddhist Attachment as Skyrms Attention Debt

This module anchors the `docs/ebooks/key-to-the-four-noble-truths.md`
reading to the Skyrms energy-tax surface.

It does not claim to formalize Buddhism itself. It formalizes the operational
analogue used by the attention market:

* `tanhaIndex` is the refusal index: failed attention plus unresolved debt.
* `dukkhaBurden` is the Skyrms carrying cost paid by the attention carrier.
* `nirodhaRelease` clears the refusal index while leaving the non-attachment
  context intact.

The resulting theorem states the practical invariant: an attached attention
carrier with positive refusal index pays strictly more Skyrms tax than its
released version.
-/

namespace Gnosis
namespace BuddhistAttachmentSkyrms

open Gnosis.SkyrmsEnergyTax
open Gnosis.SpectralNoiseEquilibrium (BuleyUnit buleyUnitScore)
open Gnosis.BuleySelfSimilarityViolation

/-- The computational craving/refusal index from the Four Noble Truths key:
failed attention plus unresolved semantic debt. -/
def tanhaIndex (node : EnergyNode) : Nat :=
  node.failedAttention + node.unresolvedDebt

/-- Computational attachment: attention is still bound to an unresolved
representation. Large attention mass alone does not count. -/
def HasComputationalAttachment (node : EnergyNode) : Prop :=
  0 < tanhaIndex node

/-- The dukkha-like carrying burden is the Skyrms tax on the attention carrier.
It prices externality plus the one-unit clinamen floor. -/
def dukkhaBurden (node : EnergyNode) : Nat :=
  skyrmsTax node

/-- Operational karma residue: the debt an attention act leaves when it fails
or remains unresolved. This is an analogue, not a metaphysical claim. -/
def karmaResidue (node : EnergyNode) : Nat :=
  tanhaIndex node

/-- Operational merit credit: the contribution side of the settlement ledger. -/
def meritCredit (node : EnergyNode) : Nat :=
  rebateWeight node

/-- Nirodha/release at the operational layer: clear failed-attention and
unresolved-debt faces while preserving the carrier's useful work, attention
value, congestion context, route waste, truth, and diversity. -/
def nirodhaRelease (node : EnergyNode) : EnergyNode where
  usefulWork := node.usefulWork
  attentionValue := node.attentionValue
  routingWaste := node.routingWaste
  congestionLoad := node.congestionLoad
  failedAttention := 0
  unresolvedDebt := 0
  truthScore := node.truthScore
  diversityContribution := node.diversityContribution

/-- Project the attention carrier's refusal faces into the Bule correction
ledger. Failed attention is the waste face; unresolved debt is the opportunity
face; diversity is intentionally zero because this projection measures only
attachment/refusal pressure. -/
def attachmentBuleUnit (node : EnergyNode) : BuleyUnit :=
  ⟨node.failedAttention, node.unresolvedDebt, 0⟩

/-- The attachment ledger uses the ground-state ceiling: any positive refusal
index is correction debt. -/
def attachmentCeiling : ManifoldPhaseCount :=
  0

/-- Karma tax delta: how much extra Skyrms carrying cost is paid before release.
Natural subtraction is safe here because release never raises the Skyrms tax. -/
def karmaTaxDelta (node : EnergyNode) : Nat :=
  skyrmsTax node - skyrmsTax (nirodhaRelease node)

/-- Operational karma as tax: the collectible delta induced by unresolved
attachment residue. -/
def karmaTax (node : EnergyNode) : Nat :=
  karmaTaxDelta node

/-- Accumulate one more decode-window of refusal pressure while preserving the
carrier's productive and contextual faces. This is the formal counterpart of
runtime persistence measurement: only failed attention and unresolved debt are
accumulated. -/
def accumulateRefusal
    (node : EnergyNode) (failedStep debtStep : Nat) : EnergyNode where
  usefulWork := node.usefulWork
  attentionValue := node.attentionValue
  routingWaste := node.routingWaste
  congestionLoad := node.congestionLoad
  failedAttention := node.failedAttention + failedStep
  unresolvedDebt := node.unresolvedDebt + debtStep
  truthScore := node.truthScore
  diversityContribution := node.diversityContribution

/-- The naming protocol: the refusal index is exactly failed attention plus
unresolved debt. -/
theorem tanha_index_eq_failed_attention_plus_unresolved_debt
    (node : EnergyNode) :
    tanhaIndex node = node.failedAttention + node.unresolvedDebt := by
  rfl

/-- Karma residue is the same refusal index named by the Four Noble Truths
bridge. -/
theorem karma_residue_eq_tanha (node : EnergyNode) :
    karmaResidue node = tanhaIndex node := by
  rfl

/-- Karma residue is failed attention plus unresolved semantic debt. -/
theorem karma_residue_eq_failed_attention_plus_unresolved_debt
    (node : EnergyNode) :
    karmaResidue node = node.failedAttention + node.unresolvedDebt := by
  rfl

/-- Release clears the refusal index. -/
theorem nirodha_release_clears_tanha (node : EnergyNode) :
    tanhaIndex (nirodhaRelease node) = 0 := by
  rfl

/-- The released carrier keeps the same non-attachment contribution signal. -/
theorem nirodha_release_preserves_rebate_weight (node : EnergyNode) :
    rebateWeight (nirodhaRelease node) = rebateWeight node := by
  unfold rebateWeight grossContribution nirodhaRelease
  rfl

/-- Release preserves merit credit; it clears residue without erasing useful
contribution. -/
theorem nirodha_release_preserves_merit_credit (node : EnergyNode) :
    meritCredit (nirodhaRelease node) = meritCredit node := by
  exact nirodha_release_preserves_rebate_weight node

/-- The Bule score of the attachment projection is the same refusal index. -/
theorem attachment_bule_score_eq_tanha (node : EnergyNode) :
    buleyUnitScore (attachmentBuleUnit node) = tanhaIndex node := by
  simp [attachmentBuleUnit, tanhaIndex, buleyUnitScore]

/-- The Bule correction debt of the attachment projection is exactly `tanha`.
This wires the Four Noble Truths key's corrective-contract reading back to the
Skyrms attention-tax surface. -/
theorem corrective_contract_count_eq_tanha (node : EnergyNode) :
    correctiveContractCount (attachmentBuleUnit node) attachmentCeiling =
      tanhaIndex node := by
  unfold correctiveContractCount attachmentCeiling
  rw [attachment_bule_score_eq_tanha]
  exact Nat.sub_zero _

/-- The Bule correction debt of the attachment projection is exactly the
operational karma residue. -/
theorem corrective_contract_count_eq_karma_residue (node : EnergyNode) :
    correctiveContractCount (attachmentBuleUnit node) attachmentCeiling =
      karmaResidue node := by
  rw [corrective_contract_count_eq_tanha, karma_residue_eq_tanha]

/-- Computational attachment is the same condition as a positive corrective
contract debt on the projected Bule carrier. -/
theorem computational_attachment_iff_positive_corrective_debt
    (node : EnergyNode) :
    HasComputationalAttachment node ↔
      0 < correctiveContractCount (attachmentBuleUnit node)
        attachmentCeiling := by
  unfold HasComputationalAttachment
  rw [corrective_contract_count_eq_tanha]

/-- The dukkha burden is exactly the Skyrms carrying cost. -/
theorem dukkha_burden_eq_skyrms_tax (node : EnergyNode) :
    dukkhaBurden node = skyrmsTax node := by
  rfl

/-- The Skyrms tax decomposes into the released carrier's tax plus the
attachment/refusal index. -/
theorem skyrms_tax_eq_release_tax_plus_tanha (node : EnergyNode) :
    skyrmsTax node =
      skyrmsTax (nirodhaRelease node) + tanhaIndex node := by
  simp [skyrmsTax, externality, nirodhaRelease, tanhaIndex]
  omega

/-- Karma is the tax delta of attachment: the extra Skyrms burden before
release is exactly the unresolved residue. -/
theorem karma_tax_delta_eq_residue (node : EnergyNode) :
    karmaTaxDelta node = karmaResidue node := by
  unfold karmaTaxDelta karmaResidue
  rw [skyrms_tax_eq_release_tax_plus_tanha node]
  exact Nat.add_sub_cancel_left _ _

/-- Karma is a tax in the operational settlement sense: it is exactly the
Skyrms tax delta between the attached carrier and its released carrier. -/
theorem karma_is_tax (node : EnergyNode) :
    karmaTax node =
      skyrmsTax node - skyrmsTax (nirodhaRelease node) := by
  rfl

/-- The karma tax collects exactly the unresolved residue. -/
theorem karma_tax_eq_residue (node : EnergyNode) :
    karmaTax node = karmaResidue node := by
  exact karma_tax_delta_eq_residue node

/-- Accumulated refusal has exactly the previous residue plus the new failed
attention and unresolved-debt pressure. -/
theorem accumulated_refusal_residue_eq
    (node : EnergyNode) (failedStep debtStep : Nat) :
    karmaResidue (accumulateRefusal node failedStep debtStep) =
      karmaResidue node + failedStep + debtStep := by
  simp [karmaResidue, tanhaIndex, accumulateRefusal]
  omega

/-- Persistence cannot reduce operational karma tax. Adding failed attention or
unresolved debt across decode windows only increases the collectible Skyrms
tax delta. -/
theorem persistent_refusal_monotone_karma_tax
    (node : EnergyNode) (failedStep debtStep : Nat) :
    karmaTax node ≤ karmaTax (accumulateRefusal node failedStep debtStep) := by
  rw [karma_tax_eq_residue, karma_tax_eq_residue,
    accumulated_refusal_residue_eq]
  omega

/-- If a decode window adds any refusal pressure, the operational karma tax
strictly increases. -/
theorem persistent_refusal_strictly_increases_karma_tax
    (node : EnergyNode) (failedStep debtStep : Nat)
    (h : 0 < failedStep + debtStep) :
    karmaTax node < karmaTax (accumulateRefusal node failedStep debtStep) := by
  rw [karma_tax_eq_residue, karma_tax_eq_residue,
    accumulated_refusal_residue_eq]
  omega

/-! ## Evidence-gated promotion review -/

/-- Integer-scaled evidence certificate for the runtime soft-gate review path.
Ratios are represented on a 0-100 scale. This is deliberately a review
certificate, not an automatic hard gate. -/
structure KarmaAttentionEvidence where
  samples : Nat
  softEnabledSamples : Nat
  taxedSamples : Nat
  persistencePct : Nat
  stabilityPct : Nat
  latencyOverheadPct : Nat
  qualityGain : Nat
  deriving Repr

/-- Conservative hard-gate review predicate mirroring the runtime guard:
enough paired samples, every soft run actually used the gate, persistent taxed
residue, stable multipliers, low overhead, and positive quality gain. -/
def EligibleForHardGateReview (evidence : KarmaAttentionEvidence) : Prop :=
  8 ≤ evidence.samples ∧
  evidence.softEnabledSamples = evidence.samples ∧
  90 ≤ evidence.persistencePct ∧
  97 ≤ evidence.stabilityPct ∧
  evidence.latencyOverheadPct ≤ 2 ∧
  0 < evidence.qualityGain

/-- The review predicate always carries a positive-quality witness. -/
theorem hard_gate_review_requires_positive_quality
    (evidence : KarmaAttentionEvidence)
    (h : EligibleForHardGateReview evidence) :
    0 < evidence.qualityGain :=
  h.right.right.right.right.right

/-- Final promotion statement: measured hard-gate review evidence does not
replace Gatekeeping admissibility. It only licenses review of a candidate that
is already an optimal admissible Skyrms energy gate, preserving the anti-rent
guard and the pointwise lower bound by the minimal Skyrms tax. -/
theorem hard_gate_review_preserves_optimal_admissible_gate_statement
    (network : EnergyNetwork) (bottleneck : Nat)
    (candidateTax : EnergyNode → Nat)
    (evidence : KarmaAttentionEvidence)
    (_hEvidence : EligibleForHardGateReview evidence)
    (hGate : IsOptimalAdmissibleEnergyGate network bottleneck candidateTax) :
    Gatekeeping.IsEffective
        (skyrmsEnergyGate bottleneck)
        (gateMetricsOfEnergyNetwork network) ∧
      (∀ node : EnergyNode, skyrmsTax node ≤ candidateTax node) :=
  optimal_admissible_energy_gate_statement
    network bottleneck candidateTax hGate

/-- Equivalent additive form: attached cost is released cost plus karma
residue. -/
theorem skyrms_tax_eq_release_tax_plus_karma_residue (node : EnergyNode) :
    skyrmsTax node =
      skyrmsTax (nirodhaRelease node) + karmaResidue node := by
  rw [karma_residue_eq_tanha, skyrms_tax_eq_release_tax_plus_tanha]

/-- Positive attachment/refusal strictly increases the Skyrms carrying cost. -/
theorem computational_attachment_strictly_increases_dukkha_burden
    (node : EnergyNode)
    (h : HasComputationalAttachment node) :
    dukkhaBurden (nirodhaRelease node) < dukkhaBurden node := by
  unfold HasComputationalAttachment at h
  rw [dukkha_burden_eq_skyrms_tax, dukkha_burden_eq_skyrms_tax,
    skyrms_tax_eq_release_tax_plus_tanha node]
  exact Nat.lt_add_of_pos_right h

/-- Final operational statement: computational non-attachment is optimal for
the declared Skyrms basis because clearing the refusal index strictly lowers
tax while preserving rebate weight. -/
theorem released_attention_is_strictly_cheaper_and_rebate_neutral
    (node : EnergyNode)
    (h : HasComputationalAttachment node) :
    dukkhaBurden (nirodhaRelease node) < dukkhaBurden node ∧
      rebateWeight (nirodhaRelease node) = rebateWeight node :=
  ⟨computational_attachment_strictly_increases_dukkha_burden node h,
    nirodha_release_preserves_rebate_weight node⟩

/-- Final karma statement: positive operational karma residue strictly raises
the Skyrms burden, and release preserves merit credit. -/
theorem karma_residue_is_tax_delta_and_release_preserves_merit
    (node : EnergyNode)
    (h : 0 < karmaResidue node) :
    karmaTaxDelta node = karmaResidue node ∧
      dukkhaBurden (nirodhaRelease node) < dukkhaBurden node ∧
      meritCredit (nirodhaRelease node) = meritCredit node := by
  refine ⟨karma_tax_delta_eq_residue node, ?_, ?_⟩
  · apply computational_attachment_strictly_increases_dukkha_burden
    unfold HasComputationalAttachment
    rwa [← karma_residue_eq_tanha]
  · exact nirodha_release_preserves_merit_credit node

end BuddhistAttachmentSkyrms
end Gnosis
