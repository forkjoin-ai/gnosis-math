import Init

/-!
# Institutional liability: Hand test, contracts, constitutions (formal shell)

Carrier: the same discrete ledger as `LiabilityEquilibrium.LiabilityLedger` — finitely
many indices, monotone vent counts `liabilityCounts`, observation length `rounds`, and
complement weights `rounds - liability(i) + 1`.

This module is self-contained (`import Init` only) so it builds even when optional
Mathlib-dependent lemmas in sibling files are unavailable.

Interpretation tags (`ContractLedger`, `ConstitutionalLedger`) carry no extra fields;
the algebra is shared. Learned Hand is the predicate `burden < PL` on `ℕ`.
Two-ledger coupling uses `max(text, practice)` per index. Amendment is a
discrete step relating two ledgers on the same index set with monotone rounds.
-/

namespace InstitutionalLiability

/-- Finitely many institutional indices, monotone vent counts, bounded by rounds. -/
structure Ledger where
  numChoices : Nat
  nontrivial : 2 ≤ numChoices
  liabilityCounts : Fin numChoices → Nat
  rounds : Nat
  positive_rounds : 0 < rounds
  bounded : ∀ i, liabilityCounts i ≤ rounds

/-- Obligation- or clause-indexed vents. -/
structure ContractLedger where
  core : Ledger

/-- Powers, rights, procedures (same carrier). -/
structure ConstitutionalLedger where
  core : Ledger

def Ledger.weight (L : Ledger) (i : Fin L.numChoices) : Nat :=
  L.rounds - L.liabilityCounts i + 1

def ContractLedger.weight (c : ContractLedger) (i : Fin c.core.numChoices) : Nat :=
  c.core.weight i

def ConstitutionalLedger.weight (k : ConstitutionalLedger) (i : Fin k.core.numChoices) : Nat :=
  k.core.weight i

theorem ledger_weight_positive (L : Ledger) (i : Fin L.numChoices) :
    0 < L.weight i := by
  unfold Ledger.weight
  exact Nat.succ_pos _

theorem contract_weight_positive (c : ContractLedger) (i : Fin c.core.numChoices) :
    0 < c.weight i :=
  ledger_weight_positive c.core i

theorem constitutional_weight_positive (k : ConstitutionalLedger) (i : Fin k.core.numChoices) :
    0 < k.weight i :=
  ledger_weight_positive k.core i

/-- Same underlying ledger: contract vs constitutional tag does not change weights. -/
theorem weights_tag_irrelevant (L : Ledger) (i : Fin L.numChoices) :
    (ContractLedger.mk L).weight i = (ConstitutionalLedger.mk L).weight i :=
  rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- Learned Hand: B < P·L as a formal predicate on ℕ
-- ═══════════════════════════════════════════════════════════════════════════════

def handNegligent (burden PL : Nat) : Prop :=
  burden < PL

theorem hand_negligent_iff (B PL : Nat) : handNegligent B PL ↔ B < PL :=
  Iff.rfl

theorem not_hand_negligent_of_le (B PL : Nat) (h : PL ≤ B) : ¬ handNegligent B PL := by
  intro hn
  unfold handNegligent at hn
  exact Nat.lt_irrefl B (Nat.lt_of_lt_of_le hn h)

def handNegligentFactored (burden P L : Nat) : Prop :=
  handNegligent burden (P * L)

theorem hand_of_slack (burden PL k : Nat) (hk : 0 < k) (hsum : burden + k = PL) :
    handNegligent burden PL := by
  unfold handNegligent
  exact hsum ▸ Nat.lt_add_of_pos_right hk

-- ═══════════════════════════════════════════════════════════════════════════════
-- Two-ledger coupling (text vs practice)
-- ═══════════════════════════════════════════════════════════════════════════════

structure TwoLedgerCoupling where
  numChoices : Nat
  nontrivial : 2 ≤ numChoices
  rounds : Nat
  positive_rounds : 0 < rounds
  textLiability : Fin numChoices → Nat
  practiceLiability : Fin numChoices → Nat
  text_bounded : ∀ i, textLiability i ≤ rounds
  practice_bounded : ∀ i, practiceLiability i ≤ rounds

def coupledLiability (t : TwoLedgerCoupling) (i : Fin t.numChoices) : Nat :=
  max (t.textLiability i) (t.practiceLiability i)

theorem coupled_liability_bounded (t : TwoLedgerCoupling) (i : Fin t.numChoices) :
    coupledLiability t i ≤ t.rounds := by
  unfold coupledLiability
  rcases Nat.le_total (t.textLiability i) (t.practiceLiability i) with h | h
  · rw [Nat.max_eq_right h]
    exact t.practice_bounded i
  · rw [Nat.max_eq_left h]
    exact t.text_bounded i

def coupledWeight (t : TwoLedgerCoupling) (i : Fin t.numChoices) : Nat :=
  t.rounds - coupledLiability t i + 1

theorem coupled_weight_positive (t : TwoLedgerCoupling) (i : Fin t.numChoices) :
    0 < coupledWeight t i := by
  unfold coupledWeight
  exact Nat.succ_pos _

theorem coupled_coherent (t : TwoLedgerCoupling)
    (h : ∀ i, t.textLiability i = t.practiceLiability i) (i : Fin t.numChoices) :
    coupledLiability t i = t.textLiability i := by
  unfold coupledLiability
  rw [h i, Nat.max_self]

theorem coupled_weight_coherent (t : TwoLedgerCoupling)
    (h : ∀ i, t.textLiability i = t.practiceLiability i) (i : Fin t.numChoices) :
    coupledWeight t i = t.rounds - t.textLiability i + 1 := by
  unfold coupledWeight
  rw [coupled_coherent t h i]

-- ═══════════════════════════════════════════════════════════════════════════════
-- Amendment: discrete step, same index set, non-shrinking observation horizon
-- ═══════════════════════════════════════════════════════════════════════════════

structure ConstitutionalAmendment where
  beforeCore : Ledger
  afterCore : Ledger
  same_dim : beforeCore.numChoices = afterCore.numChoices
  rounds_mono : beforeCore.rounds ≤ afterCore.rounds

def amendedWeight (a : ConstitutionalAmendment) (i : Fin a.afterCore.numChoices) : Nat :=
  a.afterCore.weight i

theorem amended_weight_positive (a : ConstitutionalAmendment) (i : Fin a.afterCore.numChoices) :
    0 < amendedWeight a i :=
  ledger_weight_positive a.afterCore i

-- ═══════════════════════════════════════════════════════════════════════════════
-- Compression point (axiom-free): everything is explicit input data
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Minimal inputs needed for legal-domain reduction, with no new axioms:
    (1) a ledger state, (2) optional Hand scalars, (3) optional two-ledger channel. -/
structure CompressionInputs where
  ledger : Ledger
  handBurden : Nat
  handP : Nat
  handL : Nat
  coupling : TwoLedgerCoupling
  coupling_dim : coupling.numChoices = ledger.numChoices

/-- Contract read is just the tagged ledger weight. -/
def contractWeightFromInputs (x : CompressionInputs) (i : Fin x.ledger.numChoices) : Nat :=
  (ContractLedger.mk x.ledger).weight i

/-- Constitutional read is just the coupled weight, reindexed by `coupling_dim`. -/
def constitutionalWeightFromInputs (x : CompressionInputs) (i : Fin x.ledger.numChoices) : Nat :=
  coupledWeight x.coupling (x.coupling_dim.symm ▸ i)

/-- Tort read is just the Hand predicate on provided scalars. -/
def tortNegligentFromInputs (x : CompressionInputs) : Prop :=
  handNegligentFactored x.handBurden x.handP x.handL

theorem contract_reduction_positive (x : CompressionInputs) (i : Fin x.ledger.numChoices) :
    0 < contractWeightFromInputs x i := by
  unfold contractWeightFromInputs
  exact contract_weight_positive (ContractLedger.mk x.ledger) i

theorem constitutional_reduction_positive (x : CompressionInputs) (i : Fin x.ledger.numChoices) :
    0 < constitutionalWeightFromInputs x i := by
  unfold constitutionalWeightFromInputs
  exact coupled_weight_positive x.coupling (x.coupling_dim.symm ▸ i)

theorem tort_reduction_iff (x : CompressionInputs) :
    tortNegligentFromInputs x ↔ x.handBurden < x.handP * x.handL := by
  unfold tortNegligentFromInputs handNegligentFactored handNegligent
  rfl

end InstitutionalLiability
