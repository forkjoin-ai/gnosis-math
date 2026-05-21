import Gnosis.Witnesses.Bible.Philemon.PhilemonLoveRefreshWitness
import Gnosis.Witnesses.Bible.Philemon.PhilemonOnesimusDebtWitness

namespace Gnosis.Witnesses.Bible.Philemon
namespace PhilemonSourceQualityWitness

/-!
# Philemon -- Source Quality Spine

Book invariant: reconciliation must be voluntary to be gospel-shaped. Paul has
authority to command, but he refuses compulsion so love can become effectual.

Primary gap/counterproof: social and economic ledgers can freeze Onesimus as
unprofitable, servant, debtor, and absent offender. Philemon breaks that ledger by
renaming him profitable, beloved brother, and receivable as Paul himself while
transferring debt to Paul's own account.

Unseen sat: forgiveness is not amnesia. The debt is named, accounted, and
re-routed so the person can be received beyond the former category.

No `sorry`, no new `axiom`.
-/

structure PhilemonInvariant where
  loveMustActWithoutCompulsion : Bool := true
  uselessCanBecomeUsefulInBonds : Bool := true
  brotherhoodExceedsServantCategory : Bool := true
  debtCanBeTransferredForReception : Bool := true
deriving DecidableEq, Repr

def philemonInvariant : PhilemonInvariant := {}

def voluntaryReconciliationInvariant (i : PhilemonInvariant) : Prop :=
  i.loveMustActWithoutCompulsion = true ∧
  i.uselessCanBecomeUsefulInBonds = true ∧
  i.brotherhoodExceedsServantCategory = true ∧
  i.debtCanBeTransferredForReception = true

structure PhilemonCounterproof where
  authorityCannotSubstituteForLove : Bool := true
  formerUseLedgerCannotDefineFuture : Bool := true
  servantStatusCannotBlockBrotherReception : Bool := true
  debtCannotErasePersonhood : Bool := true
deriving DecidableEq, Repr

def philemonCounterproof : PhilemonCounterproof := {}

def coerciveLedgerRejected (c : PhilemonCounterproof) : Prop :=
  c.authorityCannotSubstituteForLove = true ∧
  c.formerUseLedgerCannotDefineFuture = true ∧
  c.servantStatusCannotBlockBrotherReception = true ∧
  c.debtCannotErasePersonhood = true

theorem philemon_quality_invariant :
    voluntaryReconciliationInvariant philemonInvariant := by
  unfold voluntaryReconciliationInvariant philemonInvariant
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem philemon_quality_counterproof :
    coerciveLedgerRejected philemonCounterproof := by
  unfold coerciveLedgerRejected philemonCounterproof
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem philemon_source_quality_witness :
    voluntaryReconciliationInvariant philemonInvariant ∧
    coerciveLedgerRejected philemonCounterproof ∧
    PhilemonLoveRefreshWitness.loveRefreshWitness
      PhilemonLoveRefreshWitness.loveRefreshField ∧
    PhilemonOnesimusDebtWitness.voluntaryAppealWitness
      PhilemonOnesimusDebtWitness.voluntaryAppeal ∧
    PhilemonOnesimusDebtWitness.debtReceptionWitness
      PhilemonOnesimusDebtWitness.debtReception := by
  exact ⟨philemon_quality_invariant,
    philemon_quality_counterproof,
    PhilemonLoveRefreshWitness.philemon_love_refresh,
    PhilemonOnesimusDebtWitness.philemon_voluntary_appeal,
    PhilemonOnesimusDebtWitness.philemon_debt_reception⟩

end PhilemonSourceQualityWitness
end Gnosis.Witnesses.Bible.Philemon
