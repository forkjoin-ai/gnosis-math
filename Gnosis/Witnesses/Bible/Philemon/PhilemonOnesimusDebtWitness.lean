import Init

namespace Gnosis.Witnesses.Bible.Philemon
namespace PhilemonOnesimusDebtWitness

/-!
# Philemon 1:8-25 -- Onesimus, Voluntary Reception, and Debt Transfer

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95941-95977`.

The core witness is non-coercive reconciliation. Paul could enjoin, but appeals
for love's sake; Onesimus is reclassified from unprofitable to profitable, from
servant to beloved brother, and any debt is placed on Paul's account.

No `sorry`, no new `axiom`.
-/

structure VoluntaryAppeal where
  authorityCouldEnjoin : Bool := true
  loveInsteadBeseeches : Bool := true
  paulAgedPrisonerAppeals : Bool := true
  onesimusBegottenInBonds : Bool := true
  unprofitableNowProfitable : Bool := true
  benefitNotNecessityButWilling : Bool := true
deriving DecidableEq, Repr

def voluntaryAppeal : VoluntaryAppeal := {}

def voluntaryAppealWitness (v : VoluntaryAppeal) : Prop :=
  v.authorityCouldEnjoin = true ∧
  v.loveInsteadBeseeches = true ∧
  v.paulAgedPrisonerAppeals = true ∧
  v.onesimusBegottenInBonds = true ∧
  v.unprofitableNowProfitable = true ∧
  v.benefitNotNecessityButWilling = true

structure DebtReception where
  departedSeasonReceivedForever : Bool := true
  notServantButBelovedBrother : Bool := true
  receiveAsPaulHimself : Bool := true
  wrongDebtPutOnPaulAccount : Bool := true
  ownHandRepaymentPledged : Bool := true
  moreThanSaidExpected : Bool := true
  lodgingThroughPrayersExpected : Bool := true
  graceWithSpiritClosing : Bool := true
deriving DecidableEq, Repr

def debtReception : DebtReception := {}

def debtReceptionWitness (d : DebtReception) : Prop :=
  d.departedSeasonReceivedForever = true ∧
  d.notServantButBelovedBrother = true ∧
  d.receiveAsPaulHimself = true ∧
  d.wrongDebtPutOnPaulAccount = true ∧
  d.ownHandRepaymentPledged = true ∧
  d.moreThanSaidExpected = true ∧
  d.lodgingThroughPrayersExpected = true ∧
  d.graceWithSpiritClosing = true

theorem philemon_voluntary_appeal :
    voluntaryAppealWitness voluntaryAppeal := by
  unfold voluntaryAppealWitness voluntaryAppeal
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem philemon_debt_reception :
    debtReceptionWitness debtReception := by
  unfold debtReceptionWitness debtReception
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem philemon_onesimus_debt_witness :
    voluntaryAppealWitness voluntaryAppeal ∧
    debtReceptionWitness debtReception := by
  exact ⟨philemon_voluntary_appeal, philemon_debt_reception⟩

end PhilemonOnesimusDebtWitness
end Gnosis.Witnesses.Bible.Philemon
