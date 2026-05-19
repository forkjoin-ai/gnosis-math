import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansReconciliationNewCreatureWitness

/-! # 2 Corinthians 5 -- Judgment Seat, New Creature, and Reconciliation
Source text: `docs/ebooks/source-texts/bible-kjv.txt:93027-93087`. -/

structure ReconciliationNewCreature where
  heavenlyHouseAndSpiritEarnest : Bool
  walkByFaithNotSight : Bool
  labourAcceptedPresentAbsent : Bool
  appearJudgmentSeatChrist : Bool
  loveChristConstrainsOneDiedForAll : Bool
  liveUntoHimWhoDiedRose : Bool
  inChristNewCreature : Bool
  ministryWordReconciliation : Bool
  ambassadorsBeReconciled : Bool
  madeSinForUsMadeRighteousnessGod : Bool
deriving DecidableEq, Repr

def reconciliationNewCreature : ReconciliationNewCreature where
  heavenlyHouseAndSpiritEarnest := true
  walkByFaithNotSight := true
  labourAcceptedPresentAbsent := true
  appearJudgmentSeatChrist := true
  loveChristConstrainsOneDiedForAll := true
  liveUntoHimWhoDiedRose := true
  inChristNewCreature := true
  ministryWordReconciliation := true
  ambassadorsBeReconciled := true
  madeSinForUsMadeRighteousnessGod := true

theorem second_corinthians_reconciliation_new_creature_witness :
    reconciliationNewCreature.heavenlyHouseAndSpiritEarnest = true
    ∧ reconciliationNewCreature.walkByFaithNotSight = true
    ∧ reconciliationNewCreature.labourAcceptedPresentAbsent = true
    ∧ reconciliationNewCreature.appearJudgmentSeatChrist = true
    ∧ reconciliationNewCreature.loveChristConstrainsOneDiedForAll = true
    ∧ reconciliationNewCreature.liveUntoHimWhoDiedRose = true
    ∧ reconciliationNewCreature.inChristNewCreature = true
    ∧ reconciliationNewCreature.ministryWordReconciliation = true
    ∧ reconciliationNewCreature.ambassadorsBeReconciled = true
    ∧ reconciliationNewCreature.madeSinForUsMadeRighteousnessGod = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansReconciliationNewCreatureWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
