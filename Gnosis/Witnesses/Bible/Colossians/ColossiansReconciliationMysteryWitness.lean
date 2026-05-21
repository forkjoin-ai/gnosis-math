import Init

namespace Gnosis.Witnesses.Bible.Colossians
namespace ColossiansReconciliationMysteryWitness

/-!
# Colossians 1:21-29 -- Reconciled Enemies and Christ-in-You Mystery

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94705-94733`.

The alienated enemy-mind is reconciled in the body of flesh through death. The
manifest mystery is Christ in you, hope of glory, preached toward perfect
presentation.

No `sorry`, no new `axiom`.
-/

structure ReconciledPresentation where
  alienatedEnemiesInMind : Bool := true
  reconciledThroughDeath : Bool := true
  holyUnblameableUnreproveable : Bool := true
  continueGroundedSettled : Bool := true
  notMovedFromGospelHope : Bool := true
  gospelPreachedUnderHeaven : Bool := true
deriving DecidableEq, Repr

def reconciledPresentation : ReconciledPresentation := {}

def reconciliationWitness (r : ReconciledPresentation) : Prop :=
  r.alienatedEnemiesInMind = true ∧ r.reconciledThroughDeath = true ∧
  r.holyUnblameableUnreproveable = true ∧ r.continueGroundedSettled = true ∧
  r.notMovedFromGospelHope = true ∧ r.gospelPreachedUnderHeaven = true

structure MysteryMinistry where
  sufferingsForBodyChurch : Bool := true
  dispensationToFulfilWord : Bool := true
  mysteryHiddenNowManifest : Bool := true
  richesGloryAmongGentiles : Bool := true
  christInYouHopeGlory : Bool := true
  warningTeachingAllWisdom : Bool := true
  presentEveryManPerfect : Bool := true
  labourByMightyWorking : Bool := true
deriving DecidableEq, Repr

def mysteryMinistry : MysteryMinistry := {}

def mysteryMinistryWitness (m : MysteryMinistry) : Prop :=
  m.sufferingsForBodyChurch = true ∧ m.dispensationToFulfilWord = true ∧
  m.mysteryHiddenNowManifest = true ∧ m.richesGloryAmongGentiles = true ∧
  m.christInYouHopeGlory = true ∧ m.warningTeachingAllWisdom = true ∧
  m.presentEveryManPerfect = true ∧ m.labourByMightyWorking = true

theorem colossians_reconciliation :
    reconciliationWitness reconciledPresentation := by
  unfold reconciliationWitness reconciledPresentation
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem colossians_mystery_ministry :
    mysteryMinistryWitness mysteryMinistry := by
  unfold mysteryMinistryWitness mysteryMinistry
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem colossians_reconciliation_mystery_witness :
    reconciliationWitness reconciledPresentation ∧
    mysteryMinistryWitness mysteryMinistry := by
  exact ⟨colossians_reconciliation, colossians_mystery_ministry⟩

end ColossiansReconciliationMysteryWitness
end Gnosis.Witnesses.Bible.Colossians
