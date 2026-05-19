import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraLegalMercyWitness

/-!
# Quran 2:178-182, Al-Baqara -- Retribution, Pardon, Bequest Repair

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1564-1580`.

This bounded witness tracks legal mercy around murder and bequests:

  * fair retribution is prescribed in murder cases;
  * pardon by the aggrieved brother opens fair adherence and good payment;
  * this is alleviation and mercy, with suffering for exceeding limits;
  * fair retribution saves life and serves guarded understanding;
  * proper bequest to parents and close relatives is prescribed near death;
  * alteration guilt falls on the alterer;
  * repairing a mistaken or wrongful bequest incurs no sin because God is forgiving and merciful.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive LegalMercyMoment
  | fairRetribution
  | pardonAndPayment
  | alleviationMercy
  | limitsWarning
  | lifePreserved
  | properBequest
  | alterationGuilt
  | repairNoSin
deriving DecidableEq, Repr

def legalMercyMoments : List LegalMercyMoment :=
  [ LegalMercyMoment.fairRetribution
  , LegalMercyMoment.pardonAndPayment
  , LegalMercyMoment.alleviationMercy
  , LegalMercyMoment.limitsWarning
  , LegalMercyMoment.lifePreserved
  , LegalMercyMoment.properBequest
  , LegalMercyMoment.alterationGuilt
  , LegalMercyMoment.repairNoSin
  ]

structure RetributionMercyPattern where
  believersAddressed : Bool
  fairRetributionPrescribed : Bool
  murderCasesNamed : Bool
  equivalentCategoriesNamed : Bool
  pardonPossible : Bool
  aggrievedBrotherNamed : Bool
  fairAdherence : Bool
  goodPayment : Bool
  alleviationFromLord : Bool
  mercyAct : Bool
  limitExceedingWarned : Bool
  grievousSuffering : Bool
  savesLife : Bool
  peopleUnderstanding : Bool
  guardAgainstWrongAim : Bool
deriving DecidableEq, Repr

def retributionMercyPattern : RetributionMercyPattern where
  believersAddressed := true
  fairRetributionPrescribed := true
  murderCasesNamed := true
  equivalentCategoriesNamed := true
  pardonPossible := true
  aggrievedBrotherNamed := true
  fairAdherence := true
  goodPayment := true
  alleviationFromLord := true
  mercyAct := true
  limitExceedingWarned := true
  grievousSuffering := true
  savesLife := true
  peopleUnderstanding := true
  guardAgainstWrongAim := true

structure BequestRepairPattern where
  deathApproaches : Bool
  wealthLeft : Bool
  properBequestPrescribed : Bool
  parentsNamed : Bool
  closeRelativesNamed : Bool
  mindfulDuty : Bool
  alterationAfterHearing : Bool
  guiltOnAlterer : Bool
  godHearingKnowing : Bool
  testatorMistakeOrWrong : Bool
  putsThingsRight : Bool
  noSinInRepair : Bool
  godForgivingMerciful : Bool
deriving DecidableEq, Repr

def bequestRepairPattern : BequestRepairPattern where
  deathApproaches := true
  wealthLeft := true
  properBequestPrescribed := true
  parentsNamed := true
  closeRelativesNamed := true
  mindfulDuty := true
  alterationAfterHearing := true
  guiltOnAlterer := true
  godHearingKnowing := true
  testatorMistakeOrWrong := true
  putsThingsRight := true
  noSinInRepair := true
  godForgivingMerciful := true

theorem quran_al_baqara_legal_mercy_witness :
    legalMercyMoments.length = 8
    ∧ legalMercyMoments.head? = some LegalMercyMoment.fairRetribution
    ∧ legalMercyMoments.getLast? = some LegalMercyMoment.repairNoSin
    ∧ retributionMercyPattern.fairRetributionPrescribed = true
    ∧ retributionMercyPattern.murderCasesNamed = true
    ∧ retributionMercyPattern.pardonPossible = true
    ∧ retributionMercyPattern.fairAdherence = true
    ∧ retributionMercyPattern.goodPayment = true
    ∧ retributionMercyPattern.alleviationFromLord = true
    ∧ retributionMercyPattern.mercyAct = true
    ∧ retributionMercyPattern.limitExceedingWarned = true
    ∧ retributionMercyPattern.savesLife = true
    ∧ bequestRepairPattern.deathApproaches = true
    ∧ bequestRepairPattern.properBequestPrescribed = true
    ∧ bequestRepairPattern.parentsNamed = true
    ∧ bequestRepairPattern.closeRelativesNamed = true
    ∧ bequestRepairPattern.mindfulDuty = true
    ∧ bequestRepairPattern.alterationAfterHearing = true
    ∧ bequestRepairPattern.guiltOnAlterer = true
    ∧ bequestRepairPattern.testatorMistakeOrWrong = true
    ∧ bequestRepairPattern.putsThingsRight = true
    ∧ bequestRepairPattern.noSinInRepair = true
    ∧ bequestRepairPattern.godForgivingMerciful = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end QuranAlBaqaraLegalMercyWitness
end Gnosis.Witnesses.Islam
