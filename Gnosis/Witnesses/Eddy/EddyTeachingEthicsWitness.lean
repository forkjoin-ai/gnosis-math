import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyTeachingEthicsWitness

/-!
# Science and Health, Chapter XIII -- Teaching Ethics and Guarded Practice

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:18280-18780`.

Bounded section: 443:1-455:27. This teaching unit moves from medical-study
compromise and charity toward explicit rules for teaching, moral qualification,
malpractice defence, exposure of sin without granting reality to it, and the
teacher's obligation to guard students from human will and subtle error.
-/

inductive TeachingEthicsMoment where
  | medicalStudyCompromiseWarned
  | judgeNotCounsel
  | failedPatientsReleased
  | materialFailureCanOpenEyes
  | godRefugeWhenScientistsFail
  | charityTowardOpponents
  | noStrifeWithBrethren
  | teacherClarifiesEthics
  | allMindRequirement
  | guardAgainstMentalAssassin
  | latentGoodUnfolded
  | materialMeansDwarfUnderstanding
  | divineLawObscuredByMixing
  | divineEnergySilencesWill
  | immoralPassionsCastOut
  | avariceTeachingDanger
  | bookReadingHeals
  | maliciousPracticeDestroysPower
  | goodMustDominateHealer
  | willExerciseHypnotic
  | noTrespassSelfGovernment
  | healWhenCalled
  | exposeClaimsWithoutReality
  | sinClaimMustBeDetected
  | evasionCripplesIntegrity
  | rightDoingNamesScience
  | moralMercuryMeasuresFitness
  | evilAssociatesInoculateThought
  | threeNeophyteClasses
  | touchstoneLessensEvil
  | falseClaimsAnnihilated
  | letterWithoutSpiritShipwreck
  | humanWillNotScience
  | teacherOpensStudentsEyes
  | malpracticeBarsDoor
  | rebukeErrorWhenNeeded
  | rightMustBeLived
  | sinfulMotiveDestroysHealing
  | truthErrorStrifeWinsBasis
  | honestySpiritualPower
  | sicknessTreatedLikeSin
  | mindMedicineNoHygiene
  | truthOmnipotenceDestroysFear
  | loveIncentiveHealingTeaching
  | teacherCareContinues
  | selfCondemnationWeakensHealing
  | godSelectsFitMessenger
deriving DecidableEq, Repr

def teachingEthicsTrace : List TeachingEthicsMoment :=
  [ TeachingEthicsMoment.medicalStudyCompromiseWarned
  , TeachingEthicsMoment.judgeNotCounsel
  , TeachingEthicsMoment.failedPatientsReleased
  , TeachingEthicsMoment.materialFailureCanOpenEyes
  , TeachingEthicsMoment.godRefugeWhenScientistsFail
  , TeachingEthicsMoment.charityTowardOpponents
  , TeachingEthicsMoment.noStrifeWithBrethren
  , TeachingEthicsMoment.teacherClarifiesEthics
  , TeachingEthicsMoment.allMindRequirement
  , TeachingEthicsMoment.guardAgainstMentalAssassin
  , TeachingEthicsMoment.latentGoodUnfolded
  , TeachingEthicsMoment.materialMeansDwarfUnderstanding
  , TeachingEthicsMoment.divineLawObscuredByMixing
  , TeachingEthicsMoment.divineEnergySilencesWill
  , TeachingEthicsMoment.immoralPassionsCastOut
  , TeachingEthicsMoment.avariceTeachingDanger
  , TeachingEthicsMoment.bookReadingHeals
  , TeachingEthicsMoment.maliciousPracticeDestroysPower
  , TeachingEthicsMoment.goodMustDominateHealer
  , TeachingEthicsMoment.willExerciseHypnotic
  , TeachingEthicsMoment.noTrespassSelfGovernment
  , TeachingEthicsMoment.healWhenCalled
  , TeachingEthicsMoment.exposeClaimsWithoutReality
  , TeachingEthicsMoment.sinClaimMustBeDetected
  , TeachingEthicsMoment.evasionCripplesIntegrity
  , TeachingEthicsMoment.rightDoingNamesScience
  , TeachingEthicsMoment.moralMercuryMeasuresFitness
  , TeachingEthicsMoment.evilAssociatesInoculateThought
  , TeachingEthicsMoment.threeNeophyteClasses
  , TeachingEthicsMoment.touchstoneLessensEvil
  , TeachingEthicsMoment.falseClaimsAnnihilated
  , TeachingEthicsMoment.letterWithoutSpiritShipwreck
  , TeachingEthicsMoment.humanWillNotScience
  , TeachingEthicsMoment.teacherOpensStudentsEyes
  , TeachingEthicsMoment.malpracticeBarsDoor
  , TeachingEthicsMoment.rebukeErrorWhenNeeded
  , TeachingEthicsMoment.rightMustBeLived
  , TeachingEthicsMoment.sinfulMotiveDestroysHealing
  , TeachingEthicsMoment.truthErrorStrifeWinsBasis
  , TeachingEthicsMoment.honestySpiritualPower
  , TeachingEthicsMoment.sicknessTreatedLikeSin
  , TeachingEthicsMoment.mindMedicineNoHygiene
  , TeachingEthicsMoment.truthOmnipotenceDestroysFear
  , TeachingEthicsMoment.loveIncentiveHealingTeaching
  , TeachingEthicsMoment.teacherCareContinues
  , TeachingEthicsMoment.selfCondemnationWeakensHealing
  , TeachingEthicsMoment.godSelectsFitMessenger
  ]

structure TeachingEthics where
  medicalCompromiseWarned : Bool
  charityRequired : Bool
  teacherEthicsCentral : Bool
  malpracticeRejected : Bool
  sinExposedNotReified : Bool
  rightDoingRequired : Bool
  humanWillNotScience : Bool
  loveIncentive : Bool
deriving DecidableEq, Repr

def teachingEthics : TeachingEthics where
  medicalCompromiseWarned := true
  charityRequired := true
  teacherEthicsCentral := true
  malpracticeRejected := true
  sinExposedNotReified := true
  rightDoingRequired := true
  humanWillNotScience := true
  loveIncentive := true

theorem eddy_teaching_ethics_witness :
    teachingEthicsTrace.length = 47
    ∧ teachingEthicsTrace.head? =
      some TeachingEthicsMoment.medicalStudyCompromiseWarned
    ∧ teachingEthicsTrace.getLast? =
      some TeachingEthicsMoment.godSelectsFitMessenger
    ∧ teachingEthics.medicalCompromiseWarned = true
    ∧ teachingEthics.charityRequired = true
    ∧ teachingEthics.teacherEthicsCentral = true
    ∧ teachingEthics.malpracticeRejected = true
    ∧ teachingEthics.sinExposedNotReified = true
    ∧ teachingEthics.rightDoingRequired = true
    ∧ teachingEthics.humanWillNotScience = true
    ∧ teachingEthics.loveIncentive = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyTeachingEthicsWitness
end Gnosis.Witnesses.Eddy
