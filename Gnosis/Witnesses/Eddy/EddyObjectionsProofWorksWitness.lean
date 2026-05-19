import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyObjectionsProofWorksWitness

/-!
# Science and Health, Chapter XI -- Objections, Proof, and Works

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:14175-14480`.

Bounded section: 341:1-348:18. The chapter answers objections by refusing
detached-quote criticism and requiring proof, works, fruits, and demonstration.
It also reasserts the nothingness of error as something to be demonstrated,
not merely asserted.
-/

inductive ObjectionsProofMoment where
  | detachedSentencesMisreadContext
  | opinionValuelessProofEssential
  | proofDemonstrationSupportChristianity
  | jesusCommandIncludesHealing
  | truthNotAccidentIfScientific
  | goodWorksKnownByFruits
  | faithShownByWorks
  | miraclesProveErrorDestructible
  | apostlesHealByReligion
  | godsImageNotMatterSinDeath
  | truthHealsErrorCausesDisease
  | judgeNotUntilTested
  | oneDivineMethod
  | spiritLikenessNotMaterial
  | understandingProvedByHealing
  | godsManDistinguishedFromAdamRace
  | idealManReflectsGod
  | nothingnessOfErrorDemonstrated
  | truthAntidotesError
  | materialBeliefsExpelled
  | nothingLeftToDoctor
  | apostolicHealingRestored
  | popularGodsDestroyed
  | diseaseAsIllusion
  | allDiseaseDelusion
  | noFaithInPowerButGod
deriving DecidableEq, Repr

def objectionsProofTrace : List ObjectionsProofMoment :=
  [ ObjectionsProofMoment.detachedSentencesMisreadContext
  , ObjectionsProofMoment.opinionValuelessProofEssential
  , ObjectionsProofMoment.proofDemonstrationSupportChristianity
  , ObjectionsProofMoment.jesusCommandIncludesHealing
  , ObjectionsProofMoment.truthNotAccidentIfScientific
  , ObjectionsProofMoment.goodWorksKnownByFruits
  , ObjectionsProofMoment.faithShownByWorks
  , ObjectionsProofMoment.miraclesProveErrorDestructible
  , ObjectionsProofMoment.apostlesHealByReligion
  , ObjectionsProofMoment.godsImageNotMatterSinDeath
  , ObjectionsProofMoment.truthHealsErrorCausesDisease
  , ObjectionsProofMoment.judgeNotUntilTested
  , ObjectionsProofMoment.oneDivineMethod
  , ObjectionsProofMoment.spiritLikenessNotMaterial
  , ObjectionsProofMoment.understandingProvedByHealing
  , ObjectionsProofMoment.godsManDistinguishedFromAdamRace
  , ObjectionsProofMoment.idealManReflectsGod
  , ObjectionsProofMoment.nothingnessOfErrorDemonstrated
  , ObjectionsProofMoment.truthAntidotesError
  , ObjectionsProofMoment.materialBeliefsExpelled
  , ObjectionsProofMoment.nothingLeftToDoctor
  , ObjectionsProofMoment.apostolicHealingRestored
  , ObjectionsProofMoment.popularGodsDestroyed
  , ObjectionsProofMoment.diseaseAsIllusion
  , ObjectionsProofMoment.allDiseaseDelusion
  , ObjectionsProofMoment.noFaithInPowerButGod
  ]

structure ObjectionsProofWorks where
  contextRequired : Bool
  proofOverOpinion : Bool
  worksAsEvidence : Bool
  healingCommandScriptural : Bool
  understandingProvedPractically : Bool
  errorNothingnessDemonstrated : Bool
  truthAntidotesError : Bool
  diseaseDelusion : Bool
  noPowerButGod : Bool
deriving DecidableEq, Repr

def objectionsProofWorks : ObjectionsProofWorks where
  contextRequired := true
  proofOverOpinion := true
  worksAsEvidence := true
  healingCommandScriptural := true
  understandingProvedPractically := true
  errorNothingnessDemonstrated := true
  truthAntidotesError := true
  diseaseDelusion := true
  noPowerButGod := true

theorem eddy_objections_proof_works_witness :
    objectionsProofTrace.length = 26
    ∧ objectionsProofTrace.head? =
      some ObjectionsProofMoment.detachedSentencesMisreadContext
    ∧ objectionsProofTrace.getLast? =
      some ObjectionsProofMoment.noFaithInPowerButGod
    ∧ objectionsProofWorks.contextRequired = true
    ∧ objectionsProofWorks.proofOverOpinion = true
    ∧ objectionsProofWorks.worksAsEvidence = true
    ∧ objectionsProofWorks.healingCommandScriptural = true
    ∧ objectionsProofWorks.understandingProvedPractically = true
    ∧ objectionsProofWorks.errorNothingnessDemonstrated = true
    ∧ objectionsProofWorks.truthAntidotesError = true
    ∧ objectionsProofWorks.diseaseDelusion = true
    ∧ objectionsProofWorks.noPowerButGod = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyObjectionsProofWorksWitness
end Gnosis.Witnesses.Eddy
