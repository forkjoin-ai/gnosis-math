import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyJudgmentBeliefAngelsWitness

/-!
# Science and Health, Chapter X -- Judgment, Belief, and Thought-Angels

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:12180-12480`.

Bounded section: 291:28-299:3. The unit denies a deferred final judgment,
describes primitive error as mortal mind's material basis, treats electricity
and forces as counterfeit strata, and follows belief through purgation into
faith, spiritual sense, and angels as pure thoughts from God.
-/

inductive JudgmentBeliefMoment where
  | judgmentHourlyContinual
  | lastFaultDestroyedEndsBattle
  | truthResurrectionOnlyByDestroyingError
  | primitiveMatterBelief
  | carnalMentalityMisnamedMind
  | resurrectionShowsMortalNotEssence
  | electricityNoLinkMatterMind
  | mortalMindAndBodyFalseRepresentatives
  | forcesCounterfeitSpiritualForces
  | evilManifestationsSelfDestroyed
  | sensesInstrumentsOfError
  | pantheismSeedsAllError
  | matterThinksVerdictVictimizes
  | pleasuresPainsMyths
  | severedLimbExposesPhysicalTestimony
  | mortalConsciousnessYields
  | transparentMortalMindLosesMateriality
  | brainologyMyth
  | progressRipensMortalDroppedForImmortal
  | sufferingOrScienceDestroysIllusion
  | mixedTestimonyWearingAway
  | beliefAutocratManifestsConditions
  | truthDestroysErroneousBelief
  | faithHigherThanBelief
  | beliefFaithUnderstandingLadder
  | materialSenseTemporary
  | spiritualSenseWitnessesTruth
  | spiritualIdeasStartFromPrinciple
  | angelsPureThoughts
deriving DecidableEq, Repr

def judgmentBeliefTrace : List JudgmentBeliefMoment :=
  [ JudgmentBeliefMoment.judgmentHourlyContinual
  , JudgmentBeliefMoment.lastFaultDestroyedEndsBattle
  , JudgmentBeliefMoment.truthResurrectionOnlyByDestroyingError
  , JudgmentBeliefMoment.primitiveMatterBelief
  , JudgmentBeliefMoment.carnalMentalityMisnamedMind
  , JudgmentBeliefMoment.resurrectionShowsMortalNotEssence
  , JudgmentBeliefMoment.electricityNoLinkMatterMind
  , JudgmentBeliefMoment.mortalMindAndBodyFalseRepresentatives
  , JudgmentBeliefMoment.forcesCounterfeitSpiritualForces
  , JudgmentBeliefMoment.evilManifestationsSelfDestroyed
  , JudgmentBeliefMoment.sensesInstrumentsOfError
  , JudgmentBeliefMoment.pantheismSeedsAllError
  , JudgmentBeliefMoment.matterThinksVerdictVictimizes
  , JudgmentBeliefMoment.pleasuresPainsMyths
  , JudgmentBeliefMoment.severedLimbExposesPhysicalTestimony
  , JudgmentBeliefMoment.mortalConsciousnessYields
  , JudgmentBeliefMoment.transparentMortalMindLosesMateriality
  , JudgmentBeliefMoment.brainologyMyth
  , JudgmentBeliefMoment.progressRipensMortalDroppedForImmortal
  , JudgmentBeliefMoment.sufferingOrScienceDestroysIllusion
  , JudgmentBeliefMoment.mixedTestimonyWearingAway
  , JudgmentBeliefMoment.beliefAutocratManifestsConditions
  , JudgmentBeliefMoment.truthDestroysErroneousBelief
  , JudgmentBeliefMoment.faithHigherThanBelief
  , JudgmentBeliefMoment.beliefFaithUnderstandingLadder
  , JudgmentBeliefMoment.materialSenseTemporary
  , JudgmentBeliefMoment.spiritualSenseWitnessesTruth
  , JudgmentBeliefMoment.spiritualIdeasStartFromPrinciple
  , JudgmentBeliefMoment.angelsPureThoughts
  ]

structure JudgmentBeliefAngels where
  judgmentContinual : Bool
  deferredJudgmentRejected : Bool
  mortalStrataFalseRepresentatives : Bool
  counterfeitForcesSelfDestroyed : Bool
  materialSenseErrorInstrument : Bool
  beliefFulfillsOwnConditions : Bool
  faithAboveBelief : Bool
  spiritualSenseTruthWitness : Bool
  angelsPureThoughtsNotMaterialBeings : Bool
deriving DecidableEq, Repr

def judgmentBeliefAngels : JudgmentBeliefAngels where
  judgmentContinual := true
  deferredJudgmentRejected := true
  mortalStrataFalseRepresentatives := true
  counterfeitForcesSelfDestroyed := true
  materialSenseErrorInstrument := true
  beliefFulfillsOwnConditions := true
  faithAboveBelief := true
  spiritualSenseTruthWitness := true
  angelsPureThoughtsNotMaterialBeings := true

theorem eddy_judgment_belief_angels_witness :
    judgmentBeliefTrace.length = 29
    ∧ judgmentBeliefTrace.head? =
      some JudgmentBeliefMoment.judgmentHourlyContinual
    ∧ judgmentBeliefTrace.getLast? =
      some JudgmentBeliefMoment.angelsPureThoughts
    ∧ judgmentBeliefAngels.judgmentContinual = true
    ∧ judgmentBeliefAngels.deferredJudgmentRejected = true
    ∧ judgmentBeliefAngels.mortalStrataFalseRepresentatives = true
    ∧ judgmentBeliefAngels.counterfeitForcesSelfDestroyed = true
    ∧ judgmentBeliefAngels.materialSenseErrorInstrument = true
    ∧ judgmentBeliefAngels.beliefFulfillsOwnConditions = true
    ∧ judgmentBeliefAngels.faithAboveBelief = true
    ∧ judgmentBeliefAngels.spiritualSenseTruthWitness = true
    ∧ judgmentBeliefAngels.angelsPureThoughtsNotMaterialBeings = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyJudgmentBeliefAngelsWitness
end Gnosis.Witnesses.Eddy
