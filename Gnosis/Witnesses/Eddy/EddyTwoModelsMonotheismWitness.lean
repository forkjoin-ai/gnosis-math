import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyTwoModelsMonotheismWitness

/-!
# Science and Health, Chapter XI -- Two Models and Monotheism

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:14820-15022`.

Bounded section: 356:27-361:30. The chapter closes by rejecting two infinite
creators, denying matter's power over Life, refusing faith-in-healer as the
explanation of healing, and forcing the reader to choose one model: Spirit or
matter. It ends with First-Commandment monotheism reconciling Jew and
Christian around Christ as spiritual idea.
-/

inductive TwoModelsMoment where
  | twoCreatorsAbsurd
  | godDoesNotCreatePunishableEvil
  | truthSustainedByRejectingLie
  | truthCreatesNoLiar
  | anthropomorphicNotionsHumanOrigin
  | oppositionToGodCannotBeReal
  | matterCannotDefeatOmnipotence
  | scienceNotContradictory
  | scripturesSustainedDemonstrably
  | worksUnderstoodLessThanWords
  | faithInHealerCounterexample
  | spiritEvidenceSpiritualOnly
  | twoArtistsSpiritualAndMaterialIdeals
  | oneModelDecision
  | twoModelsMeansNone
  | christScienceReconcilesDoctrinalDispute
  | firstCommandmentMonotheismShared
  | jesusSonNotGod
  | oneInQualityNotQuantity
  | revisionsClarifyOriginalMeaning
  | spiritualIdeasUnfold
  | seedRequiresPreparedSoil
deriving DecidableEq, Repr

def twoModelsTrace : List TwoModelsMoment :=
  [ TwoModelsMoment.twoCreatorsAbsurd
  , TwoModelsMoment.godDoesNotCreatePunishableEvil
  , TwoModelsMoment.truthSustainedByRejectingLie
  , TwoModelsMoment.truthCreatesNoLiar
  , TwoModelsMoment.anthropomorphicNotionsHumanOrigin
  , TwoModelsMoment.oppositionToGodCannotBeReal
  , TwoModelsMoment.matterCannotDefeatOmnipotence
  , TwoModelsMoment.scienceNotContradictory
  , TwoModelsMoment.scripturesSustainedDemonstrably
  , TwoModelsMoment.worksUnderstoodLessThanWords
  , TwoModelsMoment.faithInHealerCounterexample
  , TwoModelsMoment.spiritEvidenceSpiritualOnly
  , TwoModelsMoment.twoArtistsSpiritualAndMaterialIdeals
  , TwoModelsMoment.oneModelDecision
  , TwoModelsMoment.twoModelsMeansNone
  , TwoModelsMoment.christScienceReconcilesDoctrinalDispute
  , TwoModelsMoment.firstCommandmentMonotheismShared
  , TwoModelsMoment.jesusSonNotGod
  , TwoModelsMoment.oneInQualityNotQuantity
  , TwoModelsMoment.revisionsClarifyOriginalMeaning
  , TwoModelsMoment.spiritualIdeasUnfold
  , TwoModelsMoment.seedRequiresPreparedSoil
  ]

structure TwoModelsMonotheism where
  twoCreatorsRejected : Bool
  matterImpotentAgainstLife : Bool
  healingNotPersonalConfidence : Bool
  spiritOrMatterModelChoice : Bool
  twoModelsNoModel : Bool
  firstCommandmentReconciles : Bool
  qualityNotQuantityOneness : Bool
  revisionClarifiesMeaning : Bool
deriving DecidableEq, Repr

def twoModelsMonotheism : TwoModelsMonotheism where
  twoCreatorsRejected := true
  matterImpotentAgainstLife := true
  healingNotPersonalConfidence := true
  spiritOrMatterModelChoice := true
  twoModelsNoModel := true
  firstCommandmentReconciles := true
  qualityNotQuantityOneness := true
  revisionClarifiesMeaning := true

theorem eddy_two_models_monotheism_witness :
    twoModelsTrace.length = 22
    ∧ twoModelsTrace.head? =
      some TwoModelsMoment.twoCreatorsAbsurd
    ∧ twoModelsTrace.getLast? =
      some TwoModelsMoment.seedRequiresPreparedSoil
    ∧ twoModelsMonotheism.twoCreatorsRejected = true
    ∧ twoModelsMonotheism.matterImpotentAgainstLife = true
    ∧ twoModelsMonotheism.healingNotPersonalConfidence = true
    ∧ twoModelsMonotheism.spiritOrMatterModelChoice = true
    ∧ twoModelsMonotheism.twoModelsNoModel = true
    ∧ twoModelsMonotheism.firstCommandmentReconciles = true
    ∧ twoModelsMonotheism.qualityNotQuantityOneness = true
    ∧ twoModelsMonotheism.revisionClarifiesMeaning = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyTwoModelsMonotheismWitness
end Gnosis.Witnesses.Eddy
