import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyErrorDeathProgressionWitness

/-!
# Science and Health, Chapter X -- Error, Death, and Progression

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:11980-12180`.

Bounded section: 287:1-291:27. This unit refuses the common escape hatch that
death repairs error. Error has no real origin, death is a mortal illusion,
pardon is destruction of sin rather than cancellation while unforsaken, and
salvation proceeds by progression and probation.
-/

inductive ErrorDeathMoment where
  | sinSicknessDeathNoRealOrigin
  | materialManPostulateContradicted
  | truthHasNoUnlikeness
  | errorOffshootOfMindRejected
  | matterObjectiveSupposition
  | truthCannotBeContaminated
  | conflictSpiritualSenseVersusMaterialSense
  | chiefStonesPostulates
  | christElementWayShower
  | realExistenceComesToLight
  | wickednessNotMan
  | deathMortalIllusion
  | materialLifeBeliefProducesDeathBelief
  | spiritualFactContradictsMaterialBelief
  | manOffspringOfSpirit
  | deathNoSpiritualAdvantage
  | deathDoesNotDestroySinBelief
  | perfectionGainedByPerfection
  | sinPunishedUntilErrorDies
  | pardonWithoutForsakingRejected
  | wisdomLastCallRequiresLesserCalls
  | salvationNeedsProgressionProbation
  | heavenStateOfMind
  | deathFindsManAsHeIs
  | mindNeverBecomesDust
deriving DecidableEq, Repr

def errorDeathTrace : List ErrorDeathMoment :=
  [ ErrorDeathMoment.sinSicknessDeathNoRealOrigin
  , ErrorDeathMoment.materialManPostulateContradicted
  , ErrorDeathMoment.truthHasNoUnlikeness
  , ErrorDeathMoment.errorOffshootOfMindRejected
  , ErrorDeathMoment.matterObjectiveSupposition
  , ErrorDeathMoment.truthCannotBeContaminated
  , ErrorDeathMoment.conflictSpiritualSenseVersusMaterialSense
  , ErrorDeathMoment.chiefStonesPostulates
  , ErrorDeathMoment.christElementWayShower
  , ErrorDeathMoment.realExistenceComesToLight
  , ErrorDeathMoment.wickednessNotMan
  , ErrorDeathMoment.deathMortalIllusion
  , ErrorDeathMoment.materialLifeBeliefProducesDeathBelief
  , ErrorDeathMoment.spiritualFactContradictsMaterialBelief
  , ErrorDeathMoment.manOffspringOfSpirit
  , ErrorDeathMoment.deathNoSpiritualAdvantage
  , ErrorDeathMoment.deathDoesNotDestroySinBelief
  , ErrorDeathMoment.perfectionGainedByPerfection
  , ErrorDeathMoment.sinPunishedUntilErrorDies
  , ErrorDeathMoment.pardonWithoutForsakingRejected
  , ErrorDeathMoment.wisdomLastCallRequiresLesserCalls
  , ErrorDeathMoment.salvationNeedsProgressionProbation
  , ErrorDeathMoment.heavenStateOfMind
  , ErrorDeathMoment.deathFindsManAsHeIs
  , ErrorDeathMoment.mindNeverBecomesDust
  ]

structure ErrorDeathProgression where
  errorNoRealOrigin : Bool
  deathMortalIllusion : Bool
  deathNoAdvantage : Bool
  pardonRequiresSinDestruction : Bool
  progressionProbationRequired : Bool
  heavenStateNotLocality : Bool
  mindNeverDust : Bool
deriving DecidableEq, Repr

def errorDeathProgression : ErrorDeathProgression where
  errorNoRealOrigin := true
  deathMortalIllusion := true
  deathNoAdvantage := true
  pardonRequiresSinDestruction := true
  progressionProbationRequired := true
  heavenStateNotLocality := true
  mindNeverDust := true

theorem eddy_error_death_progression_witness :
    errorDeathTrace.length = 25
    ∧ errorDeathTrace.head? =
      some ErrorDeathMoment.sinSicknessDeathNoRealOrigin
    ∧ errorDeathTrace.getLast? =
      some ErrorDeathMoment.mindNeverBecomesDust
    ∧ errorDeathProgression.errorNoRealOrigin = true
    ∧ errorDeathProgression.deathMortalIllusion = true
    ∧ errorDeathProgression.deathNoAdvantage = true
    ∧ errorDeathProgression.pardonRequiresSinDestruction = true
    ∧ errorDeathProgression.progressionProbationRequired = true
    ∧ errorDeathProgression.heavenStateNotLocality = true
    ∧ errorDeathProgression.mindNeverDust = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyErrorDeathProgressionWitness
end Gnosis.Witnesses.Eddy
