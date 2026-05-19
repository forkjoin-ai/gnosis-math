import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPropheticDiscipleshipWitness

/-!
# Science and Health, Chapter X -- Prophetic Discipleship

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:11287-11395`.

Bounded section: 270:14-272:18. The passage maps prophecy, Christly
demonstration, discipleship, and scriptural interpretation onto one training
surface. Healing is not treated as arbitrary miracle or private privilege; it
is a learned Science that requires spiritual sense, ethical receptivity, and
guarded transmission.
-/

inductive DiscipleshipMoment where
  | prophetsLookBeyondTheirSystems
  | newDispensationUnspecifiedToProphets
  | demonstrationDestroysSinSicknessDeath
  | priestlyPrideExcludedFromChrist
  | truthAndLoveUnmakeSinAndSickness
  | divineMindAloneHeals
  | christLifeNotMiracleButSpiritualNativeLaw
  | disciplesHealThroughMindNotMatter
  | discipleMeansStudent
  | healingComesThroughCultivatedUnderstanding
  | comforterTeachesAllTruth
  | sermonOnMountEssence
  | scripturesContainHealingPractice
  | spiritualImportImpartsPower
  | spiritualSenseRequiredForTruth
  | guardedTeachingRefusesDullEars
deriving DecidableEq, Repr

def discipleshipTrace : List DiscipleshipMoment :=
  [ DiscipleshipMoment.prophetsLookBeyondTheirSystems
  , DiscipleshipMoment.newDispensationUnspecifiedToProphets
  , DiscipleshipMoment.demonstrationDestroysSinSicknessDeath
  , DiscipleshipMoment.priestlyPrideExcludedFromChrist
  , DiscipleshipMoment.truthAndLoveUnmakeSinAndSickness
  , DiscipleshipMoment.divineMindAloneHeals
  , DiscipleshipMoment.christLifeNotMiracleButSpiritualNativeLaw
  , DiscipleshipMoment.disciplesHealThroughMindNotMatter
  , DiscipleshipMoment.discipleMeansStudent
  , DiscipleshipMoment.healingComesThroughCultivatedUnderstanding
  , DiscipleshipMoment.comforterTeachesAllTruth
  , DiscipleshipMoment.sermonOnMountEssence
  , DiscipleshipMoment.scripturesContainHealingPractice
  , DiscipleshipMoment.spiritualImportImpartsPower
  , DiscipleshipMoment.spiritualSenseRequiredForTruth
  , DiscipleshipMoment.guardedTeachingRefusesDullEars
  ]

structure PropheticDiscipleship where
  prophecySeesBeyondSystem : Bool
  demonstrationDefinesOmnipotence : Bool
  prideOfPriesthoodRejected : Bool
  sicknessFramedAsMentalNotMaterial : Bool
  divineMindOnlyHealer : Bool
  healingNotSupernaturalGift : Bool
  discipleshipRequiresCultivation : Bool
  scriptureHasSpiritualImport : Bool
  receptivityConditionRequired : Bool
  guardedTransmissionBoundary : Bool
deriving DecidableEq, Repr

def propheticDiscipleship : PropheticDiscipleship where
  prophecySeesBeyondSystem := true
  demonstrationDefinesOmnipotence := true
  prideOfPriesthoodRejected := true
  sicknessFramedAsMentalNotMaterial := true
  divineMindOnlyHealer := true
  healingNotSupernaturalGift := true
  discipleshipRequiresCultivation := true
  scriptureHasSpiritualImport := true
  receptivityConditionRequired := true
  guardedTransmissionBoundary := true

theorem eddy_prophetic_discipleship_witness :
    discipleshipTrace.length = 16
    ∧ discipleshipTrace.head? =
      some DiscipleshipMoment.prophetsLookBeyondTheirSystems
    ∧ discipleshipTrace.getLast? =
      some DiscipleshipMoment.guardedTeachingRefusesDullEars
    ∧ propheticDiscipleship.prophecySeesBeyondSystem = true
    ∧ propheticDiscipleship.demonstrationDefinesOmnipotence = true
    ∧ propheticDiscipleship.prideOfPriesthoodRejected = true
    ∧ propheticDiscipleship.sicknessFramedAsMentalNotMaterial = true
    ∧ propheticDiscipleship.divineMindOnlyHealer = true
    ∧ propheticDiscipleship.healingNotSupernaturalGift = true
    ∧ propheticDiscipleship.discipleshipRequiresCultivation = true
    ∧ propheticDiscipleship.scriptureHasSpiritualImport = true
    ∧ propheticDiscipleship.receptivityConditionRequired = true
    ∧ propheticDiscipleship.guardedTransmissionBoundary = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPropheticDiscipleshipWitness
end Gnosis.Witnesses.Eddy
