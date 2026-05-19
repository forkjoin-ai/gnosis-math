import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPracticePresentImmortalityWitness

/-!
# Science and Health, Chapter XII -- Present Immortality Before the Allegory

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:17600-17780`.

Bounded section: 426:3-430:15. This practice unit closes the pre-allegory
sequence by treating death as a belief to be mastered, immortality as a present
fact to be brought out, continuity before birth and after death as one problem,
and the shift from matter to Spirit as the condition for faster progress toward
Life and Love.
-/

inductive PresentImmortalityMoment where
  | highGoalSpeedsProgress
  | struggleForTruthStrengthens
  | noDeathTreeOfLife
  | deathDoesNotSaveFromSinOrSickness
  | fearOfGraveDestroyed
  | deathDisappearsWithSin
  | materialConceptsOnlyDestroyed
  | lifeLawOfSoul
  | existenceContingentOnMatterMastered
  | deathMaterialDreamPhase
  | brokenBodyDoesNotEndMan
  | deathDestroyedAsLastEnemy
  | immortalMindSupremeInPhysicalRealm
  | spiritFirstAndOnlyResort
  | noDeathNoReaction
  | lifeRealDeathIllusion
  | falseTrustsDivested
  | bodyAsGodBuiltTemple
  | existenceConsecratedToLife
  | mentalMightOffsetsMisconceptions
  | manPresentPerfectImmortal
  | simpleDemonstrationsFirst
  | corpseDoesNotSuffer
  | mortalMindAffirmationFalse
  | continuityBeforeAndAfter
  | jesusSayingIncludesPhenomena
  | mortalMindMustPartWithError
  | faithRestsOnSpirit
  | deathBeliefShutsOutLife
  | courtAllegoryIntroduced
deriving DecidableEq, Repr

def presentImmortalityTrace : List PresentImmortalityMoment :=
  [ PresentImmortalityMoment.highGoalSpeedsProgress
  , PresentImmortalityMoment.struggleForTruthStrengthens
  , PresentImmortalityMoment.noDeathTreeOfLife
  , PresentImmortalityMoment.deathDoesNotSaveFromSinOrSickness
  , PresentImmortalityMoment.fearOfGraveDestroyed
  , PresentImmortalityMoment.deathDisappearsWithSin
  , PresentImmortalityMoment.materialConceptsOnlyDestroyed
  , PresentImmortalityMoment.lifeLawOfSoul
  , PresentImmortalityMoment.existenceContingentOnMatterMastered
  , PresentImmortalityMoment.deathMaterialDreamPhase
  , PresentImmortalityMoment.brokenBodyDoesNotEndMan
  , PresentImmortalityMoment.deathDestroyedAsLastEnemy
  , PresentImmortalityMoment.immortalMindSupremeInPhysicalRealm
  , PresentImmortalityMoment.spiritFirstAndOnlyResort
  , PresentImmortalityMoment.noDeathNoReaction
  , PresentImmortalityMoment.lifeRealDeathIllusion
  , PresentImmortalityMoment.falseTrustsDivested
  , PresentImmortalityMoment.bodyAsGodBuiltTemple
  , PresentImmortalityMoment.existenceConsecratedToLife
  , PresentImmortalityMoment.mentalMightOffsetsMisconceptions
  , PresentImmortalityMoment.manPresentPerfectImmortal
  , PresentImmortalityMoment.simpleDemonstrationsFirst
  , PresentImmortalityMoment.corpseDoesNotSuffer
  , PresentImmortalityMoment.mortalMindAffirmationFalse
  , PresentImmortalityMoment.continuityBeforeAndAfter
  , PresentImmortalityMoment.jesusSayingIncludesPhenomena
  , PresentImmortalityMoment.mortalMindMustPartWithError
  , PresentImmortalityMoment.faithRestsOnSpirit
  , PresentImmortalityMoment.deathBeliefShutsOutLife
  , PresentImmortalityMoment.courtAllegoryIntroduced
  ]

structure PracticePresentImmortality where
  deathBeliefMustBeMastered : Bool
  lifeNotContingentOnMatter : Bool
  spiritFirstResort : Bool
  manPresentPerfectImmortal : Bool
  continuityBeforeAfter : Bool
  faithMustRestOnSpirit : Bool
  courtAllegoryNext : Bool
deriving DecidableEq, Repr

def practicePresentImmortality : PracticePresentImmortality where
  deathBeliefMustBeMastered := true
  lifeNotContingentOnMatter := true
  spiritFirstResort := true
  manPresentPerfectImmortal := true
  continuityBeforeAfter := true
  faithMustRestOnSpirit := true
  courtAllegoryNext := true

theorem eddy_practice_present_immortality_witness :
    presentImmortalityTrace.length = 30
    ∧ presentImmortalityTrace.head? =
      some PresentImmortalityMoment.highGoalSpeedsProgress
    ∧ presentImmortalityTrace.getLast? =
      some PresentImmortalityMoment.courtAllegoryIntroduced
    ∧ practicePresentImmortality.deathBeliefMustBeMastered = true
    ∧ practicePresentImmortality.lifeNotContingentOnMatter = true
    ∧ practicePresentImmortality.spiritFirstResort = true
    ∧ practicePresentImmortality.manPresentPerfectImmortal = true
    ∧ practicePresentImmortality.continuityBeforeAfter = true
    ∧ practicePresentImmortality.faithMustRestOnSpirit = true
    ∧ practicePresentImmortality.courtAllegoryNext = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPracticePresentImmortalityWitness
end Gnosis.Witnesses.Eddy
