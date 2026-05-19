import Init

namespace Gnosis.Witnesses.Eddy
namespace EddySerpentJacobSoulWitness

/-!
# Science and Health, Chapter X -- Serpent, Jacob, and Soul

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:12780-13080`.

Bounded section: 306:18-314:1. The passage names the Adam-dream as
pantheistic error, restages "Adam, where art thou?" as a consciousness test,
reads Jacob's wrestling as transformation by incorporeal Love, and rejects
structural life, sinful soul, finite personal deity, and matter-born spirit.
-/

inductive SerpentJacobSoulMoment where
  | scienceProvesManIntact
  | mortalThoughtFormsNotReal
  | scienceUnfoldsPermanentLife
  | godsManNotMaterialMortal
  | adamDreamParentOfDiscord
  | serpentMakesErrorEternalAsTruth
  | evilAffirmsManyIntelligences
  | errorChargesLieToTruth
  | spiritualStatutesHigherLaw
  | adamQuestionAsConsciousnessTest
  | bodyPartsSeekLifeInBody
  | patriarchsHearTruth
  | jacobWrestlesMortalSense
  | angelSmotesErrorStrength
  | nameChangeJacobToIsrael
  | messengerNamelessIncorporealLove
  | israelDemonstratesSpiritOverSense
  | lifeNeverStructuralOrganic
  | thoughtObjectifiedNotMatterPrior
  | potterNotInClay
  | soulCentralIntelligence
  | soulCannotSin
  | evilNotMadeNotReal
  | sinOnlyOfFlesh
  | senseMaterialCanBeLost
  | soulImpeccableHigherLaw
  | senseKnowledgeReversedBySpirit
  | corpseNotMan
  | corporealJehovahLimitsLove
  | finiteTheoriesHinderUnderstanding
  | christRoyalReflection
  | jesusScientificSpiritualCause
deriving DecidableEq, Repr

def serpentJacobSoulTrace : List SerpentJacobSoulMoment :=
  [ SerpentJacobSoulMoment.scienceProvesManIntact
  , SerpentJacobSoulMoment.mortalThoughtFormsNotReal
  , SerpentJacobSoulMoment.scienceUnfoldsPermanentLife
  , SerpentJacobSoulMoment.godsManNotMaterialMortal
  , SerpentJacobSoulMoment.adamDreamParentOfDiscord
  , SerpentJacobSoulMoment.serpentMakesErrorEternalAsTruth
  , SerpentJacobSoulMoment.evilAffirmsManyIntelligences
  , SerpentJacobSoulMoment.errorChargesLieToTruth
  , SerpentJacobSoulMoment.spiritualStatutesHigherLaw
  , SerpentJacobSoulMoment.adamQuestionAsConsciousnessTest
  , SerpentJacobSoulMoment.bodyPartsSeekLifeInBody
  , SerpentJacobSoulMoment.patriarchsHearTruth
  , SerpentJacobSoulMoment.jacobWrestlesMortalSense
  , SerpentJacobSoulMoment.angelSmotesErrorStrength
  , SerpentJacobSoulMoment.nameChangeJacobToIsrael
  , SerpentJacobSoulMoment.messengerNamelessIncorporealLove
  , SerpentJacobSoulMoment.israelDemonstratesSpiritOverSense
  , SerpentJacobSoulMoment.lifeNeverStructuralOrganic
  , SerpentJacobSoulMoment.thoughtObjectifiedNotMatterPrior
  , SerpentJacobSoulMoment.potterNotInClay
  , SerpentJacobSoulMoment.soulCentralIntelligence
  , SerpentJacobSoulMoment.soulCannotSin
  , SerpentJacobSoulMoment.evilNotMadeNotReal
  , SerpentJacobSoulMoment.sinOnlyOfFlesh
  , SerpentJacobSoulMoment.senseMaterialCanBeLost
  , SerpentJacobSoulMoment.soulImpeccableHigherLaw
  , SerpentJacobSoulMoment.senseKnowledgeReversedBySpirit
  , SerpentJacobSoulMoment.corpseNotMan
  , SerpentJacobSoulMoment.corporealJehovahLimitsLove
  , SerpentJacobSoulMoment.finiteTheoriesHinderUnderstanding
  , SerpentJacobSoulMoment.christRoyalReflection
  , SerpentJacobSoulMoment.jesusScientificSpiritualCause
  ]

structure SerpentJacobSoul where
  adamDreamPantheisticError : Bool
  manyIntelligencesRejected : Bool
  adamQuestionConsciousnessTest : Bool
  jacobRenamedBySpiritualStruggle : Bool
  incorporealMessenger : Bool
  lifeNeverStructural : Bool
  potterNotInClay : Bool
  soulCannotSin : Bool
  sinOnlyMaterialSense : Bool
  finitePersonalGodHindersUnderstanding : Bool
  christAsRoyalReflection : Bool
deriving DecidableEq, Repr

def serpentJacobSoul : SerpentJacobSoul where
  adamDreamPantheisticError := true
  manyIntelligencesRejected := true
  adamQuestionConsciousnessTest := true
  jacobRenamedBySpiritualStruggle := true
  incorporealMessenger := true
  lifeNeverStructural := true
  potterNotInClay := true
  soulCannotSin := true
  sinOnlyMaterialSense := true
  finitePersonalGodHindersUnderstanding := true
  christAsRoyalReflection := true

theorem eddy_serpent_jacob_soul_witness :
    serpentJacobSoulTrace.length = 32
    ∧ serpentJacobSoulTrace.head? =
      some SerpentJacobSoulMoment.scienceProvesManIntact
    ∧ serpentJacobSoulTrace.getLast? =
      some SerpentJacobSoulMoment.jesusScientificSpiritualCause
    ∧ serpentJacobSoul.adamDreamPantheisticError = true
    ∧ serpentJacobSoul.manyIntelligencesRejected = true
    ∧ serpentJacobSoul.adamQuestionConsciousnessTest = true
    ∧ serpentJacobSoul.jacobRenamedBySpiritualStruggle = true
    ∧ serpentJacobSoul.incorporealMessenger = true
    ∧ serpentJacobSoul.lifeNeverStructural = true
    ∧ serpentJacobSoul.potterNotInClay = true
    ∧ serpentJacobSoul.soulCannotSin = true
    ∧ serpentJacobSoul.sinOnlyMaterialSense = true
    ∧ serpentJacobSoul.finitePersonalGodHindersUnderstanding = true
    ∧ serpentJacobSoul.christAsRoyalReflection = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddySerpentJacobSoulWitness
end Gnosis.Witnesses.Eddy
