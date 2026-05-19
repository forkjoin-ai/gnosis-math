import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyRecapManSenseWitness

/-!
# Science and Health, Chapter XIV -- Man, Soul, and the Senses

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:19680-20160`.

Bounded section: 475:3-490:27. This recapitulation unit answers what man is,
what body and Soul are, whether brain thinks or nerves feel, how belief differs
from understanding, and whether the five corporeal senses constitute man.
-/

inductive RecapManSenseMoment where
  | manNotMatter
  | manIdeaOfLove
  | manNoSeparateMind
  | dominionScripture
  | manIncapableSinSicknessDeath
  | mortalsCounterfeitImmortals
  | errorSelfDestroyed
  | mortalitySwallowedByImmortality
  | spiritualStatusSought
  | perfectManHealsSick
  | materialBodyNotGodIdea
  | identityReflectionSpirit
  | soulNotInMatter
  | manExpressionSoul
  | noDivisionSpiritMan
  | indwellingSoulTheoryUnseen
  | brainDoesNotThink
  | nervesDoNotFeel
  | mortalManContradiction
  | matterNotSelfCognizant
  | chaosImaginaryOpposite
  | evilNoIdentityHue
  | matterNothingnessRecognized
  | harmoniousActionFromSpirit
  | evilFalseBelief
  | evilVanishesBeforeGood
  | materialSenseForbiddenFruit
  | hypothesesProcureDiscord
  | senseNotSoulSins
  | soulDefinedAsGodOrSense
  | jesusSonshipControlsMatter
  | sicknessErrorTruthCastsOut
  | drugsOnlyTemporaryRelief
  | scienceNamesSubstanceMind
  | scienceHonorsGodByWorks
  | medicationNotIncluded
  | physicalForceMortalMind
  | animalMagnetismError
  | materialSenseAbsurd
  | emergeGentlyIntoSpirit
  | deathNotImmortalizer
  | materialStrengthNoFoundation
  | spiritualSenseRequired
  | deathWillNotCorrectError
  | sensesPermanentInSpirit
  | mindFacultiesNotLost
  | beliefAndBelieverOneMortal
  | worksConfirmFaith
  | beliefMeansUnderstandingInScripture
  | corporealSensesMortalBeliefs
  | facultiesFromMind
  | lifeScienceRestoresSense
  | corporealSenseBreaksDecalogue
  | organicConstructionCannotMakeMind
  | willPowerAnimalPropensity
  | theoriesHelpless
  | immortalTestimonyDestroysMaterialSense
deriving DecidableEq, Repr

def recapManSenseTrace : List RecapManSenseMoment :=
  [ RecapManSenseMoment.manNotMatter
  , RecapManSenseMoment.manIdeaOfLove
  , RecapManSenseMoment.manNoSeparateMind
  , RecapManSenseMoment.dominionScripture
  , RecapManSenseMoment.manIncapableSinSicknessDeath
  , RecapManSenseMoment.mortalsCounterfeitImmortals
  , RecapManSenseMoment.errorSelfDestroyed
  , RecapManSenseMoment.mortalitySwallowedByImmortality
  , RecapManSenseMoment.spiritualStatusSought
  , RecapManSenseMoment.perfectManHealsSick
  , RecapManSenseMoment.materialBodyNotGodIdea
  , RecapManSenseMoment.identityReflectionSpirit
  , RecapManSenseMoment.soulNotInMatter
  , RecapManSenseMoment.manExpressionSoul
  , RecapManSenseMoment.noDivisionSpiritMan
  , RecapManSenseMoment.indwellingSoulTheoryUnseen
  , RecapManSenseMoment.brainDoesNotThink
  , RecapManSenseMoment.nervesDoNotFeel
  , RecapManSenseMoment.mortalManContradiction
  , RecapManSenseMoment.matterNotSelfCognizant
  , RecapManSenseMoment.chaosImaginaryOpposite
  , RecapManSenseMoment.evilNoIdentityHue
  , RecapManSenseMoment.matterNothingnessRecognized
  , RecapManSenseMoment.harmoniousActionFromSpirit
  , RecapManSenseMoment.evilFalseBelief
  , RecapManSenseMoment.evilVanishesBeforeGood
  , RecapManSenseMoment.materialSenseForbiddenFruit
  , RecapManSenseMoment.hypothesesProcureDiscord
  , RecapManSenseMoment.senseNotSoulSins
  , RecapManSenseMoment.soulDefinedAsGodOrSense
  , RecapManSenseMoment.jesusSonshipControlsMatter
  , RecapManSenseMoment.sicknessErrorTruthCastsOut
  , RecapManSenseMoment.drugsOnlyTemporaryRelief
  , RecapManSenseMoment.scienceNamesSubstanceMind
  , RecapManSenseMoment.scienceHonorsGodByWorks
  , RecapManSenseMoment.medicationNotIncluded
  , RecapManSenseMoment.physicalForceMortalMind
  , RecapManSenseMoment.animalMagnetismError
  , RecapManSenseMoment.materialSenseAbsurd
  , RecapManSenseMoment.emergeGentlyIntoSpirit
  , RecapManSenseMoment.deathNotImmortalizer
  , RecapManSenseMoment.materialStrengthNoFoundation
  , RecapManSenseMoment.spiritualSenseRequired
  , RecapManSenseMoment.deathWillNotCorrectError
  , RecapManSenseMoment.sensesPermanentInSpirit
  , RecapManSenseMoment.mindFacultiesNotLost
  , RecapManSenseMoment.beliefAndBelieverOneMortal
  , RecapManSenseMoment.worksConfirmFaith
  , RecapManSenseMoment.beliefMeansUnderstandingInScripture
  , RecapManSenseMoment.corporealSensesMortalBeliefs
  , RecapManSenseMoment.facultiesFromMind
  , RecapManSenseMoment.lifeScienceRestoresSense
  , RecapManSenseMoment.corporealSenseBreaksDecalogue
  , RecapManSenseMoment.organicConstructionCannotMakeMind
  , RecapManSenseMoment.willPowerAnimalPropensity
  , RecapManSenseMoment.theoriesHelpless
  , RecapManSenseMoment.immortalTestimonyDestroysMaterialSense
  ]

structure RecapManSense where
  manSpiritualIdea : Bool
  soulNotInBody : Bool
  matterCannotSense : Bool
  evilFalseBelief : Bool
  deathDoesNotCorrectError : Bool
  beliefMortal : Bool
  corporealSensesFalse : Bool
  facultiesFromMind : Bool
deriving DecidableEq, Repr

def recapManSense : RecapManSense where
  manSpiritualIdea := true
  soulNotInBody := true
  matterCannotSense := true
  evilFalseBelief := true
  deathDoesNotCorrectError := true
  beliefMortal := true
  corporealSensesFalse := true
  facultiesFromMind := true

theorem eddy_recap_man_sense_witness :
    recapManSenseTrace.length = 57
    ∧ recapManSenseTrace.head? =
      some RecapManSenseMoment.manNotMatter
    ∧ recapManSenseTrace.getLast? =
      some RecapManSenseMoment.immortalTestimonyDestroysMaterialSense
    ∧ recapManSense.manSpiritualIdea = true
    ∧ recapManSense.soulNotInBody = true
    ∧ recapManSense.matterCannotSense = true
    ∧ recapManSense.evilFalseBelief = true
    ∧ recapManSense.deathDoesNotCorrectError = true
    ∧ recapManSense.beliefMortal = true
    ∧ recapManSense.corporealSensesFalse = true
    ∧ recapManSense.facultiesFromMind = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyRecapManSenseWitness
end Gnosis.Witnesses.Eddy
