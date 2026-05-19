import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyLanguageGhostCopartnershipWitness

/-!
# Science and Health, Chapter XI -- Language, Ghosts, and Copartnership

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:14480-14820`.

Bounded section: 348:18-356:27. This objections block names the language gap
between material terms and spiritual ideas, insists words require works, uses
ghost fear as the anti-reality analogy for disease, and closes by rejecting
any copartnership between error and Truth.
-/

inductive LanguageGhostMoment where
  | abandonDefenseOfDisease
  | fruitageStillRipening
  | materialLawSubordinateToSpiritual
  | lifeAndManDoNotDie
  | languageInadequateForSpirit
  | newTonguesProphecy
  | substanceSpiritualOppositeView
  | wordsNeedWorks
  | lifeLinkRealReachesUnreal
  | materialBasisCannotHeal
  | presentHelpSpiritualSense
  | fatalPremisesPersonalDevilGod
  | fruitlessMaterialWorship
  | spiritTangibleToJesus
  | ghostsNotRealities
  | fearBeliefDestroyedRestoresHealth
  | realAndUnrealAntagonism
  | superstitionSomethingnessYielded
  | graveDoesNotBanishMaterialGhost
  | wordsImmortalInDeeds
  | healingOmittedByOpponents
  | consistencyInExample
  | practicalProofOverVerbalArgument
  | criticismNeedsDemonstration
  | materialTheoriesNoSpiritualEvidence
  | matterNotVestibuleOfSpirit
  | fleshSpiritOpposites
  | noCopartnershipErrorTruth
  | godCannotProduceTriadErrors
deriving DecidableEq, Repr

def languageGhostTrace : List LanguageGhostMoment :=
  [ LanguageGhostMoment.abandonDefenseOfDisease
  , LanguageGhostMoment.fruitageStillRipening
  , LanguageGhostMoment.materialLawSubordinateToSpiritual
  , LanguageGhostMoment.lifeAndManDoNotDie
  , LanguageGhostMoment.languageInadequateForSpirit
  , LanguageGhostMoment.newTonguesProphecy
  , LanguageGhostMoment.substanceSpiritualOppositeView
  , LanguageGhostMoment.wordsNeedWorks
  , LanguageGhostMoment.lifeLinkRealReachesUnreal
  , LanguageGhostMoment.materialBasisCannotHeal
  , LanguageGhostMoment.presentHelpSpiritualSense
  , LanguageGhostMoment.fatalPremisesPersonalDevilGod
  , LanguageGhostMoment.fruitlessMaterialWorship
  , LanguageGhostMoment.spiritTangibleToJesus
  , LanguageGhostMoment.ghostsNotRealities
  , LanguageGhostMoment.fearBeliefDestroyedRestoresHealth
  , LanguageGhostMoment.realAndUnrealAntagonism
  , LanguageGhostMoment.superstitionSomethingnessYielded
  , LanguageGhostMoment.graveDoesNotBanishMaterialGhost
  , LanguageGhostMoment.wordsImmortalInDeeds
  , LanguageGhostMoment.healingOmittedByOpponents
  , LanguageGhostMoment.consistencyInExample
  , LanguageGhostMoment.practicalProofOverVerbalArgument
  , LanguageGhostMoment.criticismNeedsDemonstration
  , LanguageGhostMoment.materialTheoriesNoSpiritualEvidence
  , LanguageGhostMoment.matterNotVestibuleOfSpirit
  , LanguageGhostMoment.fleshSpiritOpposites
  , LanguageGhostMoment.noCopartnershipErrorTruth
  , LanguageGhostMoment.godCannotProduceTriadErrors
  ]

structure LanguageGhostCopartnership where
  languageGapRequiresSpiritualSense : Bool
  wordsRequireWorks : Bool
  materialBasisCannotHeal : Bool
  ghostFearAnalogy : Bool
  superstitionMustYield : Bool
  practicalProofSuperior : Bool
  matterNotVestibuleOfSpirit : Bool
  noErrorTruthCopartnership : Bool
deriving DecidableEq, Repr

def languageGhostCopartnership : LanguageGhostCopartnership where
  languageGapRequiresSpiritualSense := true
  wordsRequireWorks := true
  materialBasisCannotHeal := true
  ghostFearAnalogy := true
  superstitionMustYield := true
  practicalProofSuperior := true
  matterNotVestibuleOfSpirit := true
  noErrorTruthCopartnership := true

theorem eddy_language_ghost_copartnership_witness :
    languageGhostTrace.length = 29
    ∧ languageGhostTrace.head? =
      some LanguageGhostMoment.abandonDefenseOfDisease
    ∧ languageGhostTrace.getLast? =
      some LanguageGhostMoment.godCannotProduceTriadErrors
    ∧ languageGhostCopartnership.languageGapRequiresSpiritualSense = true
    ∧ languageGhostCopartnership.wordsRequireWorks = true
    ∧ languageGhostCopartnership.materialBasisCannotHeal = true
    ∧ languageGhostCopartnership.ghostFearAnalogy = true
    ∧ languageGhostCopartnership.superstitionMustYield = true
    ∧ languageGhostCopartnership.practicalProofSuperior = true
    ∧ languageGhostCopartnership.matterNotVestibuleOfSpirit = true
    ∧ languageGhostCopartnership.noErrorTruthCopartnership = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyLanguageGhostCopartnershipWitness
end Gnosis.Witnesses.Eddy
