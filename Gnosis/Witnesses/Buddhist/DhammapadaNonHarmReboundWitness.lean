import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Non-Harm Rebound Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 10, "Punishment".

Punishment is grounded in symmetry: all tremble, all love life. Harsh speech
rebounds; outward ascetic marks fail without desire-overcoming; good people
fashion themselves.
-/

structure SharedFearNonHarm where
  allTrembleAtPunishment : Bool := true
  allFearDeath : Bool := true
  allLoveLife : Bool := true
  likenessForbidsKilling : Bool := true
  nonPunishingFindsHappiness : Bool := true
deriving Repr, DecidableEq

structure SpeechRebound where
  harshSpeechAnsweredInKind : Bool := true
  angrySpeechPainful : Bool := true
  blowsForBlowsReturn : Bool := true
  silentLikeShatteredGongReachesNirvana : Bool := true
  contentionUnknownThere : Bool := true
deriving Repr, DecidableEq

structure OuterFormNotPurity where
  ageDeathDriveLife : Bool := true
  wickedBurnByOwnDeeds : Bool := true
  painOnInnocentReturnsTenStates : Bool := true
  nakednessHairDirtFastingCannotPurify : Bool := true
  desireOvercomeRequired : Bool := true
  tranquilRestrainedOneCountsAsBrahmana : Bool := true
  goodPeopleFashionThemselves : Bool := true
deriving Repr, DecidableEq

def sharedFearNonHarm : SharedFearNonHarm := {}
def speechRebound : SpeechRebound := {}
def outerFormNotPurity : OuterFormNotPurity := {}

theorem dhammapada_shared_fear_non_harm :
    sharedFearNonHarm.allTrembleAtPunishment = true ∧
      sharedFearNonHarm.allFearDeath = true ∧
      sharedFearNonHarm.allLoveLife = true ∧
      sharedFearNonHarm.likenessForbidsKilling = true ∧
      sharedFearNonHarm.nonPunishingFindsHappiness = true := by
  simp [sharedFearNonHarm]

theorem dhammapada_speech_rebound :
    speechRebound.harshSpeechAnsweredInKind = true ∧
      speechRebound.angrySpeechPainful = true ∧
      speechRebound.blowsForBlowsReturn = true ∧
      speechRebound.silentLikeShatteredGongReachesNirvana = true ∧
      speechRebound.contentionUnknownThere = true := by
  simp [speechRebound]

theorem dhammapada_outer_form_not_purity :
    outerFormNotPurity.ageDeathDriveLife = true ∧
      outerFormNotPurity.wickedBurnByOwnDeeds = true ∧
      outerFormNotPurity.painOnInnocentReturnsTenStates = true ∧
      outerFormNotPurity.nakednessHairDirtFastingCannotPurify = true ∧
      outerFormNotPurity.desireOvercomeRequired = true ∧
      outerFormNotPurity.tranquilRestrainedOneCountsAsBrahmana = true ∧
      outerFormNotPurity.goodPeopleFashionThemselves = true := by
  simp [outerFormNotPurity]

theorem dhammapada_non_harm_rebound_witness :
    sharedFearNonHarm.likenessForbidsKilling = true ∧
      sharedFearNonHarm.nonPunishingFindsHappiness = true ∧
      speechRebound.harshSpeechAnsweredInKind = true ∧
      speechRebound.silentLikeShatteredGongReachesNirvana = true ∧
      outerFormNotPurity.nakednessHairDirtFastingCannotPurify = true ∧
      outerFormNotPurity.desireOvercomeRequired = true ∧
      outerFormNotPurity.goodPeopleFashionThemselves = true := by
  simp [sharedFearNonHarm, speechRebound, outerFormNotPurity]

end Gnosis.Witnesses.Buddhist
