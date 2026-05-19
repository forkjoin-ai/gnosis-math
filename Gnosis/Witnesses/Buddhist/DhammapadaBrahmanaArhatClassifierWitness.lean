import Gnosis.Witnesses.Buddhist.DhammapadaArhatVoidPathWitness

namespace Gnosis.Witnesses.Buddhist

/-! Witness ledger for Dhammapada chapter 26, "The Brahmana". -/

structure BrahmanaBoundary where
  streamStoppedDesiresDrivenAway : Bool := true
  madeDestroyedUnmadeUnderstood : Bool := true
  otherShoreBothLawsReached : Bool := true
  neitherThisNorThatShore : Bool := true
  evilRidQuietWalkImpuritiesSentAway : Bool := true
  nonAttackNonRetaliation : Bool := true
  noBodyWordThoughtOffense : Bool := true
deriving Repr, DecidableEq

structure NotBirthButTruth where
  plattedHairFamilyBirthInsufficient : Bool := true
  truthRighteousnessBlessed : Bool := true
  outsideCleanInsideRaveningRejected : Bool := true
  originMotherNotClassifier : Bool := true
  poorAttachmentFreeClassifier : Bool := true
  allFettersCut : Bool := true
  reproachEnduredWithoutOffense : Bool := true
  lastBodyReceived : Bool := true
deriving Repr, DecidableEq

structure PerfectedArhatClosure where
  sufferingEndedBurdenPutDown : Bool := true
  noKillingNoSlaughter : Bool := true
  tolerantWithIntolerant : Bool := true
  trueSpeechNoHarshness : Bool := true
  noWorldNextWorldDesires : Bool := true
  aboveGoodEvilBondage : Bool := true
  otherShoreReachedDoubtFree : Bool := true
  nothingOwnBeforeBehindBetween : Bool := true
  pathUnknownPassionsExtinct : Bool := true
  endOfBirthsPerfectKnowledge : Bool := true
deriving Repr, DecidableEq

def brahmanaBoundary : BrahmanaBoundary := {}
def notBirthButTruth : NotBirthButTruth := {}
def perfectedArhatClosure : PerfectedArhatClosure := {}

theorem dhammapada_brahmana_boundary :
    brahmanaBoundary.streamStoppedDesiresDrivenAway = true ∧
      brahmanaBoundary.madeDestroyedUnmadeUnderstood = true ∧
      brahmanaBoundary.otherShoreBothLawsReached = true ∧
      brahmanaBoundary.neitherThisNorThatShore = true ∧
      brahmanaBoundary.evilRidQuietWalkImpuritiesSentAway = true ∧
      brahmanaBoundary.nonAttackNonRetaliation = true ∧
      brahmanaBoundary.noBodyWordThoughtOffense = true := by
  simp [brahmanaBoundary]

theorem dhammapada_not_birth_but_truth :
    notBirthButTruth.plattedHairFamilyBirthInsufficient = true ∧
      notBirthButTruth.truthRighteousnessBlessed = true ∧
      notBirthButTruth.outsideCleanInsideRaveningRejected = true ∧
      notBirthButTruth.originMotherNotClassifier = true ∧
      notBirthButTruth.poorAttachmentFreeClassifier = true ∧
      notBirthButTruth.allFettersCut = true ∧
      notBirthButTruth.reproachEnduredWithoutOffense = true ∧
      notBirthButTruth.lastBodyReceived = true := by
  simp [notBirthButTruth]

theorem dhammapada_perfected_arhat_closure :
    perfectedArhatClosure.sufferingEndedBurdenPutDown = true ∧
      perfectedArhatClosure.noKillingNoSlaughter = true ∧
      perfectedArhatClosure.tolerantWithIntolerant = true ∧
      perfectedArhatClosure.trueSpeechNoHarshness = true ∧
      perfectedArhatClosure.noWorldNextWorldDesires = true ∧
      perfectedArhatClosure.aboveGoodEvilBondage = true ∧
      perfectedArhatClosure.otherShoreReachedDoubtFree = true ∧
      perfectedArhatClosure.nothingOwnBeforeBehindBetween = true ∧
      perfectedArhatClosure.pathUnknownPassionsExtinct = true ∧
      perfectedArhatClosure.endOfBirthsPerfectKnowledge = true := by
  simp [perfectedArhatClosure]

theorem dhammapada_brahmana_arhat_classifier_witness :
    brahmanaBoundary.streamStoppedDesiresDrivenAway = true ∧
      brahmanaBoundary.noBodyWordThoughtOffense = true ∧
      notBirthButTruth.plattedHairFamilyBirthInsufficient = true ∧
      notBirthButTruth.allFettersCut = true ∧
      perfectedArhatClosure.aboveGoodEvilBondage = true ∧
      perfectedArhatClosure.nothingOwnBeforeBehindBetween = true ∧
      perfectedArhatClosure.endOfBirthsPerfectKnowledge = true := by
  simp [brahmanaBoundary, notBirthButTruth, perfectedArhatClosure]

end Gnosis.Witnesses.Buddhist
