import Gnosis.Witnesses.Buddhist.DhammacakkappavattanaWheelWitness

namespace Gnosis.Witnesses.Buddhist

/-! Witness ledger for Dhammapada chapter 25, "The Bhikshu". -/

structure TotalRestraint where
  eyeEarNoseTongueRestrained : Bool := true
  bodySpeechThoughtRestrained : Bool := true
  allThingsRestrainedFreedFromPain : Bool := true
  handFootSpeechControlled : Bool := true
  inwardDelightSolitaryContent : Bool := true
  lawDwellingPreventsFallAway : Bool := true
deriving Repr, DecidableEq

structure EmptyBoatKnowledgeMeditation where
  nameFormNonIdentification : Bool := true
  kindnessReachesQuietPlace : Bool := true
  emptyBoatGoesQuickly : Bool := true
  passionHatredCutToNirvana : Bool := true
  fiveCutFiveLeftFiveRisenAbove : Bool := true
  noKnowledgeNoMeditation : Bool := true
  noMeditationNoKnowledge : Bool := true
  knowledgeMeditationNearNirvana : Bool := true
deriving Repr, DecidableEq

structure QuietSelfProtectedBhikshu where
  emptyHouseMindTranquil : Bool := true
  originDestructionElementsSeen : Bool := true
  nobleFriendsKept : Bool := true
  witheredFlowersShedPassionHatred : Bool := true
  bodyTongueMindQuiet : Bool := true
  baitsOfWorldRejected : Bool := true
  selfRousedBySelf : Bool := true
  selfLordSelfRefuge : Bool := true
  youngBhikshuBrightensWorld : Bool := true
deriving Repr, DecidableEq

def totalRestraint : TotalRestraint := {}
def emptyBoatKnowledgeMeditation : EmptyBoatKnowledgeMeditation := {}
def quietSelfProtectedBhikshu : QuietSelfProtectedBhikshu := {}

theorem dhammapada_total_restraint :
    totalRestraint.eyeEarNoseTongueRestrained = true ∧
      totalRestraint.bodySpeechThoughtRestrained = true ∧
      totalRestraint.allThingsRestrainedFreedFromPain = true ∧
      totalRestraint.handFootSpeechControlled = true ∧
      totalRestraint.inwardDelightSolitaryContent = true ∧
      totalRestraint.lawDwellingPreventsFallAway = true := by
  simp [totalRestraint]

theorem dhammapada_empty_boat_knowledge_meditation :
    emptyBoatKnowledgeMeditation.nameFormNonIdentification = true ∧
      emptyBoatKnowledgeMeditation.kindnessReachesQuietPlace = true ∧
      emptyBoatKnowledgeMeditation.emptyBoatGoesQuickly = true ∧
      emptyBoatKnowledgeMeditation.passionHatredCutToNirvana = true ∧
      emptyBoatKnowledgeMeditation.fiveCutFiveLeftFiveRisenAbove = true ∧
      emptyBoatKnowledgeMeditation.noKnowledgeNoMeditation = true ∧
      emptyBoatKnowledgeMeditation.noMeditationNoKnowledge = true ∧
      emptyBoatKnowledgeMeditation.knowledgeMeditationNearNirvana = true := by
  simp [emptyBoatKnowledgeMeditation]

theorem dhammapada_quiet_self_protected_bhikshu :
    quietSelfProtectedBhikshu.emptyHouseMindTranquil = true ∧
      quietSelfProtectedBhikshu.originDestructionElementsSeen = true ∧
      quietSelfProtectedBhikshu.nobleFriendsKept = true ∧
      quietSelfProtectedBhikshu.witheredFlowersShedPassionHatred = true ∧
      quietSelfProtectedBhikshu.bodyTongueMindQuiet = true ∧
      quietSelfProtectedBhikshu.baitsOfWorldRejected = true ∧
      quietSelfProtectedBhikshu.selfRousedBySelf = true ∧
      quietSelfProtectedBhikshu.selfLordSelfRefuge = true ∧
      quietSelfProtectedBhikshu.youngBhikshuBrightensWorld = true := by
  simp [quietSelfProtectedBhikshu]

theorem dhammapada_bhikshu_empty_boat_witness :
    totalRestraint.allThingsRestrainedFreedFromPain = true ∧
      emptyBoatKnowledgeMeditation.emptyBoatGoesQuickly = true ∧
      emptyBoatKnowledgeMeditation.noKnowledgeNoMeditation = true ∧
      emptyBoatKnowledgeMeditation.noMeditationNoKnowledge = true ∧
      quietSelfProtectedBhikshu.bodyTongueMindQuiet = true ∧
      quietSelfProtectedBhikshu.selfLordSelfRefuge = true := by
  simp [totalRestraint, emptyBoatKnowledgeMeditation, quietSelfProtectedBhikshu]

end Gnosis.Witnesses.Buddhist
