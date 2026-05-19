import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 4. -/

structure AncientYogaRenewed where
  deathlessYogaTaughtAnciently : Bool := true
  truthGrewDimWithYears : Bool := true
  unbornTakesVisibleShape : Bool := true
  righteousnessDeclineTriggersDescent : Bool := true
  goodSuccouredEvilThrustBack : Bool := true
  divineBirthKnownEndsRebirth : Bool := true
deriving Repr, DecidableEq

structure ActionInactionInversion where
  worksDoNotSoilEssence : Bool := true
  actingUnchainedBindsNot : Bool := true
  actionRestAndRestActionSeen : Bool := true
  desirePrickingsBurnedByTruth : Bool := true
  fruitRenouncedAlwaysContent : Bool := true
  workBecomesSacrifice : Bool := true
  allSacrificeReadAsBrahm : Bool := true
deriving Repr, DecidableEq

structure KnowledgeFire where
  knowledgeSacrificeBetterThanWealthGifts : Bool := true
  truthEndsHeartError : Bool := true
  truthShipCrossesTransgressionSea : Bool := true
  knowledgeFlameBurnsWorksDross : Bool := true
  noPurifierLikeKnowledge : Bool := true
  doubtHasNoPeace : Bool := true
  swordOfWisdomCutsDoubt : Bool := true
deriving Repr, DecidableEq

def ancientYogaRenewed : AncientYogaRenewed := {}
def actionInactionInversion : ActionInactionInversion := {}
def knowledgeFire : KnowledgeFire := {}

theorem gita_ancient_yoga_renewed :
    ancientYogaRenewed.deathlessYogaTaughtAnciently = true ∧
      ancientYogaRenewed.truthGrewDimWithYears = true ∧
      ancientYogaRenewed.unbornTakesVisibleShape = true ∧
      ancientYogaRenewed.righteousnessDeclineTriggersDescent = true ∧
      ancientYogaRenewed.goodSuccouredEvilThrustBack = true ∧
      ancientYogaRenewed.divineBirthKnownEndsRebirth = true := by
  simp [ancientYogaRenewed]

theorem gita_action_inaction_inversion :
    actionInactionInversion.worksDoNotSoilEssence = true ∧
      actionInactionInversion.actingUnchainedBindsNot = true ∧
      actionInactionInversion.actionRestAndRestActionSeen = true ∧
      actionInactionInversion.desirePrickingsBurnedByTruth = true ∧
      actionInactionInversion.fruitRenouncedAlwaysContent = true ∧
      actionInactionInversion.workBecomesSacrifice = true ∧
      actionInactionInversion.allSacrificeReadAsBrahm = true := by
  simp [actionInactionInversion]

theorem gita_knowledge_fire :
    knowledgeFire.knowledgeSacrificeBetterThanWealthGifts = true ∧
      knowledgeFire.truthEndsHeartError = true ∧
      knowledgeFire.truthShipCrossesTransgressionSea = true ∧
      knowledgeFire.knowledgeFlameBurnsWorksDross = true ∧
      knowledgeFire.noPurifierLikeKnowledge = true ∧
      knowledgeFire.doubtHasNoPeace = true ∧
      knowledgeFire.swordOfWisdomCutsDoubt = true := by
  simp [knowledgeFire]

theorem gita_knowledge_sacrifice_witness :
    ancientYogaRenewed.righteousnessDeclineTriggersDescent = true ∧
      actionInactionInversion.actionRestAndRestActionSeen = true ∧
      actionInactionInversion.workBecomesSacrifice = true ∧
      knowledgeFire.truthShipCrossesTransgressionSea = true ∧
      knowledgeFire.knowledgeFlameBurnsWorksDross = true ∧
      knowledgeFire.swordOfWisdomCutsDoubt = true := by
  simp [ancientYogaRenewed, actionInactionInversion, knowledgeFire]

end Gnosis.Witnesses.Hindu
