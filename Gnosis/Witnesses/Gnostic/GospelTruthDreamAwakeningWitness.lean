import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Gnostic
namespace GospelTruthDreamAwakeningWitness

/-!
# Gospel of Truth -- Dream Ignorance and Dawn Awakening

Source text: `docs/ebooks/source-texts/gospel-of-truth.txt`;
text anchor `docs/ebooks/source-texts/gospel-of-truth.txt:149-202`.

Sat/unseen reading:

Ignorance is modeled as dream ontology: fear, flight, falling, violence, and
phantom pursuit feel real only until waking. The dawn is not a new object added
to the nightmare; it is the knowledge that lets the dream-properties be
renounced as nothing.

Gap / counterproof:

Shadow, phantom, and dream-confusion cannot be Sat because they vanish at dawn.
The awakened one is then stood upright and given sensory access to the beloved
son: seeing, listening, tasting, smelling, and grasping.

No `sorry`, no new `axiom`.
-/

structure DreamIgnorance where
  fearConfusion : Bool
  doublemindedDivision : Bool
  emptyIgnorance : Bool
  troubledDreams : Bool
  phantomPursuit : Bool
  nothingAtAwakening : Bool
deriving DecidableEq, Repr

def gospelDreamIgnorance : DreamIgnorance where
  fearConfusion := true
  doublemindedDivision := true
  emptyIgnorance := true
  troubledDreams := true
  phantomPursuit := true
  nothingAtAwakening := true

def dreamCannotBeSat (d : DreamIgnorance) : Prop :=
  d.fearConfusion = true ∧
  d.doublemindedDivision = true ∧
  d.emptyIgnorance = true ∧
  d.troubledDreams = true ∧
  d.phantomPursuit = true ∧
  d.nothingAtAwakening = true

structure DawnKnowledge where
  ignoranceCastOffAsSleep : Bool
  knowledgeAsDawn : Bool
  comesToSelf : Bool
  awakens : Bool
  eyesOpened : Bool
  raisedToFeet : Bool
deriving DecidableEq, Repr

def gospelDawnKnowledge : DawnKnowledge where
  ignoranceCastOffAsSleep := true
  knowledgeAsDawn := true
  comesToSelf := true
  awakens := true
  eyesOpened := true
  raisedToFeet := true

def dawnAwakens (k : DawnKnowledge) : Prop :=
  k.ignoranceCastOffAsSleep = true ∧
  k.knowledgeAsDawn = true ∧
  k.comesToSelf = true ∧
  k.awakens = true ∧
  k.eyesOpened = true ∧
  k.raisedToFeet = true

structure FaultlessWordGift where
  lightSpoke : Bool
  voiceBroughtLife : Bool
  givesThoughtUnderstanding : Bool
  punishmentsCease : Bool
  pathForStrays : Bool
  supportForTremblers : Bool
deriving DecidableEq, Repr

def gospelFaultlessWordGift : FaultlessWordGift where
  lightSpoke := true
  voiceBroughtLife := true
  givesThoughtUnderstanding := true
  punishmentsCease := true
  pathForStrays := true
  supportForTremblers := true

def wordGivesLifeAndSupport (g : FaultlessWordGift) : Prop :=
  g.lightSpoke = true ∧
  g.voiceBroughtLife = true ∧
  g.givesThoughtUnderstanding = true ∧
  g.punishmentsCease = true ∧
  g.pathForStrays = true ∧
  g.supportForTremblers = true

theorem gospel_dream_counterproof :
    dreamCannotBeSat gospelDreamIgnorance := by
  unfold dreamCannotBeSat gospelDreamIgnorance
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gospel_dawn_awakening :
    dawnAwakens gospelDawnKnowledge := by
  unfold dawnAwakens gospelDawnKnowledge
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gospel_faultless_word_gift :
    wordGivesLifeAndSupport gospelFaultlessWordGift := by
  unfold wordGivesLifeAndSupport gospelFaultlessWordGift
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem awakening_recovery_shape :
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom :=
  Gnosis.GnosisTriptychBraid.two_step_recovery

theorem gospel_truth_dream_awakening_witness :
    dreamCannotBeSat gospelDreamIgnorance ∧
    dawnAwakens gospelDawnKnowledge ∧
    wordGivesLifeAndSupport gospelFaultlessWordGift ∧
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom := by
  exact ⟨gospel_dream_counterproof,
    gospel_dawn_awakening,
    gospel_faultless_word_gift,
    awakening_recovery_shape⟩

end GospelTruthDreamAwakeningWitness
end Gnosis.Witnesses.Gnostic
