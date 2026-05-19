import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Thought Fortress Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 3, "Thought".

Thought is trembling, bodyless, hard to perceive, and stronger than external
enemies. Guarding it makes a fortress; wrong direction causes greater damage.
-/

structure MindTaming where
  fletcherStraightensArrow : Bool := true
  thoughtTremblesLikeFish : Bool := true
  tamedMindBringsHappiness : Bool := true
  guardedThoughtsBringHappiness : Bool := true
  bridledBodylessMindFreesFromMara : Bool := true
deriving Repr, DecidableEq

structure FragileBodyFortress where
  unsteadyThoughtBlocksKnowledge : Bool := true
  watchfulnessRemovesFear : Bool := true
  bodyFragileLikeJar : Bool := true
  thoughtFirmLikeFortress : Bool := true
  knowledgeWeaponAgainstMara : Bool := true
  conqueredMaraStillWatched : Bool := true
deriving Repr, DecidableEq

structure MindGreaterThanEnemy where
  bodyBecomesUselessLog : Bool := true
  wrongMindGreaterMischief : Bool := true
  wellDirectedMindGreaterService : Bool := true
  kinshipCannotOutperformRightMind : Bool := true
deriving Repr, DecidableEq

def mindTaming : MindTaming := {}
def fragileBodyFortress : FragileBodyFortress := {}
def mindGreaterThanEnemy : MindGreaterThanEnemy := {}

theorem dhammapada_mind_taming :
    mindTaming.fletcherStraightensArrow = true ∧
      mindTaming.thoughtTremblesLikeFish = true ∧
      mindTaming.tamedMindBringsHappiness = true ∧
      mindTaming.guardedThoughtsBringHappiness = true ∧
      mindTaming.bridledBodylessMindFreesFromMara = true := by
  simp [mindTaming]

theorem dhammapada_fragile_body_fortress :
    fragileBodyFortress.unsteadyThoughtBlocksKnowledge = true ∧
      fragileBodyFortress.watchfulnessRemovesFear = true ∧
      fragileBodyFortress.bodyFragileLikeJar = true ∧
      fragileBodyFortress.thoughtFirmLikeFortress = true ∧
      fragileBodyFortress.knowledgeWeaponAgainstMara = true ∧
      fragileBodyFortress.conqueredMaraStillWatched = true := by
  simp [fragileBodyFortress]

theorem dhammapada_mind_greater_than_enemy :
    mindGreaterThanEnemy.bodyBecomesUselessLog = true ∧
      mindGreaterThanEnemy.wrongMindGreaterMischief = true ∧
      mindGreaterThanEnemy.wellDirectedMindGreaterService = true ∧
      mindGreaterThanEnemy.kinshipCannotOutperformRightMind = true := by
  simp [mindGreaterThanEnemy]

theorem dhammapada_thought_fortress_witness :
    mindTaming.tamedMindBringsHappiness = true ∧
      mindTaming.bridledBodylessMindFreesFromMara = true ∧
      fragileBodyFortress.thoughtFirmLikeFortress = true ∧
      fragileBodyFortress.knowledgeWeaponAgainstMara = true ∧
      mindGreaterThanEnemy.wrongMindGreaterMischief = true ∧
      mindGreaterThanEnemy.wellDirectedMindGreaterService = true := by
  simp [mindTaming, fragileBodyFortress, mindGreaterThanEnemy]

end Gnosis.Witnesses.Buddhist
