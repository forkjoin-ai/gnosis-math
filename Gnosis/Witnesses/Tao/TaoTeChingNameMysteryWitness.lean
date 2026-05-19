import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Tao
namespace TaoTeChingNameMysteryWitness

/-!
# Tao Te Ching -- Name, Mystery, and Non-Ownership

Source text: `docs/ebooks/source-texts/tao-te-ching-legge.txt`;
text anchor `docs/ebooks/source-texts/tao-te-ching-legge.txt:28-102`.

Sat/unseen reading:

The opening chapters are not vague mysticism. They are a name-capture
counterproof. The Tao that can be trodden and the name that can be named are not
the enduring Tao/name, but named and unnamed aspects still operate as one
mystery. Polarity co-arises, and the sage's non-action prevents process from
collapsing into ownership, reward, or achievement.

No `sorry`, no new `axiom`.
-/

inductive TaoAspect where
  | unnamedOrigin
  | namedMother
  | mysteryGate
deriving DecidableEq, Repr, Nonempty

inductive TaoWitness where
  | enduringMystery
deriving DecidableEq, Repr

def taoAspectsAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : TaoAspect => TaoWitness.enduringMystery)
      TaoWitness.enduringMystery :=
  TruthOneManyNamesWitness.constant_names_agree TaoWitness.enduringMystery

structure NameBoundary where
  troddenTaoNotEnduring : Bool
  namedNameNotEnduring : Bool
  unnamedOriginatesHeavenEarth : Bool
  namedMothersAllThings : Bool
  mysteryDeepestGate : Bool
deriving DecidableEq, Repr

def taoNameBoundary : NameBoundary where
  troddenTaoNotEnduring := true
  namedNameNotEnduring := true
  unnamedOriginatesHeavenEarth := true
  namedMothersAllThings := true
  mysteryDeepestGate := true

def nameCaptureFailsButTeaches (b : NameBoundary) : Prop :=
  b.troddenTaoNotEnduring = true ∧
  b.namedNameNotEnduring = true ∧
  b.unnamedOriginatesHeavenEarth = true ∧
  b.namedMothersAllThings = true ∧
  b.mysteryDeepestGate = true

structure PolarityCoarising where
  beautyCallsUgliness : Bool
  skillCallsLack : Bool
  existenceNonexistenceBirth : Bool
  difficultEasyProduce : Bool
  beforeBehindFollow : Bool
deriving DecidableEq, Repr

def taoPolarityCoarising : PolarityCoarising where
  beautyCallsUgliness := true
  skillCallsLack := true
  existenceNonexistenceBirth := true
  difficultEasyProduce := true
  beforeBehindFollow := true

def polarityIsRelational (p : PolarityCoarising) : Prop :=
  p.beautyCallsUgliness = true ∧
  p.skillCallsLack = true ∧
  p.existenceNonexistenceBirth = true ∧
  p.difficultEasyProduce = true ∧
  p.beforeBehindFollow = true

structure WuWeiInstruction where
  affairsWithoutDoing : Bool
  instructionWithoutSpeech : Bool
  noOwnershipClaim : Bool
  noRewardExpectation : Bool
  noRestingInAchievement : Bool
deriving DecidableEq, Repr

def taoWuWeiInstruction : WuWeiInstruction where
  affairsWithoutDoing := true
  instructionWithoutSpeech := true
  noOwnershipClaim := true
  noRewardExpectation := true
  noRestingInAchievement := true

def nonActionPreventsCapture (w : WuWeiInstruction) : Prop :=
  w.affairsWithoutDoing = true ∧
  w.instructionWithoutSpeech = true ∧
  w.noOwnershipClaim = true ∧
  w.noRewardExpectation = true ∧
  w.noRestingInAchievement = true

theorem tao_name_boundary :
    nameCaptureFailsButTeaches taoNameBoundary := by
  unfold nameCaptureFailsButTeaches taoNameBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tao_polarity_relational :
    polarityIsRelational taoPolarityCoarising := by
  unfold polarityIsRelational taoPolarityCoarising
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tao_wu_wei_instruction :
    nonActionPreventsCapture taoWuWeiInstruction := by
  unfold nonActionPreventsCapture taoWuWeiInstruction
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tao_te_ching_name_mystery_witness :
    nameCaptureFailsButTeaches taoNameBoundary ∧
    polarityIsRelational taoPolarityCoarising ∧
    nonActionPreventsCapture taoWuWeiInstruction ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : TaoAspect => TaoWitness.enduringMystery)
      TaoWitness.enduringMystery := by
  exact ⟨tao_name_boundary,
    tao_polarity_relational,
    tao_wu_wei_instruction,
    taoAspectsAgree⟩

end TaoTeChingNameMysteryWitness
end Gnosis.Witnesses.Tao
