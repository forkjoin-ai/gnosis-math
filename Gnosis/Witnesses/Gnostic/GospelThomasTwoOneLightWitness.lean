import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Gnostic
namespace GospelThomasTwoOneLightWitness

/-!
# Gospel of Thomas -- Making Two One and Light Within

Source text: `docs/ebooks/source-texts/gospel-of-thomas.txt`;
text anchor `docs/ebooks/source-texts/gospel-of-thomas.txt:51-160`.

Sat/unseen reading:

Thomas repeatedly rejects identity by comparison. Peter and Matthew offer
categories; Thomas cannot speak the likeness. The real invariant arrives as
integration: make two one, inside as outside, above as below, male and female
one and the same. The light within the person of light lights the whole world.

Gap / counterproof:

Institutional practice can become harm when separated from truth: fasting,
prayer, alms, and purity rules can generate sin, condemnation, or spirit-harm.
The key of knowledge can be hidden by those who neither enter nor let others in.

No `sorry`, no new `axiom`.
-/

structure ApophaticRecognition where
  categoriesFail : Bool
  mouthCannotSayLikeness : Bool
  measuredSpringIntoxicates : Bool
  hiddenThreeThings : Bool
  stoneFireCounterDisclosure : Bool
deriving DecidableEq, Repr

def thomasApophaticRecognition : ApophaticRecognition where
  categoriesFail := true
  mouthCannotSayLikeness := true
  measuredSpringIntoxicates := true
  hiddenThreeThings := true
  stoneFireCounterDisclosure := true

def likenessCategoriesFail (a : ApophaticRecognition) : Prop :=
  a.categoriesFail = true ∧
  a.mouthCannotSayLikeness = true ∧
  a.measuredSpringIntoxicates = true ∧
  a.hiddenThreeThings = true ∧
  a.stoneFireCounterDisclosure = true

structure TwoOneEntry where
  insideOutsideOne : Bool
  aboveBelowOne : Bool
  maleFemaleOne : Bool
  imageForImage : Bool
  standAsSingleOne : Bool
  lightWithinLightsWorld : Bool
deriving DecidableEq, Repr

def thomasTwoOneEntry : TwoOneEntry where
  insideOutsideOne := true
  aboveBelowOne := true
  maleFemaleOne := true
  imageForImage := true
  standAsSingleOne := true
  lightWithinLightsWorld := true

def twoMadeOneOpensKingdom (e : TwoOneEntry) : Prop :=
  e.insideOutsideOne = true ∧
  e.aboveBelowOne = true ∧
  e.maleFemaleOne = true ∧
  e.imageForImage = true ∧
  e.standAsSingleOne = true ∧
  e.lightWithinLightsWorld = true

structure KnowledgeKeyGap where
  practiceCanHarm : Bool
  mouthDefiles : Bool
  blindLeadBlindPit : Bool
  keysHidden : Bool
  holdersDoNotEnter : Bool
  entrantsBlocked : Bool
deriving DecidableEq, Repr

def thomasKnowledgeKeyGap : KnowledgeKeyGap where
  practiceCanHarm := true
  mouthDefiles := true
  blindLeadBlindPit := true
  keysHidden := true
  holdersDoNotEnter := true
  entrantsBlocked := true

def knowledgeKeyBlocked (g : KnowledgeKeyGap) : Prop :=
  g.practiceCanHarm = true ∧
  g.mouthDefiles = true ∧
  g.blindLeadBlindPit = true ∧
  g.keysHidden = true ∧
  g.holdersDoNotEnter = true ∧
  g.entrantsBlocked = true

theorem thomas_likeness_categories_fail :
    likenessCategoriesFail thomasApophaticRecognition := by
  unfold likenessCategoriesFail thomasApophaticRecognition
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_two_one_entry :
    twoMadeOneOpensKingdom thomasTwoOneEntry := by
  unfold twoMadeOneOpensKingdom thomasTwoOneEntry
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_knowledge_key_gap :
    knowledgeKeyBlocked thomasKnowledgeKeyGap := by
  unfold knowledgeKeyBlocked thomasKnowledgeKeyGap
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_two_one_centroid :
    Gnosis.GnosisTriptychBraid.cycleSum = Gnosis.GnosisTriptychBraid.truth :=
  Gnosis.GnosisTriptychBraid.cycle_sum_zero

theorem gospel_thomas_two_one_light_witness :
    likenessCategoriesFail thomasApophaticRecognition ∧
    twoMadeOneOpensKingdom thomasTwoOneEntry ∧
    knowledgeKeyBlocked thomasKnowledgeKeyGap ∧
    Gnosis.GnosisTriptychBraid.cycleSum = Gnosis.GnosisTriptychBraid.truth := by
  exact ⟨thomas_likeness_categories_fail,
    thomas_two_one_entry,
    thomas_knowledge_key_gap,
    thomas_two_one_centroid⟩

end GospelThomasTwoOneLightWitness
end Gnosis.Witnesses.Gnostic
