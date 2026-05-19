import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansIdolKnowledgeCharityWitness

/-! # 1 Corinthians 8 -- Idol Meat, Knowledge, and Charity
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92059-92094`. -/

structure IdolKnowledgeCharity where
  knowledgePuffsCharityEdifies : Bool
  idolNothingOneGod : Bool
  oneGodFatherOneLordJesus : Bool
  notAllHaveKnowledge : Bool
  libertyCanBecomeStumblingblock : Bool
  woundWeakConscienceSinAgainstChrist : Bool
  noMeatIfBrotherOffended : Bool
deriving DecidableEq, Repr

def idolKnowledgeCharity : IdolKnowledgeCharity where
  knowledgePuffsCharityEdifies := true
  idolNothingOneGod := true
  oneGodFatherOneLordJesus := true
  notAllHaveKnowledge := true
  libertyCanBecomeStumblingblock := true
  woundWeakConscienceSinAgainstChrist := true
  noMeatIfBrotherOffended := true

theorem first_corinthians_idol_knowledge_charity_witness :
    idolKnowledgeCharity.knowledgePuffsCharityEdifies = true
    ∧ idolKnowledgeCharity.idolNothingOneGod = true
    ∧ idolKnowledgeCharity.oneGodFatherOneLordJesus = true
    ∧ idolKnowledgeCharity.notAllHaveKnowledge = true
    ∧ idolKnowledgeCharity.libertyCanBecomeStumblingblock = true
    ∧ idolKnowledgeCharity.woundWeakConscienceSinAgainstChrist = true
    ∧ idolKnowledgeCharity.noMeatIfBrotherOffended = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansIdolKnowledgeCharityWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
