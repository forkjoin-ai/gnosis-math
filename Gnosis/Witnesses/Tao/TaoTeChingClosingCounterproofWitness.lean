import Gnosis.GnosisTriptychBraid
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Tao

/-!
# Tao Te Ching Closing Counterproof Witness

Witness ledger for `docs/ebooks/source-texts/tao-te-ching-legge.txt`,
chapters 70-81.

The close of the text is a stack of antitheorems: fine words fail sincerity,
knowing that does not know is highest, strength marks death, water defeats the
hard, reconciliation leaves residue, and the healthy state reduces surface area
instead of maximizing reach.
-/

/-- Chapters 70-72: hidden jade and epistemic humility protect the witness. -/
structure HiddenJadeNonKnowledge where
  easyWordsRarelyPracticed : Bool := true
  fewKnowThereforePriced : Bool := true
  poorGarbCarriesJade : Bool := true
  knowNotKnowingHighest : Bool := true
  falseKnowingDisease : Bool := true
  knowsWithoutParading : Bool := true
  selfLoveWithoutDisplay : Bool := true
deriving Repr, DecidableEq

/-- Chapters 73-79: hard enforcement, hard strength, and forced reconciliation leave residue. -/
structure HardnessCounterproofs where
  heavenOvercomesWithoutStriving : Bool := true
  quietPlansEffective : Bool := true
  deathPunishmentUsurpsOffice : Bool := true
  taxesMakeFamine : Bool := true
  excessiveAgencyMakesUngovernable : Bool := true
  strengthConcomitantDeath : Bool := true
  waterSoftOvercomesHard : Bool := true
  trueWordsSeemParadoxical : Bool := true
  reconciliationLeavesGrudge : Bool := true
  heavenWithoutPartiality : Bool := true
deriving Repr, DecidableEq

/-- Chapters 80-81: the final witness favors local sufficiency and non-accumulation. -/
structure SmallStateClosing where
  smallStateSmallPopulation : Bool := true
  weaponsUnused : Bool := true
  returnKnottedCords : Bool := true
  simpleFoodClothesDwellingEnjoyed : Bool := true
  noCompulsiveIntercourse : Bool := true
  sincereWordsNotFine : Bool := true
  skilledDoNotDispute : Bool := true
  sageDoesNotAccumulate : Bool := true
  givesMoreHasMore : Bool := true
  heavenInjuresNot : Bool := true
  sageDoesNotStrive : Bool := true
deriving Repr, DecidableEq

def hiddenJadeNonKnowledge : HiddenJadeNonKnowledge := {}

def hardnessCounterproofs : HardnessCounterproofs := {}

def smallStateClosing : SmallStateClosing := {}

theorem tao_hidden_jade_non_knowledge :
    hiddenJadeNonKnowledge.easyWordsRarelyPracticed = true ∧
      hiddenJadeNonKnowledge.fewKnowThereforePriced = true ∧
      hiddenJadeNonKnowledge.poorGarbCarriesJade = true ∧
      hiddenJadeNonKnowledge.knowNotKnowingHighest = true ∧
      hiddenJadeNonKnowledge.falseKnowingDisease = true ∧
      hiddenJadeNonKnowledge.knowsWithoutParading = true ∧
      hiddenJadeNonKnowledge.selfLoveWithoutDisplay = true := by
  simp [hiddenJadeNonKnowledge]

theorem tao_hardness_counterproofs :
    hardnessCounterproofs.heavenOvercomesWithoutStriving = true ∧
      hardnessCounterproofs.quietPlansEffective = true ∧
      hardnessCounterproofs.deathPunishmentUsurpsOffice = true ∧
      hardnessCounterproofs.taxesMakeFamine = true ∧
      hardnessCounterproofs.excessiveAgencyMakesUngovernable = true ∧
      hardnessCounterproofs.strengthConcomitantDeath = true ∧
      hardnessCounterproofs.waterSoftOvercomesHard = true ∧
      hardnessCounterproofs.trueWordsSeemParadoxical = true ∧
      hardnessCounterproofs.reconciliationLeavesGrudge = true ∧
      hardnessCounterproofs.heavenWithoutPartiality = true := by
  simp [hardnessCounterproofs]

theorem tao_small_state_closing :
    smallStateClosing.smallStateSmallPopulation = true ∧
      smallStateClosing.weaponsUnused = true ∧
      smallStateClosing.returnKnottedCords = true ∧
      smallStateClosing.simpleFoodClothesDwellingEnjoyed = true ∧
      smallStateClosing.noCompulsiveIntercourse = true ∧
      smallStateClosing.sincereWordsNotFine = true ∧
      smallStateClosing.skilledDoNotDispute = true ∧
      smallStateClosing.sageDoesNotAccumulate = true ∧
      smallStateClosing.givesMoreHasMore = true ∧
      smallStateClosing.heavenInjuresNot = true ∧
      smallStateClosing.sageDoesNotStrive = true := by
  simp [smallStateClosing]

/--
Chapters 70-81 close the Tao Te Ching by making the negative witnesses explicit:
false knowing is disease, hard strength belongs to death, enforcement leaves
residue, and small local sufficiency beats maximal accumulation and reach.
-/
theorem tao_te_ching_closing_counterproof_witness :
    hiddenJadeNonKnowledge.knowNotKnowingHighest = true ∧
      hiddenJadeNonKnowledge.falseKnowingDisease = true ∧
      hardnessCounterproofs.waterSoftOvercomesHard = true ∧
      hardnessCounterproofs.reconciliationLeavesGrudge = true ∧
      smallStateClosing.smallStateSmallPopulation = true ∧
      smallStateClosing.sincereWordsNotFine = true ∧
      smallStateClosing.sageDoesNotStrive = true := by
  simp [hiddenJadeNonKnowledge, hardnessCounterproofs, smallStateClosing]

end Gnosis.Witnesses.Tao
