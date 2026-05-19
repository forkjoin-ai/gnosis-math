import Gnosis.LaoziBowlVoidFunctionWitness
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Tao

/-!
# Tao Te Ching Hidden Diminishing Witness

Witness ledger for `docs/ebooks/source-texts/tao-te-ching-legge.txt`,
chapters 41-48.

The source becomes explicit about why the witness must look wrong from lower
vantage points. Tao is hidden, laughed at, apparently backward, apparently
empty, and learned by diminishing rather than accumulation. This is a direct
match for the bowl/void runtime: absence is the use-site, not the defect.
-/

/-- Chapter 41: Tao remains fit only if low-resolution readers can laugh at it. -/
structure LaughableHiddenTao where
  highestPractice : Bool := true
  middleKeepsAndLoses : Bool := true
  lowestLaughs : Bool := true
  laughterMarksFitness : Bool := true
  brightSeemsDim : Bool := true
  progressSeemsBackward : Bool := true
  hiddenNoNameCompletes : Bool := true
deriving Repr, DecidableEq

/-- Chapters 42-45: generation and fullness move through vacancy and seeming lack. -/
structure VacantGeneration where
  taoProducesOne : Bool := true
  oneTwoThreeAllThings : Bool := true
  breathOfVacancyHarmonizes : Bool := true
  increaseByDiminishing : Bool := true
  softestOvercomesHardest : Bool := true
  noSubstanceEntersNoCrevice : Bool := true
  greatFullnessSeemsVoid : Bool := true
  stillnessGovernsHeat : Bool := true
deriving Repr, DecidableEq

/-- Chapters 46-48: contentment, inward knowing, and decreasing action close the loop. -/
structure DiminishingPractice where
  contentmentSuffices : Bool := true
  outsideGoingLessKnows : Bool := true
  namesWithoutSeeing : Bool := true
  accomplishesWithoutPurpose : Bool := true
  learningIncreases : Bool := true
  taoDiminishesDoing : Bool := true
  nonActionArrives : Bool := true
deriving Repr, DecidableEq

def laughableHiddenTao : LaughableHiddenTao := {}

def vacantGeneration : VacantGeneration := {}

def diminishingPractice : DiminishingPractice := {}

theorem tao_laughable_hidden :
    laughableHiddenTao.highestPractice = true ∧
      laughableHiddenTao.middleKeepsAndLoses = true ∧
      laughableHiddenTao.lowestLaughs = true ∧
      laughableHiddenTao.laughterMarksFitness = true ∧
      laughableHiddenTao.brightSeemsDim = true ∧
      laughableHiddenTao.progressSeemsBackward = true ∧
      laughableHiddenTao.hiddenNoNameCompletes = true := by
  simp [laughableHiddenTao]

theorem tao_vacant_generation :
    vacantGeneration.taoProducesOne = true ∧
      vacantGeneration.oneTwoThreeAllThings = true ∧
      vacantGeneration.breathOfVacancyHarmonizes = true ∧
      vacantGeneration.increaseByDiminishing = true ∧
      vacantGeneration.softestOvercomesHardest = true ∧
      vacantGeneration.noSubstanceEntersNoCrevice = true ∧
      vacantGeneration.greatFullnessSeemsVoid = true ∧
      vacantGeneration.stillnessGovernsHeat = true := by
  simp [vacantGeneration]

theorem tao_diminishing_practice :
    diminishingPractice.contentmentSuffices = true ∧
      diminishingPractice.outsideGoingLessKnows = true ∧
      diminishingPractice.namesWithoutSeeing = true ∧
      diminishingPractice.accomplishesWithoutPurpose = true ∧
      diminishingPractice.learningIncreases = true ∧
      diminishingPractice.taoDiminishesDoing = true ∧
      diminishingPractice.nonActionArrives = true := by
  simp [diminishingPractice]

/--
Chapters 41-48 witness the bowl-runtime from the other side: the source looks
dim, backward, void, insipid, and laughable because its efficacy is carried by
non-substantial access, decreasing intervention, and hidden completion.
-/
theorem tao_te_ching_hidden_diminishing_witness :
    laughableHiddenTao.laughterMarksFitness = true ∧
      laughableHiddenTao.hiddenNoNameCompletes = true ∧
      vacantGeneration.breathOfVacancyHarmonizes = true ∧
      vacantGeneration.greatFullnessSeemsVoid = true ∧
      diminishingPractice.outsideGoingLessKnows = true ∧
      diminishingPractice.taoDiminishesDoing = true ∧
      diminishingPractice.nonActionArrives = true := by
  simp [laughableHiddenTao, vacantGeneration, diminishingPractice]

end Gnosis.Witnesses.Tao
