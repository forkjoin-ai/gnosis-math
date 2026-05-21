import Gnosis.GreekLogicCanon.SyllogisticLogic

/-!
# Question Vacuums

Init-only formalization of questions as typed open slots in an inference
topology. Assertions close a topology by supplying all required witnesses.
Questions keep the boundary fixed and mark the missing witness as a typed
vacuum that can later be filled or rejected.
-/

namespace Gnosis.GreekLogicCanon.QuestionVacuum

universe u

open Gnosis.GreekLogicCanon.SyllogisticLogic

inductive HoleKind where
  | truth
  | term
  | rule
deriving DecidableEq, Repr

inductive HoleSlot where
  | premise
  | conclusion
  | witness
  | connector
deriving DecidableEq, Repr

inductive HoleState where
  | open
  | filled
  | rejected
deriving DecidableEq, Repr

inductive QuestionFormat where
  | truthPremise
  | truthConclusion
  | truthWitness
  | truthConnector
  | termPremise
  | termConclusion
  | termWitness
  | termConnector
  | rulePremise
  | ruleConclusion
  | ruleWitness
  | ruleConnector
deriving DecidableEq, Repr

inductive PrecisionQACategory where
  | focus
  | clarification
  | assumptions
  | evidence
  | causes
  | effects
  | action
deriving DecidableEq, Repr

inductive PrecisionQASubcategory where
  | mentalEcology
  | motivation
  | participation
  | communicationChannel
  | discussionDirection
  | ambiguity
  | vagueness
  | slipperyTerms
  | mentalGraph
  | mentalPivotTable
  | difficultConcepts
  | existence
  | uniqueness
  | measurement
  | possibility
  | value
  | category
  | similarity
  | timeConstancy
  | audience
  | credibilityOfSource
  | weighingReasons
  | sampling
  | dataCollection
  | dataAnalysis
  | sequenceOfEvents
  | triggerCondition
  | mechanism
  | rootCauseAnalysis
  | driverInhibitor
  | nonLinearCausality
  | stakeholders
  | timeSpan
  | multipleScenarios
  | unintendedConsequences
  | indicators
  | riskAssessment
  | accountability
  | containmentVsPrevention
  | goalAnalysis
  | planning
  | riskManagement
deriving DecidableEq, Repr

def QuestionFormat.kind : QuestionFormat -> HoleKind
  | .truthPremise => .truth
  | .truthConclusion => .truth
  | .truthWitness => .truth
  | .truthConnector => .truth
  | .termPremise => .term
  | .termConclusion => .term
  | .termWitness => .term
  | .termConnector => .term
  | .rulePremise => .rule
  | .ruleConclusion => .rule
  | .ruleWitness => .rule
  | .ruleConnector => .rule

def QuestionFormat.slot : QuestionFormat -> HoleSlot
  | .truthPremise => .premise
  | .truthConclusion => .conclusion
  | .truthWitness => .witness
  | .truthConnector => .connector
  | .termPremise => .premise
  | .termConclusion => .conclusion
  | .termWitness => .witness
  | .termConnector => .connector
  | .rulePremise => .premise
  | .ruleConclusion => .conclusion
  | .ruleWitness => .witness
  | .ruleConnector => .connector

def PrecisionQACategory.questionFormat : PrecisionQACategory -> QuestionFormat
  | .focus => .ruleConnector
  | .clarification => .termWitness
  | .assumptions => .truthPremise
  | .evidence => .truthWitness
  | .causes => .ruleConnector
  | .effects => .truthConclusion
  | .action => .ruleConclusion

def PrecisionQASubcategory.qaCategory : PrecisionQASubcategory -> PrecisionQACategory
  | .mentalEcology => .focus
  | .motivation => .focus
  | .participation => .focus
  | .communicationChannel => .focus
  | .discussionDirection => .focus
  | .ambiguity => .clarification
  | .vagueness => .clarification
  | .slipperyTerms => .clarification
  | .mentalGraph => .clarification
  | .mentalPivotTable => .clarification
  | .difficultConcepts => .clarification
  | .existence => .assumptions
  | .uniqueness => .assumptions
  | .measurement => .assumptions
  | .possibility => .assumptions
  | .value => .assumptions
  | .category => .assumptions
  | .similarity => .assumptions
  | .timeConstancy => .assumptions
  | .audience => .assumptions
  | .credibilityOfSource => .evidence
  | .weighingReasons => .evidence
  | .sampling => .evidence
  | .dataCollection => .evidence
  | .dataAnalysis => .evidence
  | .sequenceOfEvents => .causes
  | .triggerCondition => .causes
  | .mechanism => .causes
  | .rootCauseAnalysis => .causes
  | .driverInhibitor => .causes
  | .nonLinearCausality => .causes
  | .stakeholders => .effects
  | .timeSpan => .effects
  | .multipleScenarios => .effects
  | .unintendedConsequences => .effects
  | .indicators => .effects
  | .riskAssessment => .effects
  | .accountability => .action
  | .containmentVsPrevention => .action
  | .goalAnalysis => .action
  | .planning => .action
  | .riskManagement => .action

def PrecisionQASubcategory.questionFormat
    (subcategory : PrecisionQASubcategory) :
    QuestionFormat :=
  subcategory.qaCategory.questionFormat

def questionFormats : List QuestionFormat :=
  [ .truthPremise
  , .truthConclusion
  , .truthWitness
  , .truthConnector
  , .termPremise
  , .termConclusion
  , .termWitness
  , .termConnector
  , .rulePremise
  , .ruleConclusion
  , .ruleWitness
  , .ruleConnector
  ]

def questionFormatCount : Nat :=
  questionFormats.length

theorem questionFormatCount_eq_twelve :
    questionFormatCount = 12 := by
  rfl

def questionStates : List HoleState :=
  [ .open, .filled, .rejected ]

def questionStateCount : Nat :=
  questionStates.length

theorem questionStateCount_eq_three :
    questionStateCount = 3 := by
  rfl

def precisionQACategories : List PrecisionQACategory :=
  [ .focus
  , .clarification
  , .assumptions
  , .evidence
  , .causes
  , .effects
  , .action
  ]

def precisionQACategoryCount : Nat :=
  precisionQACategories.length

theorem precisionQACategoryCount_eq_seven :
    precisionQACategoryCount = 7 := by
  rfl

def precisionQASubcategories : List PrecisionQASubcategory :=
  [ .mentalEcology
  , .motivation
  , .participation
  , .communicationChannel
  , .discussionDirection
  , .ambiguity
  , .vagueness
  , .slipperyTerms
  , .mentalGraph
  , .mentalPivotTable
  , .difficultConcepts
  , .existence
  , .uniqueness
  , .measurement
  , .possibility
  , .value
  , .category
  , .similarity
  , .timeConstancy
  , .audience
  , .credibilityOfSource
  , .weighingReasons
  , .sampling
  , .dataCollection
  , .dataAnalysis
  , .sequenceOfEvents
  , .triggerCondition
  , .mechanism
  , .rootCauseAnalysis
  , .driverInhibitor
  , .nonLinearCausality
  , .stakeholders
  , .timeSpan
  , .multipleScenarios
  , .unintendedConsequences
  , .indicators
  , .riskAssessment
  , .accountability
  , .containmentVsPrevention
  , .goalAnalysis
  , .planning
  , .riskManagement
  ]

def precisionQASubcategoryCount : Nat :=
  precisionQASubcategories.length

theorem precisionQASubcategoryCount_eq_fortyTwo :
    precisionQASubcategoryCount = 42 := by
  rfl

structure PrecisionQAQuestionFormat where
  category : PrecisionQACategory
  format : QuestionFormat
deriving Repr

structure PrecisionQASubcategoryQuestionFormat where
  subcategory : PrecisionQASubcategory
  category : PrecisionQACategory
  format : QuestionFormat
deriving Repr

def precisionQAQuestionFormats : List PrecisionQAQuestionFormat :=
  precisionQACategories.map fun category =>
    { category, format := category.questionFormat }

def precisionQAQuestionFormatCount : Nat :=
  precisionQAQuestionFormats.length

theorem precisionQAQuestionFormatCount_eq_seven :
    precisionQAQuestionFormatCount = 7 := by
  rfl

def precisionQASubcategoryQuestionFormats :
    List PrecisionQASubcategoryQuestionFormat :=
  precisionQASubcategories.map fun subcategory =>
    { subcategory
    , category := subcategory.qaCategory
    , format := subcategory.questionFormat
    }

def precisionQASubcategoryQuestionFormatCount : Nat :=
  precisionQASubcategoryQuestionFormats.length

theorem precisionQASubcategoryQuestionFormatCount_eq_fortyTwo :
    precisionQASubcategoryQuestionFormatCount = 42 := by
  rfl

inductive SyllogisticOpenSlot where
  | major
  | minor
  | conclusion
  | existentialImport
deriving DecidableEq, Repr

structure SyllogisticQuestionFormat where
  syllogism : SyllogismSignature
  openSlot : SyllogisticOpenSlot
deriving Repr

def unconditionalSyllogisticOpenSlots : List SyllogisticOpenSlot :=
  [ .major, .minor, .conclusion ]

def conditionalSyllogisticOpenSlots : List SyllogisticOpenSlot :=
  [ .major, .minor, .conclusion, .existentialImport ]

def syllogisticQuestionFormatsFor
    (openSlots : List SyllogisticOpenSlot)
    (syllogism : SyllogismSignature) :
    List SyllogisticQuestionFormat :=
  openSlots.map fun openSlot => { syllogism, openSlot }

def unconditionalSyllogisticQuestionFormats :
    List SyllogisticQuestionFormat :=
  List.flatMap
    (syllogisticQuestionFormatsFor unconditionalSyllogisticOpenSlots)
    unconditionallyValidSyllogisms

def conditionalSyllogisticQuestionFormats :
    List SyllogisticQuestionFormat :=
  List.flatMap
    (syllogisticQuestionFormatsFor conditionalSyllogisticOpenSlots)
    conditionallyValidSyllogisms

def syllogisticSingleHoleQuestionFormats :
    List SyllogisticQuestionFormat :=
  unconditionalSyllogisticQuestionFormats ++
    conditionalSyllogisticQuestionFormats

def unconditionalSyllogisticQuestionFormatCount : Nat :=
  unconditionalSyllogisticQuestionFormats.length

def conditionalSyllogisticQuestionFormatCount : Nat :=
  conditionalSyllogisticQuestionFormats.length

def syllogisticSingleHoleQuestionFormatCount : Nat :=
  syllogisticSingleHoleQuestionFormats.length

theorem unconditionalSyllogisticQuestionFormatCount_eq_fortyFive :
    unconditionalSyllogisticQuestionFormatCount = 45 := by
  rfl

theorem conditionalSyllogisticQuestionFormatCount_eq_thirtySix :
    conditionalSyllogisticQuestionFormatCount = 36 := by
  rfl

theorem syllogisticSingleHoleQuestionFormatCount_eq_eightyOne :
    syllogisticSingleHoleQuestionFormatCount = 81 := by
  rfl

structure QuestionTag where
  format : QuestionFormat
  state : HoleState
deriving Repr

def QuestionTag.kind (tag : QuestionTag) : HoleKind :=
  tag.format.kind

def QuestionTag.slot (tag : QuestionTag) : HoleSlot :=
  tag.format.slot

structure QuestionVacuum (Answer : Sort u) where
  boundary : Prop
  admissible : Answer -> Prop

structure TaggedQuestionVacuum (Answer : Sort u) extends QuestionVacuum Answer where
  tag : QuestionTag

def Open {Answer : Sort u} (question : QuestionVacuum Answer) : Prop :=
  question.boundary

def Filled {Answer : Sort u} (question : QuestionVacuum Answer) : Prop :=
  question.boundary ∧ ∃ answer, question.admissible answer

def Rejected {Answer : Sort u} (question : QuestionVacuum Answer) : Prop :=
  question.boundary ∧ ¬ ∃ answer, question.admissible answer

theorem filled_has_boundary {Answer : Sort u}
    {question : QuestionVacuum Answer}
    (filled : Filled question) :
    Open question := by
  exact filled.left

theorem filled_has_admissible_answer {Answer : Sort u}
    {question : QuestionVacuum Answer}
    (filled : Filled question) :
    ∃ answer, question.admissible answer := by
  exact filled.right

def truthQuestion (P : Prop) : QuestionVacuum P where
  boundary := True
  admissible := fun _ => True

theorem truthQuestion_filled {P : Prop}
    (proof : P) :
    Filled (truthQuestion P) := by
  exact And.intro True.intro (Exists.intro proof True.intro)

theorem truthQuestion_answer {P : Prop}
    (filled : Filled (truthQuestion P)) :
    P := by
  cases filled.right with
  | intro proof _ => exact proof

def termQuestion {α : Type u}
    (predicate : α -> Prop) :
    QuestionVacuum α where
  boundary := True
  admissible := predicate

theorem termQuestion_filled {α : Type u}
    {predicate : α -> Prop}
    (witness : α)
    (certificate : predicate witness) :
    Filled (termQuestion predicate) := by
  exact And.intro True.intro (Exists.intro witness certificate)

theorem termQuestion_answer {α : Type u}
    {predicate : α -> Prop}
    (filled : Filled (termQuestion predicate)) :
    ∃ witness, predicate witness := by
  exact filled.right

def conclusionQuestion (Premise Conclusion : Prop) :
    QuestionVacuum Conclusion where
  boundary := Premise ∧ (Premise -> Conclusion)
  admissible := fun _ => True

theorem conclusionQuestion_filled {Premise Conclusion : Prop}
    (premise : Premise)
    (rule : Premise -> Conclusion) :
    Filled (conclusionQuestion Premise Conclusion) := by
  exact
    And.intro
      (And.intro premise rule)
      (Exists.intro (rule premise) True.intro)

theorem conclusionQuestion_answer {Premise Conclusion : Prop}
    (filled : Filled (conclusionQuestion Premise Conclusion)) :
    Conclusion := by
  cases filled.right with
  | intro conclusion _ => exact conclusion

def premiseQuestion (Premise Conclusion : Prop) :
    QuestionVacuum Premise where
  boundary := Premise -> Conclusion
  admissible := fun _ => True

theorem premiseQuestion_closes {Premise Conclusion : Prop}
    (filled : Filled (premiseQuestion Premise Conclusion)) :
    Conclusion := by
  cases filled.right with
  | intro premise _ => exact filled.left premise

def ruleQuestion (Premise Conclusion : Prop) :
    QuestionVacuum (Premise -> Conclusion) where
  boundary := Premise
  admissible := fun _ => True

theorem ruleQuestion_closes {Premise Conclusion : Prop}
    (filled : Filled (ruleQuestion Premise Conclusion)) :
    Conclusion := by
  cases filled.right with
  | intro rule _ => exact rule filled.left

def openConclusionTag : QuestionTag where
  format := .truthConclusion
  state := .open

def openPremiseTag : QuestionTag where
  format := .truthPremise
  state := .open

def openRuleTag : QuestionTag where
  format := .ruleConnector
  state := .open

def taggedConclusionQuestion (Premise Conclusion : Prop) :
    TaggedQuestionVacuum Conclusion where
  boundary := (conclusionQuestion Premise Conclusion).boundary
  admissible := (conclusionQuestion Premise Conclusion).admissible
  tag := openConclusionTag

theorem taggedConclusionQuestion_filled {Premise Conclusion : Prop}
    (premise : Premise)
    (rule : Premise -> Conclusion) :
    Filled (taggedConclusionQuestion Premise Conclusion).toQuestionVacuum := by
  exact conclusionQuestion_filled premise rule

end Gnosis.GreekLogicCanon.QuestionVacuum
