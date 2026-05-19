import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansLawBoastDishonorWitness

/-!
# Romans 2:17-24 (KJV) -- Law Boast and Dishonor

This unit gives one bounded direct-address topology:

  * the addressed figure is called a Jew, rests in the law, and boasts of God;
  * he knows the will and approves excellent things from instruction in the law;
  * he claims guide, light, instructor, and teacher roles;
  * the questions turn the teaching role back on the teacher;
  * breaking the law dishonors God, and God's name is blasphemed among Gentiles.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 2:17-24 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_2_17_24_quote : String :=
  "2:17 Behold, thou art called a Jew, and restest in the law, and " ++
  "makest thy boast of God, 2:18 And knowest his will, and approvest " ++
  "the things that are more excellent, being instructed out of the law; " ++
  "2:19 And art confident that thou thyself art a guide of the blind, " ++
  "a light of them which are in darkness, 2:20 An instructor of the " ++
  "foolish, a teacher of babes, which hast the form of knowledge and " ++
  "of the truth in the law. 2:21 Thou therefore which teachest another, " ++
  "teachest thou not thyself? thou that preachest a man should not " ++
  "steal, dost thou steal? 2:22 Thou that sayest a man should not commit " ++
  "adultery, dost thou commit adultery? thou that abhorrest idols, dost " ++
  "thou commit sacrilege? 2:23 Thou that makest thy boast of the law, " ++
  "through breaking the law dishonourest thou God? 2:24 For the name of " ++
  "God is blasphemed among the Gentiles through you, as it is written."

/-! ## Section 1: Law boast posture -/

/-- The initial law-boast posture in Romans 2:17-18. -/
structure LawBoastPosture where
  calledJew : Bool
  restsInLaw : Bool
  boastsOfGod : Bool
  knowsWill : Bool
  approvesExcellentThings : Bool
  instructedOutOfLaw : Bool
deriving DecidableEq, Repr

/-- The addressed figure is positioned by law, boast, and instruction. -/
def lawBoastPosture : LawBoastPosture where
  calledJew := true
  restsInLaw := true
  boastsOfGod := true
  knowsWill := true
  approvesExcellentThings := true
  instructedOutOfLaw := true

/-- Romans 2:17-18 names law-rest, God-boast, and law instruction. -/
theorem law_boast_posture_named :
    lawBoastPosture.calledJew = true
    ∧ lawBoastPosture.restsInLaw = true
    ∧ lawBoastPosture.boastsOfGod = true
    ∧ lawBoastPosture.knowsWill = true
    ∧ lawBoastPosture.approvesExcellentThings = true
    ∧ lawBoastPosture.instructedOutOfLaw = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 2: Claimed teaching roles -/

/-- Claimed roles in Romans 2:19-20. -/
inductive ClaimedTeachingRole
  | guideOfBlind
  | lightInDarkness
  | instructorOfFoolish
  | teacherOfBabes
deriving DecidableEq, Repr

/-- Claimed teaching roles in source order. -/
def claimedTeachingRoles : List ClaimedTeachingRole :=
  [ ClaimedTeachingRole.guideOfBlind
  , ClaimedTeachingRole.lightInDarkness
  , ClaimedTeachingRole.instructorOfFoolish
  , ClaimedTeachingRole.teacherOfBabes
  ]

/-- The role-list begins with guide of the blind. -/
theorem roles_begin_with_guide_of_blind :
    claimedTeachingRoles.head? = some ClaimedTeachingRole.guideOfBlind := rfl

/-- The role-list closes with teacher of babes. -/
theorem roles_close_with_teacher_of_babes :
    claimedTeachingRoles.getLast? = some ClaimedTeachingRole.teacherOfBabes := rfl

/-! ## Section 3: Teaching turned back -/

/-- The self-indicting questions in Romans 2:21-23. -/
inductive TurnedQuestion
  | teachestNotThyself
  | preachNoStealYetSteal
  | sayNoAdulteryYetCommitAdultery
  | abhorIdolsYetCommitSacrilege
  | boastLawYetBreakLawDishonorGod
deriving DecidableEq, Repr

/-- The questions in source order. -/
def turnedQuestions : List TurnedQuestion :=
  [ TurnedQuestion.teachestNotThyself
  , TurnedQuestion.preachNoStealYetSteal
  , TurnedQuestion.sayNoAdulteryYetCommitAdultery
  , TurnedQuestion.abhorIdolsYetCommitSacrilege
  , TurnedQuestion.boastLawYetBreakLawDishonorGod
  ]

/-- The questions begin with whether the teacher teaches himself. -/
theorem questions_begin_with_self_teaching :
    turnedQuestions.head? = some TurnedQuestion.teachestNotThyself := rfl

/-- The questions close with law-boast, law-breaking, and dishonor. -/
theorem questions_close_with_dishonor :
    turnedQuestions.getLast? =
      some TurnedQuestion.boastLawYetBreakLawDishonorGod := rfl

/-! ## Section 4: Blasphemy among Gentiles -/

/-- The closing blasphemy claim in Romans 2:24. -/
structure GentileBlasphemyPattern where
  nameOfGodBlasphemedAmongGentiles : Bool
  throughYou : Bool
  asItIsWritten : Bool
deriving DecidableEq, Repr

/-- The unit closes with blasphemy among Gentiles through the addressed party. -/
def gentileBlasphemyPattern : GentileBlasphemyPattern where
  nameOfGodBlasphemedAmongGentiles := true
  throughYou := true
  asItIsWritten := true

/-- God's name is blasphemed among Gentiles through the addressed party. -/
theorem gods_name_blasphemed_among_gentiles :
    gentileBlasphemyPattern.nameOfGodBlasphemedAmongGentiles = true
    ∧ gentileBlasphemyPattern.throughYou = true
    ∧ gentileBlasphemyPattern.asItIsWritten = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 5: Master witness -/

/-- The bounded Romans 2:17-24 witness. -/
theorem romans_law_boast_dishonor_witness :
    lawBoastPosture.calledJew = true
    ∧ lawBoastPosture.restsInLaw = true
    ∧ lawBoastPosture.boastsOfGod = true
    ∧ lawBoastPosture.knowsWill = true
    ∧ lawBoastPosture.approvesExcellentThings = true
    ∧ lawBoastPosture.instructedOutOfLaw = true
    ∧ claimedTeachingRoles.length = 4
    ∧ claimedTeachingRoles.head? = some ClaimedTeachingRole.guideOfBlind
    ∧ claimedTeachingRoles.getLast? = some ClaimedTeachingRole.teacherOfBabes
    ∧ turnedQuestions.length = 5
    ∧ turnedQuestions.head? = some TurnedQuestion.teachestNotThyself
    ∧ turnedQuestions.getLast? =
      some TurnedQuestion.boastLawYetBreakLawDishonorGod
    ∧ gentileBlasphemyPattern.nameOfGodBlasphemedAmongGentiles = true
    ∧ gentileBlasphemyPattern.throughYou = true
    ∧ gentileBlasphemyPattern.asItIsWritten = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end RomansLawBoastDishonorWitness
end Gnosis.Witnesses.Bible.Romans
