import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansNoDivisionsCrossWitness

/-!
# 1 Corinthians 1:10-17 (KJV) -- No Divisions, No Baptismal Factions

This unit gives one bounded division/cross topology:

  * the brethren are beseeched to speak the same thing;
  * there should be no divisions, but joining in same mind and judgment;
  * Chloe's household reports contentions;
  * party slogans name Paul, Apollos, Cephas, and Christ;
  * Christ is not divided, Paul was not crucified for them, and they were not
    baptized in Paul's name;
  * Christ sent Paul to preach the gospel, not with wisdom of words, lest the
    cross of Christ be made of none effect.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- 1 Corinthians 1:10-17 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def first_corinthians_1_10_17_quote : String :=
  "1:10 Now I beseech you, brethren, by the name of our Lord Jesus " ++
  "Christ, that ye all speak the same thing, and that there be no " ++
  "divisions among you; but that ye be perfectly joined together in the " ++
  "same mind and in the same judgment. 1:11 For it hath been declared " ++
  "unto me of you, my brethren, by them which are of the house of Chloe, " ++
  "that there are contentions among you. 1:12 Now this I say, that every " ++
  "one of you saith, I am of Paul; and I of Apollos; and I of Cephas; " ++
  "and I of Christ. 1:13 Is Christ divided? was Paul crucified for you? " ++
  "or were ye baptized in the name of Paul? 1:14 I thank God that I " ++
  "baptized none of you, but Crispus and Gaius; 1:15 Lest any should " ++
  "say that I had baptized in mine own name. 1:16 And I baptized also " ++
  "the household of Stephanas: besides, I know not whether I baptized " ++
  "any other. 1:17 For Christ sent me not to baptize, but to preach the " ++
  "gospel: not with wisdom of words, lest the cross of Christ should be " ++
  "made of none effect."

/-! ## Section 1: Appeal against divisions -/

/-- The unity appeal in 1 Corinthians 1:10. -/
structure UnityAppeal where
  beseechByNameOfChrist : Bool
  speakSameThing : Bool
  noDivisions : Bool
  joinedSameMind : Bool
  joinedSameJudgment : Bool
deriving DecidableEq, Repr

/-- The appeal seeks no divisions and shared mind/judgment. -/
def unityAppeal : UnityAppeal where
  beseechByNameOfChrist := true
  speakSameThing := true
  noDivisions := true
  joinedSameMind := true
  joinedSameJudgment := true

/-! ## Section 2: Reported factions -/

/-- The reported contention and slogans in 1 Corinthians 1:11-12. -/
structure FactionReport where
  chloeHouseholdDeclaredContentions : Bool
  saysIAmOfPaul : Bool
  saysIAmOfApollos : Bool
  saysIAmOfCephas : Bool
  saysIAmOfChrist : Bool
deriving DecidableEq, Repr

/-- Chloe's report names contentions and the faction slogans. -/
def factionReport : FactionReport where
  chloeHouseholdDeclaredContentions := true
  saysIAmOfPaul := true
  saysIAmOfApollos := true
  saysIAmOfCephas := true
  saysIAmOfChrist := true

/-! ## Section 3: Baptism and cross -/

/-- The baptism/cross correction in 1 Corinthians 1:13-17. -/
structure BaptismCrossCorrection where
  christNotDivided : Bool
  paulNotCrucifiedForYou : Bool
  notBaptizedInNameOfPaul : Bool
  paulNotSentToBaptizeButPreach : Bool
  notWithWisdomOfWords : Bool
  crossNotMadeNoneEffect : Bool
deriving DecidableEq, Repr

/-- Baptismal factionalism is rejected so the cross is not emptied. -/
def baptismCrossCorrection : BaptismCrossCorrection where
  christNotDivided := true
  paulNotCrucifiedForYou := true
  notBaptizedInNameOfPaul := true
  paulNotSentToBaptizeButPreach := true
  notWithWisdomOfWords := true
  crossNotMadeNoneEffect := true

/-! ## Section 4: Master witness -/

/-- The bounded 1 Corinthians 1:10-17 witness. -/
theorem first_corinthians_no_divisions_cross_witness :
    unityAppeal.beseechByNameOfChrist = true
    ∧ unityAppeal.speakSameThing = true
    ∧ unityAppeal.noDivisions = true
    ∧ unityAppeal.joinedSameMind = true
    ∧ unityAppeal.joinedSameJudgment = true
    ∧ factionReport.chloeHouseholdDeclaredContentions = true
    ∧ factionReport.saysIAmOfPaul = true
    ∧ factionReport.saysIAmOfApollos = true
    ∧ factionReport.saysIAmOfCephas = true
    ∧ factionReport.saysIAmOfChrist = true
    ∧ baptismCrossCorrection.christNotDivided = true
    ∧ baptismCrossCorrection.paulNotCrucifiedForYou = true
    ∧ baptismCrossCorrection.notBaptizedInNameOfPaul = true
    ∧ baptismCrossCorrection.paulNotSentToBaptizeButPreach = true
    ∧ baptismCrossCorrection.notWithWisdomOfWords = true
    ∧ baptismCrossCorrection.crossNotMadeNoneEffect = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rfl

end FirstCorinthiansNoDivisionsCrossWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
