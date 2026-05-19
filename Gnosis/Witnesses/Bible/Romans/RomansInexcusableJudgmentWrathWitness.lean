import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansInexcusableJudgmentWrathWitness

/-!
# Romans 2:1-5 (KJV) -- Inexcusable Judgment and Stored Wrath

This unit follows the first judgment turn after Romans 1:

  * the judge is inexcusable because he does the same things;
  * God's judgment is according to truth;
  * the hypocritical judge does not escape judgment;
  * despising goodness, forbearance, and longsuffering misses repentance;
  * hardness and impenitence store wrath against the day of righteous judgment.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 2:1-5 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_2_1_5_quote : String :=
  "2:1 Therefore thou art inexcusable, O man, whosoever thou art that " ++
  "judgest: for wherein thou judgest another, thou condemnest thyself; " ++
  "for thou that judgest doest the same things. 2:2 But we are sure " ++
  "that the judgment of God is according to truth against them which " ++
  "commit such things. 2:3 And thinkest thou this, O man, that judgest " ++
  "them which do such things, and doest the same, that thou shalt escape " ++
  "the judgment of God? 2:4 Or despisest thou the riches of his goodness " ++
  "and forbearance and longsuffering; not knowing that the goodness of " ++
  "God leadeth thee to repentance? 2:5 But after thy hardness and " ++
  "impenitent heart treasurest up unto thyself wrath against the day of " ++
  "wrath and revelation of the righteous judgment of God;"

/-! ## Section 1: Inexcusable judging -/

/-- The self-condemnation pattern in Romans 2:1. -/
structure InexcusableJudgmentPattern where
  judgesAnother : Bool
  condemnsSelf : Bool
  doesSameThings : Bool
  isInexcusable : Bool
deriving DecidableEq, Repr

/-- Judging another while doing the same things makes the judge inexcusable. -/
def inexcusableJudgmentPattern : InexcusableJudgmentPattern where
  judgesAnother := true
  condemnsSelf := true
  doesSameThings := true
  isInexcusable := true

/-- The inexcusable judge condemns himself while doing the same things. -/
theorem inexcusable_judge_condemns_self :
    inexcusableJudgmentPattern.judgesAnother = true
    ∧ inexcusableJudgmentPattern.condemnsSelf = true
    ∧ inexcusableJudgmentPattern.doesSameThings = true
    ∧ inexcusableJudgmentPattern.isInexcusable = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 2: Judgment according to truth -/

/-- The truth-standard and non-escape pattern in Romans 2:2-3. -/
structure TruthJudgmentPattern where
  judgmentOfGodAccordingToTruth : Bool
  againstCommittersOfSuchThings : Bool
  hypocriticalJudgeDoesSame : Bool
  hypocriticalJudgeDoesNotEscape : Bool
deriving DecidableEq, Repr

/-- God's judgment is according to truth and the same-doing judge does not escape. -/
def truthJudgmentPattern : TruthJudgmentPattern where
  judgmentOfGodAccordingToTruth := true
  againstCommittersOfSuchThings := true
  hypocriticalJudgeDoesSame := true
  hypocriticalJudgeDoesNotEscape := true

/-- Judgment is according to truth against those committing such things. -/
theorem judgment_according_to_truth :
    truthJudgmentPattern.judgmentOfGodAccordingToTruth = true
    ∧ truthJudgmentPattern.againstCommittersOfSuchThings = true := by
  exact ⟨rfl, rfl⟩

/-- The same-doing judge does not escape the judgment of God. -/
theorem same_doing_judge_does_not_escape :
    truthJudgmentPattern.hypocriticalJudgeDoesSame = true
    ∧ truthJudgmentPattern.hypocriticalJudgeDoesNotEscape = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 3: Goodness, repentance, and stored wrath -/

/-- The repentance and wrath pattern in Romans 2:4-5. -/
structure RepentanceWrathPattern where
  despisesGoodnessForbearanceLongsuffering : Bool
  goodnessLeadsToRepentance : Bool
  hardnessAndImpenitentHeart : Bool
  storesWrathForRighteousJudgment : Bool
deriving DecidableEq, Repr

/-- Goodness leads toward repentance; hardness stores wrath. -/
def repentanceWrathPattern : RepentanceWrathPattern where
  despisesGoodnessForbearanceLongsuffering := true
  goodnessLeadsToRepentance := true
  hardnessAndImpenitentHeart := true
  storesWrathForRighteousJudgment := true

/-- Despising divine patience misses its repentance-directed function. -/
theorem goodness_leads_to_repentance :
    repentanceWrathPattern.despisesGoodnessForbearanceLongsuffering = true
    ∧ repentanceWrathPattern.goodnessLeadsToRepentance = true := by
  exact ⟨rfl, rfl⟩

/-- Hardness and impenitence store wrath against righteous judgment. -/
theorem hardness_stores_wrath :
    repentanceWrathPattern.hardnessAndImpenitentHeart = true
    ∧ repentanceWrathPattern.storesWrathForRighteousJudgment = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 4: Master witness -/

/-- The bounded Romans 2:1-5 witness. -/
theorem romans_inexcusable_judgment_wrath_witness :
    inexcusableJudgmentPattern.judgesAnother = true
    ∧ inexcusableJudgmentPattern.condemnsSelf = true
    ∧ inexcusableJudgmentPattern.doesSameThings = true
    ∧ inexcusableJudgmentPattern.isInexcusable = true
    ∧ truthJudgmentPattern.judgmentOfGodAccordingToTruth = true
    ∧ truthJudgmentPattern.againstCommittersOfSuchThings = true
    ∧ truthJudgmentPattern.hypocriticalJudgeDoesSame = true
    ∧ truthJudgmentPattern.hypocriticalJudgeDoesNotEscape = true
    ∧ repentanceWrathPattern.despisesGoodnessForbearanceLongsuffering = true
    ∧ repentanceWrathPattern.goodnessLeadsToRepentance = true
    ∧ repentanceWrathPattern.hardnessAndImpenitentHeart = true
    ∧ repentanceWrathPattern.storesWrathForRighteousJudgment = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end RomansInexcusableJudgmentWrathWitness
end Gnosis.Witnesses.Bible.Romans
