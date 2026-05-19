import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansLawMouthGuiltKnowledgeWitness

/-!
# Romans 3:19-20 (KJV) -- Law, Stopped Mouth, Guilt, and Knowledge of Sin

This unit gives one bounded law-function topology:

  * what the law says, it says to those under the law;
  * every mouth is stopped;
  * all the world becomes guilty before God;
  * no flesh is justified in God's sight by deeds of the law;
  * by the law is the knowledge of sin.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 3:19-20 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_3_19_20_quote : String :=
  "3:19 Now we know that what things soever the law saith, it saith to " ++
  "them who are under the law: that every mouth may be stopped, and all " ++
  "the world may become guilty before God. 3:20 Therefore by the deeds " ++
  "of the law there shall no flesh be justified in his sight: for by " ++
  "the law is the knowledge of sin."

/-! ## Section 1: Law speaks and stops mouths -/

/-- The law-speech consequence in Romans 3:19. -/
structure LawSpeechConsequence where
  lawSpeaksToUnderLaw : Bool
  everyMouthStopped : Bool
  worldGuiltyBeforeGod : Bool
deriving DecidableEq, Repr

/-- Law speech stops mouths and leaves the world guilty before God. -/
def lawSpeechConsequence : LawSpeechConsequence where
  lawSpeaksToUnderLaw := true
  everyMouthStopped := true
  worldGuiltyBeforeGod := true

/-- The law speaks to those under law and stops every mouth. -/
theorem law_speaks_to_under_law_and_stops_mouths :
    lawSpeechConsequence.lawSpeaksToUnderLaw = true
    ∧ lawSpeechConsequence.everyMouthStopped = true
    ∧ lawSpeechConsequence.worldGuiltyBeforeGod = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 2: Law deeds and knowledge of sin -/

/-- The law-deeds conclusion in Romans 3:20. -/
structure LawDeedsConclusion where
  noFleshJustifiedByLawDeeds : Bool
  inHisSight : Bool
  lawGivesKnowledgeOfSin : Bool
deriving DecidableEq, Repr

/-- No flesh is justified by law deeds; law gives knowledge of sin. -/
def lawDeedsConclusion : LawDeedsConclusion where
  noFleshJustifiedByLawDeeds := true
  inHisSight := true
  lawGivesKnowledgeOfSin := true

/-- Law deeds do not justify flesh in God's sight. -/
theorem no_flesh_justified_by_law_deeds :
    lawDeedsConclusion.noFleshJustifiedByLawDeeds = true
    ∧ lawDeedsConclusion.inHisSight = true := by
  exact ⟨rfl, rfl⟩

/-- By the law is the knowledge of sin. -/
theorem law_gives_knowledge_of_sin :
    lawDeedsConclusion.lawGivesKnowledgeOfSin = true := rfl

/-! ## Section 3: Master witness -/

/-- The bounded Romans 3:19-20 witness. -/
theorem romans_law_mouth_guilt_knowledge_witness :
    lawSpeechConsequence.lawSpeaksToUnderLaw = true
    ∧ lawSpeechConsequence.everyMouthStopped = true
    ∧ lawSpeechConsequence.worldGuiltyBeforeGod = true
    ∧ lawDeedsConclusion.noFleshJustifiedByLawDeeds = true
    ∧ lawDeedsConclusion.inHisSight = true
    ∧ lawDeedsConclusion.lawGivesKnowledgeOfSin = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end RomansLawMouthGuiltKnowledgeWitness
end Gnosis.Witnesses.Bible.Romans
