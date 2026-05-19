import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlFatihaOpeningWitness

/-!
# Quran 1, Al-Fatiha -- The Opening

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:879-889`.

This bounded witness tracks Abdel Haleem's translation of Al-Fatiha:

  * invocation in the name of God, Lord of Mercy, Giver of Mercy;
  * praise belongs to God, Lord of the Worlds;
  * God is Lord/Giver of Mercy and Master of the Day of Judgement;
  * worship and help are directed to God alone;
  * guidance is requested to the straight path;
  * the path is distinguished from anger and straying.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-- The seven opening movements in source order. -/
inductive AlFatihaMovement
  | nameOfGodMercy
  | praiseLordWorlds
  | mercyRepeated
  | masterJudgement
  | worshipAndHelp
  | guideStraightPath
  | blessedNotAngerNorAstray
deriving DecidableEq, Repr

/-- Al-Fatiha's movements in source order. -/
def alFatihaMovements : List AlFatihaMovement :=
  [ AlFatihaMovement.nameOfGodMercy
  , AlFatihaMovement.praiseLordWorlds
  , AlFatihaMovement.mercyRepeated
  , AlFatihaMovement.masterJudgement
  , AlFatihaMovement.worshipAndHelp
  , AlFatihaMovement.guideStraightPath
  , AlFatihaMovement.blessedNotAngerNorAstray
  ]

/-- Invocation and praise features in verses 1-4. -/
structure OpeningPraisePattern where
  nameOfGod : Bool
  lordOfMercy : Bool
  giverOfMercy : Bool
  praiseBelongsToGod : Bool
  lordOfWorlds : Bool
  masterDayJudgement : Bool
deriving DecidableEq, Repr

def openingPraisePattern : OpeningPraisePattern where
  nameOfGod := true
  lordOfMercy := true
  giverOfMercy := true
  praiseBelongsToGod := true
  lordOfWorlds := true
  masterDayJudgement := true

/-- Worship, help, and guidance features in verses 5-7. -/
structure WorshipGuidancePattern where
  youWeWorship : Bool
  youWeAskHelp : Bool
  guideStraightPath : Bool
  pathOfBlessed : Bool
  notAnger : Bool
  notAstray : Bool
deriving DecidableEq, Repr

def worshipGuidancePattern : WorshipGuidancePattern where
  youWeWorship := true
  youWeAskHelp := true
  guideStraightPath := true
  pathOfBlessed := true
  notAnger := true
  notAstray := true

/-- The bounded Quran 1 / Al-Fatiha witness. -/
theorem quran_al_fatiha_opening_witness :
    alFatihaMovements.length = 7
    ∧ alFatihaMovements.head? = some AlFatihaMovement.nameOfGodMercy
    ∧ alFatihaMovements.getLast? = some AlFatihaMovement.blessedNotAngerNorAstray
    ∧ openingPraisePattern.nameOfGod = true
    ∧ openingPraisePattern.lordOfMercy = true
    ∧ openingPraisePattern.giverOfMercy = true
    ∧ openingPraisePattern.praiseBelongsToGod = true
    ∧ openingPraisePattern.lordOfWorlds = true
    ∧ openingPraisePattern.masterDayJudgement = true
    ∧ worshipGuidancePattern.youWeWorship = true
    ∧ worshipGuidancePattern.youWeAskHelp = true
    ∧ worshipGuidancePattern.guideStraightPath = true
    ∧ worshipGuidancePattern.pathOfBlessed = true
    ∧ worshipGuidancePattern.notAnger = true
    ∧ worshipGuidancePattern.notAstray = true := by
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

end QuranAlFatihaOpeningWitness
end Gnosis.Witnesses.Islam
