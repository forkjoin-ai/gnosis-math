import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraWorshipDirectionWitness

/-!
# Quran 2:114-115, Al-Baqara -- Worship Places and Divine Direction

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1319-1324`.

This bounded witness tracks the worship-place and divine-direction unit:

  * obstructing mention of God's name in places of worship is named wicked;
  * making such places deserted is condemned;
  * fearful entry, worldly disgrace, and Hereafter punishment are named;
  * East and West belong to God;
  * wherever one turns, there is His Face;
  * God is all pervading and all knowing.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive WorshipDirectionMoment
  | worshipObstruction
  | desertedPlaces
  | fearfulEntry
  | disgracePunishment
  | eastWestBelongToGod
  | divineFaceWhereverTurn
  | pervadingKnowing
deriving DecidableEq, Repr

def worshipDirectionMoments : List WorshipDirectionMoment :=
  [ WorshipDirectionMoment.worshipObstruction
  , WorshipDirectionMoment.desertedPlaces
  , WorshipDirectionMoment.fearfulEntry
  , WorshipDirectionMoment.disgracePunishment
  , WorshipDirectionMoment.eastWestBelongToGod
  , WorshipDirectionMoment.divineFaceWhereverTurn
  , WorshipDirectionMoment.pervadingKnowing
  ]

structure WorshipObstructionPattern where
  wickednessQuestioned : Bool
  godsNameProhibited : Bool
  worshipPlacesNamed : Bool
  desertedPlacesSought : Bool
  entryWithoutFearDenied : Bool
  disgraceInWorld : Bool
  painfulHereafterPunishment : Bool
deriving DecidableEq, Repr

def worshipObstructionPattern : WorshipObstructionPattern where
  wickednessQuestioned := true
  godsNameProhibited := true
  worshipPlacesNamed := true
  desertedPlacesSought := true
  entryWithoutFearDenied := true
  disgraceInWorld := true
  painfulHereafterPunishment := true

structure DivineDirectionPattern where
  eastBelongsToGod : Bool
  westBelongsToGod : Bool
  whereverTurnFaceThere : Bool
  allPervading : Bool
  allKnowing : Bool
deriving DecidableEq, Repr

def divineDirectionPattern : DivineDirectionPattern where
  eastBelongsToGod := true
  westBelongsToGod := true
  whereverTurnFaceThere := true
  allPervading := true
  allKnowing := true

theorem quran_al_baqara_worship_direction_witness :
    worshipDirectionMoments.length = 7
    ∧ worshipDirectionMoments.head? = some WorshipDirectionMoment.worshipObstruction
    ∧ worshipDirectionMoments.getLast? = some WorshipDirectionMoment.pervadingKnowing
    ∧ worshipObstructionPattern.godsNameProhibited = true
    ∧ worshipObstructionPattern.worshipPlacesNamed = true
    ∧ worshipObstructionPattern.desertedPlacesSought = true
    ∧ worshipObstructionPattern.disgraceInWorld = true
    ∧ worshipObstructionPattern.painfulHereafterPunishment = true
    ∧ divineDirectionPattern.eastBelongsToGod = true
    ∧ divineDirectionPattern.westBelongsToGod = true
    ∧ divineDirectionPattern.whereverTurnFaceThere = true
    ∧ divineDirectionPattern.allPervading = true
    ∧ divineDirectionPattern.allKnowing = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end QuranAlBaqaraWorshipDirectionWitness
end Gnosis.Witnesses.Islam
