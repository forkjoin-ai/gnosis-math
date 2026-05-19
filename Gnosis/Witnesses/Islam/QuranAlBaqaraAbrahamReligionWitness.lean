import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraAbrahamReligionWitness

/-!
# Quran 2:130, Al-Baqara -- Abraham's Religion

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1377-1378`.

This bounded witness tracks the single-verse boundary claim:

  * forsaking Abraham's religion is named folly;
  * Abraham is chosen in this world;
  * Abraham ranks among the righteous in the Hereafter.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive AbrahamReligionMoment
  | forsakingNamedFolly
  | chosenInWorld
  | righteousInHereafter
deriving DecidableEq, Repr

def abrahamReligionMoments : List AbrahamReligionMoment :=
  [ AbrahamReligionMoment.forsakingNamedFolly
  , AbrahamReligionMoment.chosenInWorld
  , AbrahamReligionMoment.righteousInHereafter
  ]

structure AbrahamReligionPattern where
  religionOfAbrahamNamed : Bool
  forsakingQuestioned : Bool
  foolishnessNamed : Bool
  chosenInThisWorld : Bool
  righteousInHereafter : Bool
deriving DecidableEq, Repr

def abrahamReligionPattern : AbrahamReligionPattern where
  religionOfAbrahamNamed := true
  forsakingQuestioned := true
  foolishnessNamed := true
  chosenInThisWorld := true
  righteousInHereafter := true

theorem quran_al_baqara_abraham_religion_witness :
    abrahamReligionMoments.length = 3
    ∧ abrahamReligionMoments.head? = some AbrahamReligionMoment.forsakingNamedFolly
    ∧ abrahamReligionMoments.getLast? = some AbrahamReligionMoment.righteousInHereafter
    ∧ abrahamReligionPattern.religionOfAbrahamNamed = true
    ∧ abrahamReligionPattern.forsakingQuestioned = true
    ∧ abrahamReligionPattern.foolishnessNamed = true
    ∧ abrahamReligionPattern.chosenInThisWorld = true
    ∧ abrahamReligionPattern.righteousInHereafter = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end QuranAlBaqaraAbrahamReligionWitness
end Gnosis.Witnesses.Islam
