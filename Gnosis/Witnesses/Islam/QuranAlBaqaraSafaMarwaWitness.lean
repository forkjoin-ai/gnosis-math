import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraSafaMarwaWitness

/-!
# Quran 2:158, Al-Baqara -- Safa and Marwa

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1487-1490`.

This bounded witness tracks the Safa and Marwa rite:

  * Safa and Marwa are among God's rites;
  * major and minor pilgrimage to the House are named;
  * circulating between the two is no offence;
  * voluntary good is rewarded;
  * God rewards good deeds and knows everything.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive SafaMarwaMoment
  | ritesOfGod
  | pilgrimageToHouse
  | circulationPermitted
  | voluntaryGood
  | rewardAndKnowledge
deriving DecidableEq, Repr

def safaMarwaMoments : List SafaMarwaMoment :=
  [ SafaMarwaMoment.ritesOfGod
  , SafaMarwaMoment.pilgrimageToHouse
  , SafaMarwaMoment.circulationPermitted
  , SafaMarwaMoment.voluntaryGood
  , SafaMarwaMoment.rewardAndKnowledge
  ]

structure SafaMarwaPattern where
  safaNamed : Bool
  marwaNamed : Bool
  ritesOfGod : Bool
  majorPilgrimageNamed : Bool
  minorPilgrimageNamed : Bool
  houseNamed : Bool
  circulationNoOffence : Bool
  voluntaryGoodRewarded : Bool
  godRewardsGoodDeeds : Bool
  godKnowsEverything : Bool
deriving DecidableEq, Repr

def safaMarwaPattern : SafaMarwaPattern where
  safaNamed := true
  marwaNamed := true
  ritesOfGod := true
  majorPilgrimageNamed := true
  minorPilgrimageNamed := true
  houseNamed := true
  circulationNoOffence := true
  voluntaryGoodRewarded := true
  godRewardsGoodDeeds := true
  godKnowsEverything := true

theorem quran_al_baqara_safa_marwa_witness :
    safaMarwaMoments.length = 5
    ∧ safaMarwaMoments.head? = some SafaMarwaMoment.ritesOfGod
    ∧ safaMarwaMoments.getLast? = some SafaMarwaMoment.rewardAndKnowledge
    ∧ safaMarwaPattern.safaNamed = true
    ∧ safaMarwaPattern.marwaNamed = true
    ∧ safaMarwaPattern.ritesOfGod = true
    ∧ safaMarwaPattern.majorPilgrimageNamed = true
    ∧ safaMarwaPattern.minorPilgrimageNamed = true
    ∧ safaMarwaPattern.houseNamed = true
    ∧ safaMarwaPattern.circulationNoOffence = true
    ∧ safaMarwaPattern.voluntaryGoodRewarded = true
    ∧ safaMarwaPattern.godRewardsGoodDeeds = true
    ∧ safaMarwaPattern.godKnowsEverything = true := by
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

end QuranAlBaqaraSafaMarwaWitness
end Gnosis.Witnesses.Islam
