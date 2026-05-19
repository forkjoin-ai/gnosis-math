import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraCloudsSignsSingleCommunityWitness

/-!
# Quran 2:210-213, Al-Baqara -- Clouds, Signs, Single Community

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1715-1739`.

This witness tracks the warning that waiting until the matter is decided is too
late, the Children of Israel's clear signs and altered blessings, worldly glamour
mocking believers, and mankind's single community divided after Scripture came
with truth until God guides believers to the truth by His leave.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive CloudsSignsSingleCommunityMoment
  | cloudsAngelsDecision
  | mattersReturnToGod
  | israelClearSigns
  | blessingsAlteredPunishment
  | worldlyGlamourMockery
  | mindfulAboveResurrection
  | singleCommunity
  | prophetsScriptureTruth
  | rivalryDisagreement
  | guidedToTruth
deriving DecidableEq, Repr

def cloudsSignsSingleCommunityMoments : List CloudsSignsSingleCommunityMoment :=
  [ .cloudsAngelsDecision, .mattersReturnToGod, .israelClearSigns
  , .blessingsAlteredPunishment, .worldlyGlamourMockery, .mindfulAboveResurrection
  , .singleCommunity, .prophetsScriptureTruth, .rivalryDisagreement, .guidedToTruth ]

theorem quran_al_baqara_clouds_signs_single_community_witness :
    cloudsSignsSingleCommunityMoments.length = 10
    ∧ cloudsSignsSingleCommunityMoments.head? = some .cloudsAngelsDecision
    ∧ cloudsSignsSingleCommunityMoments.getLast? = some .guidedToTruth := by
  exact ⟨rfl, rfl, rfl⟩

end QuranAlBaqaraCloudsSignsSingleCommunityWitness
end Gnosis.Witnesses.Islam
