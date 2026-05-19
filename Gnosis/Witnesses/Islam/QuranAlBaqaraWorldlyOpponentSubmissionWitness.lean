import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraWorldlyOpponentSubmissionWitness

/-!
# Quran 2:204-209, Al-Baqara -- Worldly Opponent and Whole Submission

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1703-1714`.

This witness tracks the contrast between pleasing worldly speech that hides bitter
opposition and the person who gives life to please God, then calls believers into
wholehearted submission without following Satan after clear proof.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive WorldlyOpponentSubmissionMoment
  | pleasingWorldlySpeech
  | bitterOpponent
  | corruptionCropsLivestock
  | arrogantSinHell
  | lifeGivenForGod
  | wholeheartedSubmission
  | satanFootstepsRejected
  | clearProofNoSlip
  | almightyWise
deriving DecidableEq, Repr

def worldlyOpponentSubmissionMoments : List WorldlyOpponentSubmissionMoment :=
  [ .pleasingWorldlySpeech, .bitterOpponent, .corruptionCropsLivestock
  , .arrogantSinHell, .lifeGivenForGod, .wholeheartedSubmission
  , .satanFootstepsRejected, .clearProofNoSlip, .almightyWise ]

theorem quran_al_baqara_worldly_opponent_submission_witness :
    worldlyOpponentSubmissionMoments.length = 9
    ∧ worldlyOpponentSubmissionMoments.head? = some .pleasingWorldlySpeech
    ∧ worldlyOpponentSubmissionMoments.getLast? = some .almightyWise := by
  exact ⟨rfl, rfl, rfl⟩

end QuranAlBaqaraWorldlyOpponentSubmissionWitness
end Gnosis.Witnesses.Islam
