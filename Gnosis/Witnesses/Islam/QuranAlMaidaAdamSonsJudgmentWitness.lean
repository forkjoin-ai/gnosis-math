import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlMaidaAdamSonsJudgmentWitness

/-!
# Quran 5:27-50, Al-Maida -- Adam's Sons, Life Decree, Penalties, Torah, Gospel, and Judgment

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:3588-3687`.

This bounded witness tracks Quran 5:27-50:

  * Adam's two sons offer sacrifices; one is accepted from the mindful and one is not;
  * the threatened brother refuses reciprocal killing, fears God, and names the Fire as
    the evildoers' reward;
  * killing his brother makes the killer one of the losers, and the raven teaches burial;
  * killing one person is compared to killing all mankind, and saving one life to saving
    all mankind;
  * those waging war against God and His Messenger and spreading corruption receive
    worldly disgrace and Hereafter punishment unless they repent before capture;
  * believers seek nearness to God and strive in His cause;
  * disbelievers cannot ransom themselves from Resurrection torment;
  * theft, repentance, amendment, punishment, forgiveness, and God's control are named;
  * some race into disbelief with mouths claiming belief while hearts lack faith;
  * judgment may be declined or given justly, while Torah judgment is still turned away;
  * Torah is guidance and light, preserved and witnessed by prophets, rabbis, and scholars;
  * equal retribution and charitable forgoing are named;
  * Jesus confirms Torah and receives Gospel as guidance, light, confirmation, guide, and
    lesson;
  * the Quran confirms earlier Scripture with final authority, assigns each a law and path,
    tests communities, commands racing to good, and returns all to God;
  * judgment by God is contrasted with judgment from pagan ignorance.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive AdamSonsJudgmentMoment
  | sacrificesAccepted
  | nonRetaliationFear
  | ravenBurialRemorse
  | lifeDecree
  | corruptionPenaltyRepentance
  | seekNearnessStrive
  | ransomRejected
  | theftRepentanceControl
  | disbeliefRace
  | judgeJustlyOrDecline
  | torahGuidanceLight
  | equalRetributionForgoing
  | gospelGuidanceLight
  | quranFinalAuthority
  | lawPathRaceGood
  | bestJudgmentGod
deriving DecidableEq, Repr

def adamSonsJudgmentMoments : List AdamSonsJudgmentMoment :=
  [ AdamSonsJudgmentMoment.sacrificesAccepted
  , AdamSonsJudgmentMoment.nonRetaliationFear
  , AdamSonsJudgmentMoment.ravenBurialRemorse
  , AdamSonsJudgmentMoment.lifeDecree
  , AdamSonsJudgmentMoment.corruptionPenaltyRepentance
  , AdamSonsJudgmentMoment.seekNearnessStrive
  , AdamSonsJudgmentMoment.ransomRejected
  , AdamSonsJudgmentMoment.theftRepentanceControl
  , AdamSonsJudgmentMoment.disbeliefRace
  , AdamSonsJudgmentMoment.judgeJustlyOrDecline
  , AdamSonsJudgmentMoment.torahGuidanceLight
  , AdamSonsJudgmentMoment.equalRetributionForgoing
  , AdamSonsJudgmentMoment.gospelGuidanceLight
  , AdamSonsJudgmentMoment.quranFinalAuthority
  , AdamSonsJudgmentMoment.lawPathRaceGood
  , AdamSonsJudgmentMoment.bestJudgmentGod
  ]

structure AdamSonsJudgmentPattern where
  sacrificeMindfulnessNamed : Bool
  refusalToKillNamed : Bool
  ravenBurialNamed : Bool
  oneLifeAllMankind : Bool
  corruptionPenaltyNamed : Bool
  repentanceBeforeCaptureException : Bool
  seekNearnessAndStrive : Bool
  ransomNotAccepted : Bool
  theftRepentanceAccepted : Bool
  mouthsHeartsGapNamed : Bool
  judgeJustlyCommanded : Bool
  torahGuidanceLight : Bool
  equalRetributionCharity : Bool
  gospelGuidanceLight : Bool
  quranConfirmsAndGuards : Bool
  lawPathTestRaceGood : Bool
  returnClarifiesDifferences : Bool
  godBestJudge : Bool
deriving DecidableEq, Repr

def adamSonsJudgmentPattern : AdamSonsJudgmentPattern where
  sacrificeMindfulnessNamed := true
  refusalToKillNamed := true
  ravenBurialNamed := true
  oneLifeAllMankind := true
  corruptionPenaltyNamed := true
  repentanceBeforeCaptureException := true
  seekNearnessAndStrive := true
  ransomNotAccepted := true
  theftRepentanceAccepted := true
  mouthsHeartsGapNamed := true
  judgeJustlyCommanded := true
  torahGuidanceLight := true
  equalRetributionCharity := true
  gospelGuidanceLight := true
  quranConfirmsAndGuards := true
  lawPathTestRaceGood := true
  returnClarifiesDifferences := true
  godBestJudge := true

theorem quran_al_maida_adam_sons_judgment_witness :
    adamSonsJudgmentMoments.length = 16
    ∧ adamSonsJudgmentMoments.head? = some AdamSonsJudgmentMoment.sacrificesAccepted
    ∧ adamSonsJudgmentMoments.getLast? = some AdamSonsJudgmentMoment.bestJudgmentGod
    ∧ adamSonsJudgmentPattern.sacrificeMindfulnessNamed = true
    ∧ adamSonsJudgmentPattern.refusalToKillNamed = true
    ∧ adamSonsJudgmentPattern.ravenBurialNamed = true
    ∧ adamSonsJudgmentPattern.oneLifeAllMankind = true
    ∧ adamSonsJudgmentPattern.corruptionPenaltyNamed = true
    ∧ adamSonsJudgmentPattern.repentanceBeforeCaptureException = true
    ∧ adamSonsJudgmentPattern.seekNearnessAndStrive = true
    ∧ adamSonsJudgmentPattern.ransomNotAccepted = true
    ∧ adamSonsJudgmentPattern.theftRepentanceAccepted = true
    ∧ adamSonsJudgmentPattern.mouthsHeartsGapNamed = true
    ∧ adamSonsJudgmentPattern.judgeJustlyCommanded = true
    ∧ adamSonsJudgmentPattern.torahGuidanceLight = true
    ∧ adamSonsJudgmentPattern.equalRetributionCharity = true
    ∧ adamSonsJudgmentPattern.gospelGuidanceLight = true
    ∧ adamSonsJudgmentPattern.quranConfirmsAndGuards = true
    ∧ adamSonsJudgmentPattern.lawPathTestRaceGood = true
    ∧ adamSonsJudgmentPattern.returnClarifiesDifferences = true
    ∧ adamSonsJudgmentPattern.godBestJudge = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlMaidaAdamSonsJudgmentWitness
end Gnosis.Witnesses.Islam
