import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlMaidaPledgesMosesWitness

/-!
# Quran 5:12-26, Al-Maida -- Pledges, Hidden Scripture, Messiah Claim, and Moses' People

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:3530-3587`.

This bounded witness tracks Quran 5:12-26:

  * God takes a pledge from the Children of Israel and appoints twelve leaders;
  * prayer, alms, belief in messengers, support, and a good loan are tied to wiped sins
    and Gardens, while pledge ignoring strays from the path;
  * pledge-breaking hardens hearts, distorts words, forgets reminders, and leaves
    treachery except among a few;
  * those who say "we are Christians" also forget part of the reminder and fall into
    enmity and hatred until Resurrection;
  * the Messenger comes to the People of the Book, making clear what was hidden and
    overlooking much;
  * light and clear Scripture guide those seeking God's pleasure to peace, out of
    darkness into light, and to a straight path;
  * the claim that God is the Messiah is rejected by God's control over the heavens,
    earth, and creation;
  * Jewish and Christian claims of being God's children and beloved are answered by
    human creatureliness, forgiveness, punishment, return, and divine control;
  * the Messenger comes after a break in messengers so no one can claim no bearer of good
    news or warning came;
  * Moses reminds his people of prophets, kings, and blessing, commands entry into the
    holy land, and is met by fear and refusal;
  * two blessed men counsel trust and entry through the gate;
  * refusal leads Moses to ask judgment between himself, his brother, and the disobedient,
    and the land is forbidden to them for forty years.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive PledgesMosesMoment
  | israelPledge
  | pledgeRewardWarning
  | brokenPledgeHardHearts
  | christianPledgeForgotten
  | messengerClarifiesHidden
  | lightGuidesPeace
  | messiahClaimRejected
  | belovedClaimAnswered
  | messengerAfterBreak
  | mosesBlessingReminder
  | holyLandRefusal
  | blessedMenTrust
  | fortyYearWandering
deriving DecidableEq, Repr

def pledgesMosesMoments : List PledgesMosesMoment :=
  [ PledgesMosesMoment.israelPledge
  , PledgesMosesMoment.pledgeRewardWarning
  , PledgesMosesMoment.brokenPledgeHardHearts
  , PledgesMosesMoment.christianPledgeForgotten
  , PledgesMosesMoment.messengerClarifiesHidden
  , PledgesMosesMoment.lightGuidesPeace
  , PledgesMosesMoment.messiahClaimRejected
  , PledgesMosesMoment.belovedClaimAnswered
  , PledgesMosesMoment.messengerAfterBreak
  , PledgesMosesMoment.mosesBlessingReminder
  , PledgesMosesMoment.holyLandRefusal
  , PledgesMosesMoment.blessedMenTrust
  , PledgesMosesMoment.fortyYearWandering
  ]

structure PledgesMosesPattern where
  twelveLeadersNamed : Bool
  prayerAlmsMessengerSupport : Bool
  goodLoanGardens : Bool
  pledgeBreakingHardensHearts : Bool
  wordsDistortedReminderForgotten : Bool
  christianEnmityUntilResurrection : Bool
  hiddenScriptureMadeClear : Bool
  lightAndClearScripture : Bool
  darknessToLightStraightPath : Bool
  messiahDivinityClaimRejected : Bool
  belovedClaimHumanized : Bool
  noExcuseAfterMessengerBreak : Bool
  mosesBlessingsNamed : Bool
  gateTrustCounsel : Bool
  fortyYearsForbiddenLand : Bool
deriving DecidableEq, Repr

def pledgesMosesPattern : PledgesMosesPattern where
  twelveLeadersNamed := true
  prayerAlmsMessengerSupport := true
  goodLoanGardens := true
  pledgeBreakingHardensHearts := true
  wordsDistortedReminderForgotten := true
  christianEnmityUntilResurrection := true
  hiddenScriptureMadeClear := true
  lightAndClearScripture := true
  darknessToLightStraightPath := true
  messiahDivinityClaimRejected := true
  belovedClaimHumanized := true
  noExcuseAfterMessengerBreak := true
  mosesBlessingsNamed := true
  gateTrustCounsel := true
  fortyYearsForbiddenLand := true

theorem quran_al_maida_pledges_moses_witness :
    pledgesMosesMoments.length = 13
    ∧ pledgesMosesMoments.head? = some PledgesMosesMoment.israelPledge
    ∧ pledgesMosesMoments.getLast? = some PledgesMosesMoment.fortyYearWandering
    ∧ pledgesMosesPattern.twelveLeadersNamed = true
    ∧ pledgesMosesPattern.prayerAlmsMessengerSupport = true
    ∧ pledgesMosesPattern.goodLoanGardens = true
    ∧ pledgesMosesPattern.pledgeBreakingHardensHearts = true
    ∧ pledgesMosesPattern.wordsDistortedReminderForgotten = true
    ∧ pledgesMosesPattern.christianEnmityUntilResurrection = true
    ∧ pledgesMosesPattern.hiddenScriptureMadeClear = true
    ∧ pledgesMosesPattern.lightAndClearScripture = true
    ∧ pledgesMosesPattern.darknessToLightStraightPath = true
    ∧ pledgesMosesPattern.messiahDivinityClaimRejected = true
    ∧ pledgesMosesPattern.belovedClaimHumanized = true
    ∧ pledgesMosesPattern.noExcuseAfterMessengerBreak = true
    ∧ pledgesMosesPattern.mosesBlessingsNamed = true
    ∧ pledgesMosesPattern.gateTrustCounsel = true
    ∧ pledgesMosesPattern.fortyYearsForbiddenLand = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlMaidaPledgesMosesWitness
end Gnosis.Witnesses.Islam
