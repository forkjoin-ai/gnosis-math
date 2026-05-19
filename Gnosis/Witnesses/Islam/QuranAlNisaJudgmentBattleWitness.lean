import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlNisaJudgmentBattleWitness

/-!
# Quran 4:60-87, An-Nisa -- Judgment, Obedience, Guarded Battle, and True Word

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:3018-3113`.

This bounded witness tracks Quran 4:60-87:

  * those claiming belief still seek tyrannical judgment and turn from revelation;
  * hearts are known, penetrating instruction is commanded, and messengers are sent to
    be obeyed by God's leave;
  * true belief accepts the Prophet's judgment without inward resistance;
  * obedience leads to straight path, favour, and companionship with messengers, truthful,
    witnesses to truth, and righteous people;
  * believers are told to be on guard and march in groups or together;
  * laggards interpret calamity and favour through self-interest;
  * fighting in God's cause includes defense of oppressed men, women, and children;
  * believers fight for God's cause, while rejecters fight for an unjust cause;
  * fear of people, death in high towers, good and bad fortune, Messenger obedience,
    and night scheming are addressed;
  * the Quran's lack of inconsistency is a sign of divine source;
  * public news of peace or war should be referred to the Messenger and authority;
  * the Prophet is accountable for himself, urges believers, and God curbs disbelievers;
  * good and bad intercession, greeting response, final gathering, and God's truest word
    close the unit.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive JudgmentBattleMoment
  | tyrantJudgmentClaim
  | penetratingInstruction
  | messengerObedience
  | prophetJudgmentAccepted
  | blessedCompanions
  | guardedMarch
  | laggardSpeech
  | oppressedCry
  | godsCauseAgainstUnjustCause
  | deathAndFortune
  | messengerObedienceGod
  | quranConsistency
  | newsReferral
  | greetingAndGathering
deriving DecidableEq, Repr

def judgmentBattleMoments : List JudgmentBattleMoment :=
  [ JudgmentBattleMoment.tyrantJudgmentClaim
  , JudgmentBattleMoment.penetratingInstruction
  , JudgmentBattleMoment.messengerObedience
  , JudgmentBattleMoment.prophetJudgmentAccepted
  , JudgmentBattleMoment.blessedCompanions
  , JudgmentBattleMoment.guardedMarch
  , JudgmentBattleMoment.laggardSpeech
  , JudgmentBattleMoment.oppressedCry
  , JudgmentBattleMoment.godsCauseAgainstUnjustCause
  , JudgmentBattleMoment.deathAndFortune
  , JudgmentBattleMoment.messengerObedienceGod
  , JudgmentBattleMoment.quranConsistency
  , JudgmentBattleMoment.newsReferral
  , JudgmentBattleMoment.greetingAndGathering
  ]

structure JudgmentBattlePattern where
  tyrantJudgmentRejected : Bool
  hypocritesTurnAway : Bool
  heartsKnown : Bool
  prophetDecisionNoResistance : Bool
  obeyGodMessengerBlessed : Bool
  guardAndMarchCommanded : Bool
  laggardSelfInterestExposed : Bool
  oppressedPrayerNamed : Bool
  satanStrategiesWeak : Bool
  deathOvertakesEverywhere : Bool
  messengerObedienceEqualsGodObedience : Bool
  quranNoInconsistency : Bool
  newsReferredToAuthority : Bool
  goodBadCauseShares : Bool
  greetingReturnedBetter : Bool
  resurrectionNoDoubt : Bool
deriving DecidableEq, Repr

def judgmentBattlePattern : JudgmentBattlePattern where
  tyrantJudgmentRejected := true
  hypocritesTurnAway := true
  heartsKnown := true
  prophetDecisionNoResistance := true
  obeyGodMessengerBlessed := true
  guardAndMarchCommanded := true
  laggardSelfInterestExposed := true
  oppressedPrayerNamed := true
  satanStrategiesWeak := true
  deathOvertakesEverywhere := true
  messengerObedienceEqualsGodObedience := true
  quranNoInconsistency := true
  newsReferredToAuthority := true
  goodBadCauseShares := true
  greetingReturnedBetter := true
  resurrectionNoDoubt := true

theorem quran_al_nisa_judgment_battle_witness :
    judgmentBattleMoments.length = 14
    ∧ judgmentBattleMoments.head? = some JudgmentBattleMoment.tyrantJudgmentClaim
    ∧ judgmentBattleMoments.getLast? = some JudgmentBattleMoment.greetingAndGathering
    ∧ judgmentBattlePattern.tyrantJudgmentRejected = true
    ∧ judgmentBattlePattern.hypocritesTurnAway = true
    ∧ judgmentBattlePattern.heartsKnown = true
    ∧ judgmentBattlePattern.prophetDecisionNoResistance = true
    ∧ judgmentBattlePattern.obeyGodMessengerBlessed = true
    ∧ judgmentBattlePattern.guardAndMarchCommanded = true
    ∧ judgmentBattlePattern.laggardSelfInterestExposed = true
    ∧ judgmentBattlePattern.oppressedPrayerNamed = true
    ∧ judgmentBattlePattern.satanStrategiesWeak = true
    ∧ judgmentBattlePattern.deathOvertakesEverywhere = true
    ∧ judgmentBattlePattern.messengerObedienceEqualsGodObedience = true
    ∧ judgmentBattlePattern.quranNoInconsistency = true
    ∧ judgmentBattlePattern.newsReferredToAuthority = true
    ∧ judgmentBattlePattern.goodBadCauseShares = true
    ∧ judgmentBattlePattern.greetingReturnedBetter = true
    ∧ judgmentBattlePattern.resurrectionNoDoubt = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlNisaJudgmentBattleWitness
end Gnosis.Witnesses.Islam
