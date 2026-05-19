import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlNisaBetrayalSatanAbrahamWitness

/-!
# Quran 4:105-126, An-Nisa -- Betrayal, Forgiveness, Satan, Deeds, and Abraham

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:3209-3265`.

This bounded witness tracks Quran 4:105-126:

  * Scripture is sent with truth so the Prophet can judge by what God has shown;
  * betrayal advocacy is forbidden, forgiveness is requested, and treachery cannot hide
    from God;
  * arguing for betrayers in this life leaves no defender before God on Resurrection Day;
  * evil and self-wronging followed by forgiveness-seeking finds God forgiving and merciful;
  * sin is against one's own soul, and blaming the innocent adds deceit and flagrant sin;
  * divine grace, mercy, Scripture, Wisdom, teaching, and bounty protect the Prophet;
  * secret talk is good only when commanding charity, good, or reconciliation for God's
    pleasure;
  * opposing the Messenger after clear guidance and following another path leads to Hell;
  * worship of others beside God is not forgiven, while Satan promises, misleads, incites
    vain desires, and commands tampering with creation;
  * Satan's promises are delusion, while believers who do good receive God's true promise;
  * outcomes are not according to hopes: wrong is requited, and faithful good enters
    Paradise without the date-stone dip of wrong;
  * the best religion is wholly directing oneself to God, doing good, and following
    Abraham, true in faith and God's friend;
  * everything in the heavens and earth belongs to God.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive BetrayalSatanAbrahamMoment
  | truthJudgment
  | noBetrayalAdvocacy
  | cannotHideFromGod
  | forgivenessAfterWrong
  | innocentBlamed
  | graceScriptureWisdom
  | secretTalkGood
  | messengerOpposed
  | satanPatron
  | promiseAndRequital
  | faithfulGoodParadise
  | abrahamFriend
  | heavensEarthBelongGod
deriving DecidableEq, Repr

def betrayalSatanAbrahamMoments : List BetrayalSatanAbrahamMoment :=
  [ BetrayalSatanAbrahamMoment.truthJudgment
  , BetrayalSatanAbrahamMoment.noBetrayalAdvocacy
  , BetrayalSatanAbrahamMoment.cannotHideFromGod
  , BetrayalSatanAbrahamMoment.forgivenessAfterWrong
  , BetrayalSatanAbrahamMoment.innocentBlamed
  , BetrayalSatanAbrahamMoment.graceScriptureWisdom
  , BetrayalSatanAbrahamMoment.secretTalkGood
  , BetrayalSatanAbrahamMoment.messengerOpposed
  , BetrayalSatanAbrahamMoment.satanPatron
  , BetrayalSatanAbrahamMoment.promiseAndRequital
  , BetrayalSatanAbrahamMoment.faithfulGoodParadise
  , BetrayalSatanAbrahamMoment.abrahamFriend
  , BetrayalSatanAbrahamMoment.heavensEarthBelongGod
  ]

structure BetrayalSatanAbrahamPattern where
  scriptureWithTruthForJudgment : Bool
  betrayersNotDefended : Bool
  godPresentAtNightPlot : Bool
  forgivenessAfterSelfWrong : Bool
  innocentBlameFlagrantSin : Bool
  scriptureWisdomTeachingNamed : Bool
  secretTalkCharityGoodReconciliation : Bool
  messengerOppositionCondemned : Bool
  partnerWorshipNotForgiven : Bool
  satanMisleadsAndCommandsTampering : Bool
  satanPromiseDelusion : Bool
  godsPromiseTrue : Bool
  maleFemaleGoodNotWronged : Bool
  abrahamTrueFriend : Bool
  godAwareOfAllThings : Bool
deriving DecidableEq, Repr

def betrayalSatanAbrahamPattern : BetrayalSatanAbrahamPattern where
  scriptureWithTruthForJudgment := true
  betrayersNotDefended := true
  godPresentAtNightPlot := true
  forgivenessAfterSelfWrong := true
  innocentBlameFlagrantSin := true
  scriptureWisdomTeachingNamed := true
  secretTalkCharityGoodReconciliation := true
  messengerOppositionCondemned := true
  partnerWorshipNotForgiven := true
  satanMisleadsAndCommandsTampering := true
  satanPromiseDelusion := true
  godsPromiseTrue := true
  maleFemaleGoodNotWronged := true
  abrahamTrueFriend := true
  godAwareOfAllThings := true

theorem quran_al_nisa_betrayal_satan_abraham_witness :
    betrayalSatanAbrahamMoments.length = 13
    ∧ betrayalSatanAbrahamMoments.head? = some BetrayalSatanAbrahamMoment.truthJudgment
    ∧ betrayalSatanAbrahamMoments.getLast? = some BetrayalSatanAbrahamMoment.heavensEarthBelongGod
    ∧ betrayalSatanAbrahamPattern.scriptureWithTruthForJudgment = true
    ∧ betrayalSatanAbrahamPattern.betrayersNotDefended = true
    ∧ betrayalSatanAbrahamPattern.godPresentAtNightPlot = true
    ∧ betrayalSatanAbrahamPattern.forgivenessAfterSelfWrong = true
    ∧ betrayalSatanAbrahamPattern.innocentBlameFlagrantSin = true
    ∧ betrayalSatanAbrahamPattern.scriptureWisdomTeachingNamed = true
    ∧ betrayalSatanAbrahamPattern.secretTalkCharityGoodReconciliation = true
    ∧ betrayalSatanAbrahamPattern.messengerOppositionCondemned = true
    ∧ betrayalSatanAbrahamPattern.partnerWorshipNotForgiven = true
    ∧ betrayalSatanAbrahamPattern.satanMisleadsAndCommandsTampering = true
    ∧ betrayalSatanAbrahamPattern.satanPromiseDelusion = true
    ∧ betrayalSatanAbrahamPattern.godsPromiseTrue = true
    ∧ betrayalSatanAbrahamPattern.maleFemaleGoodNotWronged = true
    ∧ betrayalSatanAbrahamPattern.abrahamTrueFriend = true
    ∧ betrayalSatanAbrahamPattern.godAwareOfAllThings = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlNisaBetrayalSatanAbrahamWitness
end Gnosis.Witnesses.Islam
