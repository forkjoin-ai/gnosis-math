import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlImranWarningSovereigntyWitness

/-!
# Quran 3:10-32, Al Imran -- Warning, Desire, Witness, and Sovereignty

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:2158-2231`.

This bounded witness tracks Quran 3:10-32:

  * possessions and children do not save disbelievers from the Fire;
  * Pharaoh and earlier peoples denied revelations and were seized for sin;
  * two armies become a sign, and God helps whom He will;
  * worldly desires are named beside the better return with God;
  * believers pray for forgiveness and protection from the Fire;
  * God, the angels, and those with knowledge witness to divine oneness and justice;
  * dispute over Scripture is tied to rivalry after knowledge;
  * some reject Scripture judgment while claiming limited fire;
  * God gives and removes control, honors and humbles, alternates night and day,
    brings living from dead and dead from living, and provides without reckoning;
  * believers are warned about protective alliance against the faithful;
  * hidden and revealed hearts are known, deeds are presented, and love of God is
    tested through following the Messenger.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive WarningSovereigntyMoment
  | possessionsDoNotSave
  | pharaohPattern
  | twoArmiesSign
  | desiresAndBetterReturn
  | forgivenessPrayer
  | justiceWitness
  | scriptureJudgmentRejected
  | sovereigntyAlternation
  | allianceWarning
  | presentedDeeds
  | followMessenger
deriving DecidableEq, Repr

def warningSovereigntyMoments : List WarningSovereigntyMoment :=
  [ WarningSovereigntyMoment.possessionsDoNotSave
  , WarningSovereigntyMoment.pharaohPattern
  , WarningSovereigntyMoment.twoArmiesSign
  , WarningSovereigntyMoment.desiresAndBetterReturn
  , WarningSovereigntyMoment.forgivenessPrayer
  , WarningSovereigntyMoment.justiceWitness
  , WarningSovereigntyMoment.scriptureJudgmentRejected
  , WarningSovereigntyMoment.sovereigntyAlternation
  , WarningSovereigntyMoment.allianceWarning
  , WarningSovereigntyMoment.presentedDeeds
  , WarningSovereigntyMoment.followMessenger
  ]

structure WarningSovereigntyPattern where
  possessionsDoNotSave : Bool
  childrenDoNotSave : Bool
  fireFuelNamed : Bool
  earlierDeniersSeized : Bool
  twoArmiesSign : Bool
  worldlyDesireListed : Bool
  betterReturnNamed : Bool
  godAngelsKnowledgeWitness : Bool
  justiceUpheld : Bool
  scriptureJudgmentRefused : Bool
  controlGivenRemoved : Bool
  nightDayAlternation : Bool
  livingDeadAlternation : Bool
  heartKnowledgeNamed : Bool
  followMessengerCriterion : Bool
deriving DecidableEq, Repr

def warningSovereigntyPattern : WarningSovereigntyPattern where
  possessionsDoNotSave := true
  childrenDoNotSave := true
  fireFuelNamed := true
  earlierDeniersSeized := true
  twoArmiesSign := true
  worldlyDesireListed := true
  betterReturnNamed := true
  godAngelsKnowledgeWitness := true
  justiceUpheld := true
  scriptureJudgmentRefused := true
  controlGivenRemoved := true
  nightDayAlternation := true
  livingDeadAlternation := true
  heartKnowledgeNamed := true
  followMessengerCriterion := true

theorem quran_al_imran_warning_sovereignty_witness :
    warningSovereigntyMoments.length = 11
    ∧ warningSovereigntyMoments.head? = some WarningSovereigntyMoment.possessionsDoNotSave
    ∧ warningSovereigntyMoments.getLast? = some WarningSovereigntyMoment.followMessenger
    ∧ warningSovereigntyPattern.possessionsDoNotSave = true
    ∧ warningSovereigntyPattern.childrenDoNotSave = true
    ∧ warningSovereigntyPattern.fireFuelNamed = true
    ∧ warningSovereigntyPattern.earlierDeniersSeized = true
    ∧ warningSovereigntyPattern.twoArmiesSign = true
    ∧ warningSovereigntyPattern.worldlyDesireListed = true
    ∧ warningSovereigntyPattern.betterReturnNamed = true
    ∧ warningSovereigntyPattern.godAngelsKnowledgeWitness = true
    ∧ warningSovereigntyPattern.justiceUpheld = true
    ∧ warningSovereigntyPattern.scriptureJudgmentRefused = true
    ∧ warningSovereigntyPattern.controlGivenRemoved = true
    ∧ warningSovereigntyPattern.nightDayAlternation = true
    ∧ warningSovereigntyPattern.livingDeadAlternation = true
    ∧ warningSovereigntyPattern.heartKnowledgeNamed = true
    ∧ warningSovereigntyPattern.followMessengerCriterion = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlImranWarningSovereigntyWitness
end Gnosis.Witnesses.Islam
