import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlImranMartyrsMiserlinessWitness

/-!
# Quran 3:169-188, Al Imran -- Martyrs, Respite, Miserliness, Death, and Pledge

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:2652-2712`.

This bounded witness tracks Quran 3:169-188:

  * those killed in God's way are alive with their Lord, provided for and rejoicing;
  * they rejoice for those who have not yet joined them, with no fear or grief;
  * responders after defeat, who do good and remain mindful, receive reward;
  * threat of gathered forces increases faith, and God is enough as protector;
  * believers return with grace and bounty, unharmed;
  * Satan urges fear of his followers, but believers fear God;
  * quick movement into disbelief does not harm God;
  * respite only increases sin for those who sell faith for disbelief;
  * God separates bad from good and chooses messengers;
  * miserliness with God's bounty is bad and becomes a burden on Resurrection Day;
  * God inherits the heavens and earth;
  * the claim that God is poor and humans rich is recorded, along with killing prophets;
  * every soul tastes death and is paid in full on Resurrection Day;
  * success is being kept from the Fire and brought into the Garden;
  * possessions, persons, and hurtful speech are tests;
  * Scripture people are pledged to make revelation known and not conceal it;
  * rejoicing in deeds and seeking praise for what was not done does not escape torment.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive MartyrsMiserlinessMoment
  | martyrsAlive
  | noFearNoGrief
  | respondersRewarded
  | godEnoughProtector
  | returnedWithGrace
  | satanFearWarning
  | disbeliefDoesNotHarmGod
  | respiteIncreasesSin
  | badGoodSeparated
  | miserlinessBurden
  | godInherits
  | arrogantSpeechRecorded
  | everySoulDeath
  | fireGardenMeasure
  | testedAndHurt
  | pledgeToDisclose
  | falsePraiseCondemned
deriving DecidableEq, Repr

def martyrsMiserlinessMoments : List MartyrsMiserlinessMoment :=
  [ MartyrsMiserlinessMoment.martyrsAlive
  , MartyrsMiserlinessMoment.noFearNoGrief
  , MartyrsMiserlinessMoment.respondersRewarded
  , MartyrsMiserlinessMoment.godEnoughProtector
  , MartyrsMiserlinessMoment.returnedWithGrace
  , MartyrsMiserlinessMoment.satanFearWarning
  , MartyrsMiserlinessMoment.disbeliefDoesNotHarmGod
  , MartyrsMiserlinessMoment.respiteIncreasesSin
  , MartyrsMiserlinessMoment.badGoodSeparated
  , MartyrsMiserlinessMoment.miserlinessBurden
  , MartyrsMiserlinessMoment.godInherits
  , MartyrsMiserlinessMoment.arrogantSpeechRecorded
  , MartyrsMiserlinessMoment.everySoulDeath
  , MartyrsMiserlinessMoment.fireGardenMeasure
  , MartyrsMiserlinessMoment.testedAndHurt
  , MartyrsMiserlinessMoment.pledgeToDisclose
  , MartyrsMiserlinessMoment.falsePraiseCondemned
  ]

structure MartyrsMiserlinessPattern where
  martyrsAliveProvided : Bool
  noFearNoGrief : Bool
  respondersRewarded : Bool
  godEnoughProtector : Bool
  returnedWithGraceBounty : Bool
  satanFearRejected : Bool
  disbeliefNoHarmToGod : Bool
  respiteIncreasesSin : Bool
  badGoodSeparated : Bool
  messengersChosen : Bool
  miserlinessBurdenNamed : Bool
  godInheritsHeavensEarth : Bool
  arrogantSpeechRecorded : Bool
  everySoulTastesDeath : Bool
  fullPaymentResurrection : Bool
  worldlyLifeIllusion : Bool
  disclosurePledgeNamed : Bool
  falsePraiseCondemned : Bool
deriving DecidableEq, Repr

def martyrsMiserlinessPattern : MartyrsMiserlinessPattern where
  martyrsAliveProvided := true
  noFearNoGrief := true
  respondersRewarded := true
  godEnoughProtector := true
  returnedWithGraceBounty := true
  satanFearRejected := true
  disbeliefNoHarmToGod := true
  respiteIncreasesSin := true
  badGoodSeparated := true
  messengersChosen := true
  miserlinessBurdenNamed := true
  godInheritsHeavensEarth := true
  arrogantSpeechRecorded := true
  everySoulTastesDeath := true
  fullPaymentResurrection := true
  worldlyLifeIllusion := true
  disclosurePledgeNamed := true
  falsePraiseCondemned := true

theorem quran_al_imran_martyrs_miserliness_witness :
    martyrsMiserlinessMoments.length = 17
    ∧ martyrsMiserlinessMoments.head? = some MartyrsMiserlinessMoment.martyrsAlive
    ∧ martyrsMiserlinessMoments.getLast? = some MartyrsMiserlinessMoment.falsePraiseCondemned
    ∧ martyrsMiserlinessPattern.martyrsAliveProvided = true
    ∧ martyrsMiserlinessPattern.noFearNoGrief = true
    ∧ martyrsMiserlinessPattern.respondersRewarded = true
    ∧ martyrsMiserlinessPattern.godEnoughProtector = true
    ∧ martyrsMiserlinessPattern.returnedWithGraceBounty = true
    ∧ martyrsMiserlinessPattern.satanFearRejected = true
    ∧ martyrsMiserlinessPattern.disbeliefNoHarmToGod = true
    ∧ martyrsMiserlinessPattern.respiteIncreasesSin = true
    ∧ martyrsMiserlinessPattern.badGoodSeparated = true
    ∧ martyrsMiserlinessPattern.messengersChosen = true
    ∧ martyrsMiserlinessPattern.miserlinessBurdenNamed = true
    ∧ martyrsMiserlinessPattern.godInheritsHeavensEarth = true
    ∧ martyrsMiserlinessPattern.arrogantSpeechRecorded = true
    ∧ martyrsMiserlinessPattern.everySoulTastesDeath = true
    ∧ martyrsMiserlinessPattern.fullPaymentResurrection = true
    ∧ martyrsMiserlinessPattern.worldlyLifeIllusion = true
    ∧ martyrsMiserlinessPattern.disclosurePledgeNamed = true
    ∧ martyrsMiserlinessPattern.falsePraiseCondemned = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlImranMartyrsMiserlinessWitness
end Gnosis.Witnesses.Islam
