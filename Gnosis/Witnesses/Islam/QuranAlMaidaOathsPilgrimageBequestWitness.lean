import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlMaidaOathsPilgrimageBequestWitness

/-!
# Quran 5:87-108, Al-Maida -- Lawful Good, Oaths, Intoxicants, Pilgrimage Game, Questions, and Bequest Witnesses

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:3812-3912`.

This bounded witness tracks Quran 5:87-108:

  * believers must not forbid the good things God made lawful or exceed limits;
  * lawful and good provision is to be eaten with mindfulness of God;
  * binding oaths have atonement through feeding, clothing, freeing a slave, or fasting;
  * intoxicants, gambling, idolatrous practices, and divining arrows are Satanic and to
    be shunned;
  * Satan uses intoxicants and gambling to incite enmity and hatred and to block
    remembrance and prayer;
  * obedience to God and the Messenger is commanded, while the Messenger's duty is clear
    delivery;
  * past consumption is not blamed for believers who remain mindful, believe, and do good;
  * game within reach tests fear of God unseen;
  * intentional game-killing during consecration is answered by equivalent offering,
    feeding, or fasting, judged by two just men;
  * seafood is permitted, while land game remains forbidden during consecration;
  * Kaaba, Sacred Months, sacrificial animals, and garlands are supports for people;
  * bad and good are not alike despite abundant bad;
  * believers are warned not to ask burdensome questions during revelation;
  * invented livestock dedications to idols are lies about God and inherited ignorance;
  * believers are responsible for their own souls and return to God;
  * deathbed bequests require two witnesses, oaths, and replacement testimony where
    perjury is discovered.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive OathsPilgrimageBequestMoment
  | lawfulGoodNotForbidden
  | oathAtonement
  | intoxicantsGamblingShunned
  | satanBlocksPrayer
  | messengerClearDelivery
  | pastConsumptionMercy
  | gameTestUnseenFear
  | consecrationPenalty
  | seafoodPermitted
  | kaabaSacredSupports
  | badNotGood
  | questionsLimited
  | inheritedIdolDedicates
  | soulResponsibility
  | bequestWitnesses
deriving DecidableEq, Repr

def oathsPilgrimageBequestMoments : List OathsPilgrimageBequestMoment :=
  [ OathsPilgrimageBequestMoment.lawfulGoodNotForbidden
  , OathsPilgrimageBequestMoment.oathAtonement
  , OathsPilgrimageBequestMoment.intoxicantsGamblingShunned
  , OathsPilgrimageBequestMoment.satanBlocksPrayer
  , OathsPilgrimageBequestMoment.messengerClearDelivery
  , OathsPilgrimageBequestMoment.pastConsumptionMercy
  , OathsPilgrimageBequestMoment.gameTestUnseenFear
  , OathsPilgrimageBequestMoment.consecrationPenalty
  , OathsPilgrimageBequestMoment.seafoodPermitted
  , OathsPilgrimageBequestMoment.kaabaSacredSupports
  , OathsPilgrimageBequestMoment.badNotGood
  , OathsPilgrimageBequestMoment.questionsLimited
  , OathsPilgrimageBequestMoment.inheritedIdolDedicates
  , OathsPilgrimageBequestMoment.soulResponsibility
  , OathsPilgrimageBequestMoment.bequestWitnesses
  ]

structure OathsPilgrimageBequestPattern where
  lawfulGoodNotForbidden : Bool
  oathAtonementOptions : Bool
  satanicActsShunned : Bool
  enmityPrayerBlockNamed : Bool
  messengerClearDelivery : Bool
  pastConsumptionNotBlamed : Bool
  gameTestNamed : Bool
  consecrationPenaltyOptions : Bool
  seafoodPermitted : Bool
  kaabaSupportNamed : Bool
  godKnowsRevealConceal : Bool
  badNotLikeGood : Bool
  burdensomeQuestionsWarned : Bool
  idolDedicatesInvented : Bool
  ownSoulsResponsible : Bool
  bequestOathWitnesses : Bool
deriving DecidableEq, Repr

def oathsPilgrimageBequestPattern : OathsPilgrimageBequestPattern where
  lawfulGoodNotForbidden := true
  oathAtonementOptions := true
  satanicActsShunned := true
  enmityPrayerBlockNamed := true
  messengerClearDelivery := true
  pastConsumptionNotBlamed := true
  gameTestNamed := true
  consecrationPenaltyOptions := true
  seafoodPermitted := true
  kaabaSupportNamed := true
  godKnowsRevealConceal := true
  badNotLikeGood := true
  burdensomeQuestionsWarned := true
  idolDedicatesInvented := true
  ownSoulsResponsible := true
  bequestOathWitnesses := true

theorem quran_al_maida_oaths_pilgrimage_bequest_witness :
    oathsPilgrimageBequestMoments.length = 15
    ∧ oathsPilgrimageBequestMoments.head? = some OathsPilgrimageBequestMoment.lawfulGoodNotForbidden
    ∧ oathsPilgrimageBequestMoments.getLast? = some OathsPilgrimageBequestMoment.bequestWitnesses
    ∧ oathsPilgrimageBequestPattern.lawfulGoodNotForbidden = true
    ∧ oathsPilgrimageBequestPattern.oathAtonementOptions = true
    ∧ oathsPilgrimageBequestPattern.satanicActsShunned = true
    ∧ oathsPilgrimageBequestPattern.enmityPrayerBlockNamed = true
    ∧ oathsPilgrimageBequestPattern.messengerClearDelivery = true
    ∧ oathsPilgrimageBequestPattern.pastConsumptionNotBlamed = true
    ∧ oathsPilgrimageBequestPattern.gameTestNamed = true
    ∧ oathsPilgrimageBequestPattern.consecrationPenaltyOptions = true
    ∧ oathsPilgrimageBequestPattern.seafoodPermitted = true
    ∧ oathsPilgrimageBequestPattern.kaabaSupportNamed = true
    ∧ oathsPilgrimageBequestPattern.godKnowsRevealConceal = true
    ∧ oathsPilgrimageBequestPattern.badNotLikeGood = true
    ∧ oathsPilgrimageBequestPattern.burdensomeQuestionsWarned = true
    ∧ oathsPilgrimageBequestPattern.idolDedicatesInvented = true
    ∧ oathsPilgrimageBequestPattern.ownSoulsResponsible = true
    ∧ oathsPilgrimageBequestPattern.bequestOathWitnesses = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlMaidaOathsPilgrimageBequestWitness
end Gnosis.Witnesses.Islam
