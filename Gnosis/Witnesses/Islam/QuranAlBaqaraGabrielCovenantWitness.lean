import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraGabrielCovenantWitness

/-!
# Quran 2:97-100, Al-Baqara -- Gabriel, Clear Messages, Covenant-Breaking

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1254-1262`.

This bounded witness tracks the Gabriel and covenant-breaking unit:

  * Gabriel brings down the Qur'an by God's leave to the Prophet's heart;
  * it confirms previous scriptures and serves as guide and good news for the faithful;
  * enmity against God, angels, messengers, Gabriel, and Michael is named;
  * God is enemy to such disbelievers;
  * clear messages are sent down;
  * only defiance refuses belief;
  * covenants and pledges are thrown away by some, while most do not believe.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive GabrielCovenantMoment
  | gabrielBringsQuran
  | confirmsPreviousScriptures
  | guideAndGoodNews
  | enmityNamed
  | godEnemyToDisbelievers
  | clearMessagesSent
  | defiantRefusal
  | covenantThrownAway
  | mostDoNotBelieve
deriving DecidableEq, Repr

def gabrielCovenantMoments : List GabrielCovenantMoment :=
  [ GabrielCovenantMoment.gabrielBringsQuran
  , GabrielCovenantMoment.confirmsPreviousScriptures
  , GabrielCovenantMoment.guideAndGoodNews
  , GabrielCovenantMoment.enmityNamed
  , GabrielCovenantMoment.godEnemyToDisbelievers
  , GabrielCovenantMoment.clearMessagesSent
  , GabrielCovenantMoment.defiantRefusal
  , GabrielCovenantMoment.covenantThrownAway
  , GabrielCovenantMoment.mostDoNotBelieve
  ]

structure GabrielRevelationPattern where
  gabrielNamed : Bool
  broughtDownQuran : Bool
  byGodsLeave : Bool
  toProphetHeart : Bool
  confirmsPreviousScriptures : Bool
  guideForFaithful : Bool
  goodNewsForFaithful : Bool
deriving DecidableEq, Repr

def gabrielRevelationPattern : GabrielRevelationPattern where
  gabrielNamed := true
  broughtDownQuran := true
  byGodsLeave := true
  toProphetHeart := true
  confirmsPreviousScriptures := true
  guideForFaithful := true
  goodNewsForFaithful := true

structure EnmityClearMessagePattern where
  enemyOfGodNamed : Bool
  enemyOfAngelsNamed : Bool
  enemyOfMessengersNamed : Bool
  enemyOfGabrielNamed : Bool
  enemyOfMichaelNamed : Bool
  godEnemyToDisbelievers : Bool
  clearMessagesSentDown : Bool
  defiantRefuseBelief : Bool
deriving DecidableEq, Repr

def enmityClearMessagePattern : EnmityClearMessagePattern where
  enemyOfGodNamed := true
  enemyOfAngelsNamed := true
  enemyOfMessengersNamed := true
  enemyOfGabrielNamed := true
  enemyOfMichaelNamed := true
  godEnemyToDisbelievers := true
  clearMessagesSentDown := true
  defiantRefuseBelief := true

structure CovenantBreakingPattern where
  covenantMade : Bool
  pledgeMade : Bool
  someThrowAway : Bool
  mostDoNotBelieve : Bool
deriving DecidableEq, Repr

def covenantBreakingPattern : CovenantBreakingPattern where
  covenantMade := true
  pledgeMade := true
  someThrowAway := true
  mostDoNotBelieve := true

theorem quran_al_baqara_gabriel_covenant_witness :
    gabrielCovenantMoments.length = 9
    ∧ gabrielCovenantMoments.head? = some GabrielCovenantMoment.gabrielBringsQuran
    ∧ gabrielCovenantMoments.getLast? = some GabrielCovenantMoment.mostDoNotBelieve
    ∧ gabrielRevelationPattern.gabrielNamed = true
    ∧ gabrielRevelationPattern.broughtDownQuran = true
    ∧ gabrielRevelationPattern.byGodsLeave = true
    ∧ gabrielRevelationPattern.toProphetHeart = true
    ∧ gabrielRevelationPattern.confirmsPreviousScriptures = true
    ∧ gabrielRevelationPattern.guideForFaithful = true
    ∧ gabrielRevelationPattern.goodNewsForFaithful = true
    ∧ enmityClearMessagePattern.enemyOfGodNamed = true
    ∧ enmityClearMessagePattern.enemyOfAngelsNamed = true
    ∧ enmityClearMessagePattern.enemyOfMessengersNamed = true
    ∧ enmityClearMessagePattern.enemyOfGabrielNamed = true
    ∧ enmityClearMessagePattern.enemyOfMichaelNamed = true
    ∧ enmityClearMessagePattern.godEnemyToDisbelievers = true
    ∧ enmityClearMessagePattern.clearMessagesSentDown = true
    ∧ enmityClearMessagePattern.defiantRefuseBelief = true
    ∧ covenantBreakingPattern.covenantMade = true
    ∧ covenantBreakingPattern.pledgeMade = true
    ∧ covenantBreakingPattern.someThrowAway = true
    ∧ covenantBreakingPattern.mostDoNotBelieve = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end QuranAlBaqaraGabrielCovenantWitness
end Gnosis.Witnesses.Islam
