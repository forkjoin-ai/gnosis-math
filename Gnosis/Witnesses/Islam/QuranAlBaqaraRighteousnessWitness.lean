import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraRighteousnessWitness

/-!
# Quran 2:177, Al-Baqara -- Righteousness Redefined

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1551-1559`.

This bounded witness tracks the dense righteousness definition:

  * goodness is not reduced to turning toward East or West;
  * true goodness includes belief in God, the Last Day, angels, Scripture, and prophets;
  * cherished wealth is given to relatives, orphans, needy, travellers, beggars, and liberation;
  * prayer and prescribed alms are kept;
  * pledges are fulfilled;
  * steadfastness holds in misfortune, adversity, and danger;
  * such people are true and aware of God.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive RighteousnessMoment
  | notEastWestOrientation
  | beliefNamed
  | cherishedWealthGiven
  | prayerAndAlms
  | pledgeKeeping
  | steadfastInTrials
  | trueAndAware
deriving DecidableEq, Repr

def righteousnessMoments : List RighteousnessMoment :=
  [ RighteousnessMoment.notEastWestOrientation
  , RighteousnessMoment.beliefNamed
  , RighteousnessMoment.cherishedWealthGiven
  , RighteousnessMoment.prayerAndAlms
  , RighteousnessMoment.pledgeKeeping
  , RighteousnessMoment.steadfastInTrials
  , RighteousnessMoment.trueAndAware
  ]

structure BeliefRighteousnessPattern where
  notEastWestTurning : Bool
  believeInGod : Bool
  believeLastDay : Bool
  believeAngels : Bool
  believeScripture : Bool
  believeProphets : Bool
deriving DecidableEq, Repr

def beliefRighteousnessPattern : BeliefRighteousnessPattern where
  notEastWestTurning := true
  believeInGod := true
  believeLastDay := true
  believeAngels := true
  believeScripture := true
  believeProphets := true

structure CharityPracticePattern where
  cherishedWealthGiven : Bool
  relativesReceive : Bool
  orphansReceive : Bool
  needyReceive : Bool
  travellersReceive : Bool
  beggarsReceive : Bool
  bondageLiberation : Bool
  prayerKept : Bool
  prescribedAlmsPaid : Bool
deriving DecidableEq, Repr

def charityPracticePattern : CharityPracticePattern where
  cherishedWealthGiven := true
  relativesReceive := true
  orphansReceive := true
  needyReceive := true
  travellersReceive := true
  beggarsReceive := true
  bondageLiberation := true
  prayerKept := true
  prescribedAlmsPaid := true

structure PledgeSteadfastTruthPattern where
  pledgesKept : Bool
  misfortuneSteadfastness : Bool
  adversitySteadfastness : Bool
  dangerSteadfastness : Bool
  trueOnes : Bool
  awareOfGod : Bool
deriving DecidableEq, Repr

def pledgeSteadfastTruthPattern : PledgeSteadfastTruthPattern where
  pledgesKept := true
  misfortuneSteadfastness := true
  adversitySteadfastness := true
  dangerSteadfastness := true
  trueOnes := true
  awareOfGod := true

theorem quran_al_baqara_righteousness_witness :
    righteousnessMoments.length = 7
    ∧ righteousnessMoments.head? = some RighteousnessMoment.notEastWestOrientation
    ∧ righteousnessMoments.getLast? = some RighteousnessMoment.trueAndAware
    ∧ beliefRighteousnessPattern.notEastWestTurning = true
    ∧ beliefRighteousnessPattern.believeInGod = true
    ∧ beliefRighteousnessPattern.believeLastDay = true
    ∧ beliefRighteousnessPattern.believeAngels = true
    ∧ beliefRighteousnessPattern.believeScripture = true
    ∧ beliefRighteousnessPattern.believeProphets = true
    ∧ charityPracticePattern.cherishedWealthGiven = true
    ∧ charityPracticePattern.relativesReceive = true
    ∧ charityPracticePattern.orphansReceive = true
    ∧ charityPracticePattern.needyReceive = true
    ∧ charityPracticePattern.bondageLiberation = true
    ∧ charityPracticePattern.prayerKept = true
    ∧ charityPracticePattern.prescribedAlmsPaid = true
    ∧ pledgeSteadfastTruthPattern.pledgesKept = true
    ∧ pledgeSteadfastTruthPattern.misfortuneSteadfastness = true
    ∧ pledgeSteadfastTruthPattern.adversitySteadfastness = true
    ∧ pledgeSteadfastTruthPattern.dangerSteadfastness = true
    ∧ pledgeSteadfastTruthPattern.trueOnes = true
    ∧ pledgeSteadfastTruthPattern.awareOfGod = true := by
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

end QuranAlBaqaraRighteousnessWitness
end Gnosis.Witnesses.Islam
