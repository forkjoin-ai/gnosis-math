import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraWorshipChallengeCreationWitness

/-!
# Quran 2:21-29, Al-Baqara -- Worship, Challenge, Creation

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:993-1021`.

This bounded witness tracks the next Al-Baqara movement after the opening
guidance groups:

  * people are called to worship the Lord who created them and those before them;
  * earth, sky, rain, and sustenance are named as creation/provision signs;
  * rivals to God are rejected;
  * the revelation challenge asks doubters to produce a single sura like it;
  * inability to meet that challenge is paired with the Fire warning;
  * believers who do good receive the garden promise;
  * parables, even small ones, distinguish truth-recognition from rebellious error;
  * covenant-breaking, severed bonds, and corruption mark the losers;
  * life, death, resurrection, return, earth, seven heavens, and knowledge close the unit.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive BaqaraWorshipCreationMoment
  | worshipCreator
  | provisionSigns
  | suraChallenge
  | fireWarning
  | gardenPromise
  | parableSorting
  | covenantRupture
  | lifeDeathReturn
  | sevenHeavensKnowledge
deriving DecidableEq, Repr

def baqaraWorshipCreationMoments : List BaqaraWorshipCreationMoment :=
  [ BaqaraWorshipCreationMoment.worshipCreator
  , BaqaraWorshipCreationMoment.provisionSigns
  , BaqaraWorshipCreationMoment.suraChallenge
  , BaqaraWorshipCreationMoment.fireWarning
  , BaqaraWorshipCreationMoment.gardenPromise
  , BaqaraWorshipCreationMoment.parableSorting
  , BaqaraWorshipCreationMoment.covenantRupture
  , BaqaraWorshipCreationMoment.lifeDeathReturn
  , BaqaraWorshipCreationMoment.sevenHeavensKnowledge
  ]

structure WorshipProvisionPattern where
  worshipLord : Bool
  creatorOfPresentAndBefore : Bool
  mindfulnessAim : Bool
  earthSpreadOut : Bool
  skyBuilt : Bool
  rainSentDown : Bool
  sustenanceProduced : Bool
  rivalsRejected : Bool
deriving DecidableEq, Repr

def worshipProvisionPattern : WorshipProvisionPattern where
  worshipLord := true
  creatorOfPresentAndBefore := true
  mindfulnessAim := true
  earthSpreadOut := true
  skyBuilt := true
  rainSentDown := true
  sustenanceProduced := true
  rivalsRejected := true

structure RevelationChallengePattern where
  doubtNamed : Bool
  revelationSentToServant : Bool
  singleSuraChallenge : Bool
  supportersPermitted : Bool
  challengeWillNotBeMet : Bool
  firePrepared : Bool
  fuelMenAndStones : Bool
deriving DecidableEq, Repr

def revelationChallengePattern : RevelationChallengePattern where
  doubtNamed := true
  revelationSentToServant := true
  singleSuraChallenge := true
  supportersPermitted := true
  challengeWillNotBeMet := true
  firePrepared := true
  fuelMenAndStones := true

structure GardenParableCovenantPattern where
  believersDoGood : Bool
  gardensFlowingStreams : Bool
  recurringRecognizedSustenance : Bool
  pureSpousesAbiding : Bool
  smallParableAllowed : Bool
  believersKnowTruth : Bool
  rebelsLedAstray : Bool
  covenantBroken : Bool
  commandedBondsSevered : Bool
  earthCorruption : Bool
  losersNamed : Bool
deriving DecidableEq, Repr

def gardenParableCovenantPattern : GardenParableCovenantPattern where
  believersDoGood := true
  gardensFlowingStreams := true
  recurringRecognizedSustenance := true
  pureSpousesAbiding := true
  smallParableAllowed := true
  believersKnowTruth := true
  rebelsLedAstray := true
  covenantBroken := true
  commandedBondsSevered := true
  earthCorruption := true
  losersNamed := true

structure LifeCreationReturnPattern where
  lifelessThenGivenLife : Bool
  causedToDie : Bool
  resurrected : Bool
  returnedToGod : Bool
  earthCreatedForYou : Bool
  skyTurnedToward : Bool
  sevenHeavensMade : Bool
  knowledgeOfAllThings : Bool
deriving DecidableEq, Repr

def lifeCreationReturnPattern : LifeCreationReturnPattern where
  lifelessThenGivenLife := true
  causedToDie := true
  resurrected := true
  returnedToGod := true
  earthCreatedForYou := true
  skyTurnedToward := true
  sevenHeavensMade := true
  knowledgeOfAllThings := true

theorem quran_al_baqara_worship_challenge_creation_witness :
    baqaraWorshipCreationMoments.length = 9
    ∧ baqaraWorshipCreationMoments.head? =
        some BaqaraWorshipCreationMoment.worshipCreator
    ∧ baqaraWorshipCreationMoments.getLast? =
        some BaqaraWorshipCreationMoment.sevenHeavensKnowledge
    ∧ worshipProvisionPattern.worshipLord = true
    ∧ worshipProvisionPattern.creatorOfPresentAndBefore = true
    ∧ worshipProvisionPattern.mindfulnessAim = true
    ∧ worshipProvisionPattern.rainSentDown = true
    ∧ worshipProvisionPattern.sustenanceProduced = true
    ∧ worshipProvisionPattern.rivalsRejected = true
    ∧ revelationChallengePattern.doubtNamed = true
    ∧ revelationChallengePattern.revelationSentToServant = true
    ∧ revelationChallengePattern.singleSuraChallenge = true
    ∧ revelationChallengePattern.challengeWillNotBeMet = true
    ∧ revelationChallengePattern.firePrepared = true
    ∧ gardenParableCovenantPattern.believersDoGood = true
    ∧ gardenParableCovenantPattern.gardensFlowingStreams = true
    ∧ gardenParableCovenantPattern.smallParableAllowed = true
    ∧ gardenParableCovenantPattern.rebelsLedAstray = true
    ∧ gardenParableCovenantPattern.commandedBondsSevered = true
    ∧ gardenParableCovenantPattern.earthCorruption = true
    ∧ lifeCreationReturnPattern.lifelessThenGivenLife = true
    ∧ lifeCreationReturnPattern.resurrected = true
    ∧ lifeCreationReturnPattern.returnedToGod = true
    ∧ lifeCreationReturnPattern.sevenHeavensMade = true
    ∧ lifeCreationReturnPattern.knowledgeOfAllThings = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rfl
  · rfl
  · rfl

end QuranAlBaqaraWorshipChallengeCreationWitness
end Gnosis.Witnesses.Islam
