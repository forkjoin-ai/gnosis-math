import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraQiblaCommunityWitness

/-!
# Quran 2:142-150, Al-Baqara -- Qibla and Just Community

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1421-1462`.

This bounded witness tracks the qibla reorientation unit:

  * foolish objection to changed prayer direction is answered by God's ownership of East and West;
  * believers are made a just community bearing witness before others;
  * the Messenger bears witness before the believers;
  * prayer direction distinguishes followers from those turning back;
  * faith is not wasted because God is compassionate and merciful;
  * the Prophet is turned toward the Sacred Mosque, and believers turn wherever they are;
  * Scripture recipients know the truth but some hide it;
  * communities have directions, while believers race to good deeds;
  * repeated direction to the Sacred Mosque closes with no fear of wrongdoers, fear of God,
    perfected favor, and guidance.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive QiblaCommunityMoment
  | foolishObjection
  | eastWestGuidance
  | justCommunityWitness
  | messengerWitness
  | directionTest
  | faithNotWasted
  | sacredMosqueTurn
  | scriptureKnowledgeHidden
  | raceToGood
  | perfectedFavorGuidance
deriving DecidableEq, Repr

def qiblaCommunityMoments : List QiblaCommunityMoment :=
  [ QiblaCommunityMoment.foolishObjection
  , QiblaCommunityMoment.eastWestGuidance
  , QiblaCommunityMoment.justCommunityWitness
  , QiblaCommunityMoment.messengerWitness
  , QiblaCommunityMoment.directionTest
  , QiblaCommunityMoment.faithNotWasted
  , QiblaCommunityMoment.sacredMosqueTurn
  , QiblaCommunityMoment.scriptureKnowledgeHidden
  , QiblaCommunityMoment.raceToGood
  , QiblaCommunityMoment.perfectedFavorGuidance
  ]

structure DirectionTestPattern where
  foolishPeopleObject : Bool
  previousDirectionNamed : Bool
  eastWestBelongToGod : Bool
  godGuidesWhomHeWill : Bool
  believersJustCommunity : Bool
  believersBearWitness : Bool
  messengerBearsWitness : Bool
  distinguishesFollowers : Bool
  distinguishesHeelTurners : Bool
  hardExceptGuided : Bool
  faithNotWasted : Bool
  compassionateMerciful : Bool
deriving DecidableEq, Repr

def directionTestPattern : DirectionTestPattern where
  foolishPeopleObject := true
  previousDirectionNamed := true
  eastWestBelongToGod := true
  godGuidesWhomHeWill := true
  believersJustCommunity := true
  believersBearWitness := true
  messengerBearsWitness := true
  distinguishesFollowers := true
  distinguishesHeelTurners := true
  hardExceptGuided := true
  faithNotWasted := true
  compassionateMerciful := true

structure SacredMosquePattern where
  prophetFaceHeavenSeen : Bool
  pleasingDirectionGiven : Bool
  sacredMosqueDirection : Bool
  believersTurnWherever : Bool
  scripturePeopleKnowTruth : Bool
  godNotUnaware : Bool
  everyProofRejected : Bool
  directionsNotMutuallyFollowed : Bool
  desiresAfterKnowledgeWrong : Bool
  truthHiddenKnowingly : Bool
  noDoubtCommand : Bool
deriving DecidableEq, Repr

def sacredMosquePattern : SacredMosquePattern where
  prophetFaceHeavenSeen := true
  pleasingDirectionGiven := true
  sacredMosqueDirection := true
  believersTurnWherever := true
  scripturePeopleKnowTruth := true
  godNotUnaware := true
  everyProofRejected := true
  directionsNotMutuallyFollowed := true
  desiresAfterKnowledgeWrong := true
  truthHiddenKnowingly := true
  noDoubtCommand := true

structure RaceFavorPattern where
  eachCommunityDirection : Bool
  raceToGoodDeeds : Bool
  godBringsTogether : Bool
  godPowerEverything : Bool
  repeatedSacredMosqueCommand : Bool
  noArgumentAgainstBelievers : Bool
  wrongdoersExcepted : Bool
  fearGodNotThem : Bool
  favorPerfected : Bool
  guidanceAim : Bool
deriving DecidableEq, Repr

def raceFavorPattern : RaceFavorPattern where
  eachCommunityDirection := true
  raceToGoodDeeds := true
  godBringsTogether := true
  godPowerEverything := true
  repeatedSacredMosqueCommand := true
  noArgumentAgainstBelievers := true
  wrongdoersExcepted := true
  fearGodNotThem := true
  favorPerfected := true
  guidanceAim := true

theorem quran_al_baqara_qibla_community_witness :
    qiblaCommunityMoments.length = 10
    ∧ qiblaCommunityMoments.head? = some QiblaCommunityMoment.foolishObjection
    ∧ qiblaCommunityMoments.getLast? = some QiblaCommunityMoment.perfectedFavorGuidance
    ∧ directionTestPattern.foolishPeopleObject = true
    ∧ directionTestPattern.eastWestBelongToGod = true
    ∧ directionTestPattern.believersJustCommunity = true
    ∧ directionTestPattern.believersBearWitness = true
    ∧ directionTestPattern.messengerBearsWitness = true
    ∧ directionTestPattern.distinguishesFollowers = true
    ∧ directionTestPattern.faithNotWasted = true
    ∧ sacredMosquePattern.prophetFaceHeavenSeen = true
    ∧ sacredMosquePattern.sacredMosqueDirection = true
    ∧ sacredMosquePattern.believersTurnWherever = true
    ∧ sacredMosquePattern.scripturePeopleKnowTruth = true
    ∧ sacredMosquePattern.everyProofRejected = true
    ∧ sacredMosquePattern.desiresAfterKnowledgeWrong = true
    ∧ sacredMosquePattern.truthHiddenKnowingly = true
    ∧ raceFavorPattern.eachCommunityDirection = true
    ∧ raceFavorPattern.raceToGoodDeeds = true
    ∧ raceFavorPattern.godBringsTogether = true
    ∧ raceFavorPattern.noArgumentAgainstBelievers = true
    ∧ raceFavorPattern.fearGodNotThem = true
    ∧ raceFavorPattern.favorPerfected = true
    ∧ raceFavorPattern.guidanceAim = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end QuranAlBaqaraQiblaCommunityWitness
end Gnosis.Witnesses.Islam
