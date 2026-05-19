import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlMaidaObligationsPurityJusticeWitness

/-!
# Quran 5:1-11, Al-Maida -- Obligations, Food, Purity, Pledge, and Justice

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:3441-3529`.

This bounded witness tracks the opening unit of Sura 5:

  * believers are commanded to fulfil obligations;
  * livestock is made lawful with named exceptions, and game-killing is forbidden during
    pilgrimage;
  * God's rites, Sacred Month, offerings, garlands, and pilgrims seeking the Sacred House
    are not to be violated;
  * hatred for those who barred access to the Sacred Mosque must not induce lawbreaking;
  * mutual help is commanded for what is right and good, not for sin and hostility;
  * forbidden foods are listed, including carrion, blood, pig's meat, wrongly invoked
    animals, certain dead animals, idolatrous sacrifice, and arrow-allotment;
  * the religion is perfected, blessing completed, and islam chosen as religion, with a
    hunger exception without intent to do wrong;
  * good things, trained hunting animals, People of the Book food, and chaste marriage
    with bride-gifts are treated as lawful;
  * prayer purity requires washing face, hands, head, and feet, or clean earth when water
    is unavailable under named conditions;
  * God wishes cleansing and perfected blessing rather than burden;
  * the pledge of hearing and obeying is remembered, and secrets of the heart are known;
  * believers must be steadfast for God and bear impartial witness, without hatred
    leading away from justice;
  * faith and good works receive forgiveness and rich reward, while rejection and denial
    lead to blazing Fire;
  * believers remember God's protection when hostile hands were restrained and trust Him.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive ObligationsPurityJusticeMoment
  | obligationsFulfilled
  | pilgrimageFoodBounds
  | sacredRitesProtected
  | hatredDoesNotBreakLaw
  | mutualHelpRightGood
  | forbiddenFoodsListed
  | perfectedReligion
  | lawfulGoodThings
  | prayerPurity
  | burdenLiftedBlessingPerfected
  | pledgeRemembered
  | impartialJustice
  | rewardAndFire
  | protectionAndTrust
deriving DecidableEq, Repr

def obligationsPurityJusticeMoments : List ObligationsPurityJusticeMoment :=
  [ ObligationsPurityJusticeMoment.obligationsFulfilled
  , ObligationsPurityJusticeMoment.pilgrimageFoodBounds
  , ObligationsPurityJusticeMoment.sacredRitesProtected
  , ObligationsPurityJusticeMoment.hatredDoesNotBreakLaw
  , ObligationsPurityJusticeMoment.mutualHelpRightGood
  , ObligationsPurityJusticeMoment.forbiddenFoodsListed
  , ObligationsPurityJusticeMoment.perfectedReligion
  , ObligationsPurityJusticeMoment.lawfulGoodThings
  , ObligationsPurityJusticeMoment.prayerPurity
  , ObligationsPurityJusticeMoment.burdenLiftedBlessingPerfected
  , ObligationsPurityJusticeMoment.pledgeRemembered
  , ObligationsPurityJusticeMoment.impartialJustice
  , ObligationsPurityJusticeMoment.rewardAndFire
  , ObligationsPurityJusticeMoment.protectionAndTrust
  ]

structure ObligationsPurityJusticePattern where
  obligationsCommanded : Bool
  pilgrimageGameForbidden : Bool
  sacredRitesNotViolated : Bool
  hatredDoesNotInduceLawbreaking : Bool
  helpRightNotSin : Bool
  forbiddenFoodListNamed : Bool
  religionPerfected : Bool
  blessingCompleted : Bool
  hungerExceptionNamed : Bool
  trainedHuntingLawful : Bool
  peopleBookFoodLawful : Bool
  chasteMarriageBrideGifts : Bool
  washingAndEarthPurity : Bool
  noBurdenCleansingBlessing : Bool
  pledgeHearObeyRemembered : Bool
  heartSecretsKnown : Bool
  impartialJusticeCommanded : Bool
  rewardFireContrasted : Bool
  hostileHandsRestrained : Bool
deriving DecidableEq, Repr

def obligationsPurityJusticePattern : ObligationsPurityJusticePattern where
  obligationsCommanded := true
  pilgrimageGameForbidden := true
  sacredRitesNotViolated := true
  hatredDoesNotInduceLawbreaking := true
  helpRightNotSin := true
  forbiddenFoodListNamed := true
  religionPerfected := true
  blessingCompleted := true
  hungerExceptionNamed := true
  trainedHuntingLawful := true
  peopleBookFoodLawful := true
  chasteMarriageBrideGifts := true
  washingAndEarthPurity := true
  noBurdenCleansingBlessing := true
  pledgeHearObeyRemembered := true
  heartSecretsKnown := true
  impartialJusticeCommanded := true
  rewardFireContrasted := true
  hostileHandsRestrained := true

theorem quran_al_maida_obligations_purity_justice_witness :
    obligationsPurityJusticeMoments.length = 14
    ∧ obligationsPurityJusticeMoments.head? = some ObligationsPurityJusticeMoment.obligationsFulfilled
    ∧ obligationsPurityJusticeMoments.getLast? = some ObligationsPurityJusticeMoment.protectionAndTrust
    ∧ obligationsPurityJusticePattern.obligationsCommanded = true
    ∧ obligationsPurityJusticePattern.pilgrimageGameForbidden = true
    ∧ obligationsPurityJusticePattern.sacredRitesNotViolated = true
    ∧ obligationsPurityJusticePattern.hatredDoesNotInduceLawbreaking = true
    ∧ obligationsPurityJusticePattern.helpRightNotSin = true
    ∧ obligationsPurityJusticePattern.forbiddenFoodListNamed = true
    ∧ obligationsPurityJusticePattern.religionPerfected = true
    ∧ obligationsPurityJusticePattern.blessingCompleted = true
    ∧ obligationsPurityJusticePattern.hungerExceptionNamed = true
    ∧ obligationsPurityJusticePattern.trainedHuntingLawful = true
    ∧ obligationsPurityJusticePattern.peopleBookFoodLawful = true
    ∧ obligationsPurityJusticePattern.chasteMarriageBrideGifts = true
    ∧ obligationsPurityJusticePattern.washingAndEarthPurity = true
    ∧ obligationsPurityJusticePattern.noBurdenCleansingBlessing = true
    ∧ obligationsPurityJusticePattern.pledgeHearObeyRemembered = true
    ∧ obligationsPurityJusticePattern.heartSecretsKnown = true
    ∧ obligationsPurityJusticePattern.impartialJusticeCommanded = true
    ∧ obligationsPurityJusticePattern.rewardFireContrasted = true
    ∧ obligationsPurityJusticePattern.hostileHandsRestrained = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlMaidaObligationsPurityJusticeWitness
end Gnosis.Witnesses.Islam
