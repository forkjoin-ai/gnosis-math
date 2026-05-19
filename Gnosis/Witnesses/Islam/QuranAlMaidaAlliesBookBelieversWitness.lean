import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlMaidaAlliesBookBelieversWitness

/-!
# Quran 5:51-86, Al-Maida -- Allies, Ridicule, People of the Book, Messiah Claims, and Believing Witnesses

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:3688-3811`.

This bounded witness tracks Quran 5:51-86:

  * believers are warned against taking hostile Jews and Christians as preferred allies;
  * perverse hearts seek protection and later rue hidden secrets when God brings triumph;
  * if some turn back, God can replace them with people He loves and who love Him;
  * true allies are God, His Messenger, and praying, almsgiving, worshipping believers;
  * ridicule of religion and prayer is rejected;
  * hidden disbelief, sinful speech, unlawful consumption, tight-fisted claims about God,
    corruption, enmity, and failure to forbid wrong are exposed;
  * People of the Book are called to uphold Torah, Gospel, and what was sent down;
  * believers, Jews, Sabians, and Christians who believe in God and the Last Day and do
    good deeds have no fear or grief;
  * Israel's pledge and messenger rejection are recalled;
  * claims that God is the Messiah or the third of three are rejected in favor of one God;
  * Jesus is only a messenger, his mother virtuous, and both ate food;
  * bounds of truth in religion must not be exceeded;
  * those closest in affection include non-arrogant Christians devoted to learning and
    ascetic discipline;
  * hearing revelation brings tears, recognition of truth, witness, longing for the
    righteous, Gardens, and contrast with Hellfire.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive AlliesBookBelieversMoment
  | hostileAlliesWarning
  | hiddenSecretsRued
  | replacementBelovedPeople
  | trueAllies
  | ridiculeRejected
  | unlawfulCorruptionExposed
  | upholdScriptures
  | noFearNoGrief
  | israelMessengerRejection
  | messiahClaimsRejected
  | jesusMessengerHumanity
  | religiousExcessForbidden
  | closeAffection
  | tearsAndWitness
  | gardensAndHellfire
deriving DecidableEq, Repr

def alliesBookBelieversMoments : List AlliesBookBelieversMoment :=
  [ AlliesBookBelieversMoment.hostileAlliesWarning
  , AlliesBookBelieversMoment.hiddenSecretsRued
  , AlliesBookBelieversMoment.replacementBelovedPeople
  , AlliesBookBelieversMoment.trueAllies
  , AlliesBookBelieversMoment.ridiculeRejected
  , AlliesBookBelieversMoment.unlawfulCorruptionExposed
  , AlliesBookBelieversMoment.upholdScriptures
  , AlliesBookBelieversMoment.noFearNoGrief
  , AlliesBookBelieversMoment.israelMessengerRejection
  , AlliesBookBelieversMoment.messiahClaimsRejected
  , AlliesBookBelieversMoment.jesusMessengerHumanity
  , AlliesBookBelieversMoment.religiousExcessForbidden
  , AlliesBookBelieversMoment.closeAffection
  , AlliesBookBelieversMoment.tearsAndWitness
  , AlliesBookBelieversMoment.gardensAndHellfire
  ]

structure AlliesBookBelieversPattern where
  hostileAllianceWarning : Bool
  godPartyTriumph : Bool
  ridiculePrayerNamed : Bool
  unlawfulConsumptionCondemned : Bool
  tightFistedClaimRejected : Bool
  corruptionNotLoved : Bool
  upholdTorahGospelRequired : Bool
  noFearNoGriefPromise : Bool
  messengerRejectionPattern : Bool
  messiahDivinityRejected : Bool
  trinityClaimRejected : Bool
  jesusAndMaryHumanSigns : Bool
  boundsTruthNotExceeded : Bool
  wrongNotForbiddenCondemned : Bool
  affectionateWitnessesNamed : Bool
  tearsRecognitionTruth : Bool
  gardensHellfireContrasted : Bool
deriving DecidableEq, Repr

def alliesBookBelieversPattern : AlliesBookBelieversPattern where
  hostileAllianceWarning := true
  godPartyTriumph := true
  ridiculePrayerNamed := true
  unlawfulConsumptionCondemned := true
  tightFistedClaimRejected := true
  corruptionNotLoved := true
  upholdTorahGospelRequired := true
  noFearNoGriefPromise := true
  messengerRejectionPattern := true
  messiahDivinityRejected := true
  trinityClaimRejected := true
  jesusAndMaryHumanSigns := true
  boundsTruthNotExceeded := true
  wrongNotForbiddenCondemned := true
  affectionateWitnessesNamed := true
  tearsRecognitionTruth := true
  gardensHellfireContrasted := true

theorem quran_al_maida_allies_book_believers_witness :
    alliesBookBelieversMoments.length = 15
    ∧ alliesBookBelieversMoments.head? = some AlliesBookBelieversMoment.hostileAlliesWarning
    ∧ alliesBookBelieversMoments.getLast? = some AlliesBookBelieversMoment.gardensAndHellfire
    ∧ alliesBookBelieversPattern.hostileAllianceWarning = true
    ∧ alliesBookBelieversPattern.godPartyTriumph = true
    ∧ alliesBookBelieversPattern.ridiculePrayerNamed = true
    ∧ alliesBookBelieversPattern.unlawfulConsumptionCondemned = true
    ∧ alliesBookBelieversPattern.tightFistedClaimRejected = true
    ∧ alliesBookBelieversPattern.corruptionNotLoved = true
    ∧ alliesBookBelieversPattern.upholdTorahGospelRequired = true
    ∧ alliesBookBelieversPattern.noFearNoGriefPromise = true
    ∧ alliesBookBelieversPattern.messengerRejectionPattern = true
    ∧ alliesBookBelieversPattern.messiahDivinityRejected = true
    ∧ alliesBookBelieversPattern.trinityClaimRejected = true
    ∧ alliesBookBelieversPattern.jesusAndMaryHumanSigns = true
    ∧ alliesBookBelieversPattern.boundsTruthNotExceeded = true
    ∧ alliesBookBelieversPattern.wrongNotForbiddenCondemned = true
    ∧ alliesBookBelieversPattern.affectionateWitnessesNamed = true
    ∧ alliesBookBelieversPattern.tearsRecognitionTruth = true
    ∧ alliesBookBelieversPattern.gardensHellfireContrasted = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlMaidaAlliesBookBelieversWitness
end Gnosis.Witnesses.Islam
