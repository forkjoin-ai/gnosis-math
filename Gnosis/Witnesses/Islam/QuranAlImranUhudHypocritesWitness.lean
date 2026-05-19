import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlImranUhudHypocritesWitness

/-!
# Quran 3:149-168, Al Imran -- Uhud, Pardon, Trust, Gains, and Hypocrites

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:2572-2651`.

This bounded witness tracks Quran 3:149-168:

  * believers are warned not to obey disbelievers and turn back;
  * God is protector and best helper;
  * panic is cast into disbelieving hearts because partners are assigned without warrant;
  * the Uhud promise is described through early victory, faltering, dispute, disobedience,
    worldly desire, pardon, and sorrow;
  * calm sleep covers some while others harbor ignorant thoughts about God;
  * concealed speech about command and death is answered by destiny and heart testing;
  * Satan causes some to slip, but God pardons;
  * believers must not imitate disbelieving speech about travel and raids;
  * God's forgiveness and mercy exceed what is amassed;
  * the Prophet's gentleness is by mercy from God, with pardon, forgiveness-seeking,
    consultation, and trust;
  * divine help cannot be overcome, and without it no helper remains;
  * prophets do not dishonestly take gains, and each soul is repaid;
  * the Messenger recites, purifies, and teaches after clear error;
  * calamity is traced to the believers themselves and separates believers from hypocrites;
  * those who stayed behind speak with tongues what is not in hearts.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive UhudHypocritesMoment
  | doNotTurnBack
  | godProtector
  | panicInHearts
  | uhudPromiseAndPardon
  | calmAndIgnorantThoughts
  | destinyAndHeartTest
  | satanSlipPardoned
  | deathSpeechWarning
  | mercyConsultTrust
  | helpOnlyGod
  | dishonestGainsRejected
  | messengerPurifiesTeaches
  | calamityFromYourselves
  | hypocriteSpeechExposed
deriving DecidableEq, Repr

def uhudHypocritesMoments : List UhudHypocritesMoment :=
  [ UhudHypocritesMoment.doNotTurnBack
  , UhudHypocritesMoment.godProtector
  , UhudHypocritesMoment.panicInHearts
  , UhudHypocritesMoment.uhudPromiseAndPardon
  , UhudHypocritesMoment.calmAndIgnorantThoughts
  , UhudHypocritesMoment.destinyAndHeartTest
  , UhudHypocritesMoment.satanSlipPardoned
  , UhudHypocritesMoment.deathSpeechWarning
  , UhudHypocritesMoment.mercyConsultTrust
  , UhudHypocritesMoment.helpOnlyGod
  , UhudHypocritesMoment.dishonestGainsRejected
  , UhudHypocritesMoment.messengerPurifiesTeaches
  , UhudHypocritesMoment.calamityFromYourselves
  , UhudHypocritesMoment.hypocriteSpeechExposed
  ]

structure UhudHypocritesPattern where
  disbelieverObedienceWarned : Bool
  godBestHelper : Bool
  partnerPanicNamed : Bool
  uhudFalteringDisputeDisobedience : Bool
  godPardoned : Bool
  calmSleepAndAnxiety : Bool
  destinedDeathsNamed : Bool
  heartTestNamed : Bool
  satanSlipPardoned : Bool
  disbelieverDeathSpeechRejected : Bool
  prophetGentleByMercy : Bool
  consultationAndTrust : Bool
  dishonestGainsRejected : Bool
  messengerRecitesPurifiesTeaches : Bool
  believersHypocritesSeparated : Bool
  tongueHeartGapNamed : Bool
deriving DecidableEq, Repr

def uhudHypocritesPattern : UhudHypocritesPattern where
  disbelieverObedienceWarned := true
  godBestHelper := true
  partnerPanicNamed := true
  uhudFalteringDisputeDisobedience := true
  godPardoned := true
  calmSleepAndAnxiety := true
  destinedDeathsNamed := true
  heartTestNamed := true
  satanSlipPardoned := true
  disbelieverDeathSpeechRejected := true
  prophetGentleByMercy := true
  consultationAndTrust := true
  dishonestGainsRejected := true
  messengerRecitesPurifiesTeaches := true
  believersHypocritesSeparated := true
  tongueHeartGapNamed := true

theorem quran_al_imran_uhud_hypocrites_witness :
    uhudHypocritesMoments.length = 14
    ∧ uhudHypocritesMoments.head? = some UhudHypocritesMoment.doNotTurnBack
    ∧ uhudHypocritesMoments.getLast? = some UhudHypocritesMoment.hypocriteSpeechExposed
    ∧ uhudHypocritesPattern.disbelieverObedienceWarned = true
    ∧ uhudHypocritesPattern.godBestHelper = true
    ∧ uhudHypocritesPattern.partnerPanicNamed = true
    ∧ uhudHypocritesPattern.uhudFalteringDisputeDisobedience = true
    ∧ uhudHypocritesPattern.godPardoned = true
    ∧ uhudHypocritesPattern.calmSleepAndAnxiety = true
    ∧ uhudHypocritesPattern.destinedDeathsNamed = true
    ∧ uhudHypocritesPattern.heartTestNamed = true
    ∧ uhudHypocritesPattern.satanSlipPardoned = true
    ∧ uhudHypocritesPattern.disbelieverDeathSpeechRejected = true
    ∧ uhudHypocritesPattern.prophetGentleByMercy = true
    ∧ uhudHypocritesPattern.consultationAndTrust = true
    ∧ uhudHypocritesPattern.dishonestGainsRejected = true
    ∧ uhudHypocritesPattern.messengerRecitesPurifiesTeaches = true
    ∧ uhudHypocritesPattern.believersHypocritesSeparated = true
    ∧ uhudHypocritesPattern.tongueHeartGapNamed = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlImranUhudHypocritesWitness
end Gnosis.Witnesses.Islam
