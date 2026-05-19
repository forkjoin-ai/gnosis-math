import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlNisaWomenJusticeHypocritesWitness

/-!
# Quran 4:127-149, An-Nisa -- Women, Settlement, Justice, and Hypocrites

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:3266-3346`.

This bounded witness tracks Quran 4:127-149:

  * God gives a ruling about women, orphan girls, withheld shares, desired marriage, and
    helpless children;
  * orphans must be treated fairly, and God knows whatever good is done;
  * peaceful settlement between spouses is permitted when alienation or high-handedness
    is feared;
  * peace is best, souls are prone to selfishness, and fairness must avoid leaving one
    wife suspended;
  * separation is met by God's provision from His plenty;
  * everything in the heavens and earth belongs to God, and mindfulness is commanded to
    earlier Scripture communities and to believers;
  * God can replace people, owns rewards of this world and the next, and hears and sees;
  * believers uphold justice and bear witness to God even against self, parents, or kin;
  * belief is commanded in God, Messenger, Scripture, earlier Scripture, angels, messengers,
    and the Last Day;
  * repeated belief and rejection, hypocrite alliance-seeking, and sitting with revelation
    denial and ridicule are warned against;
  * hypocrites waver, show off in prayer, remember little, and face the lowest depths of Hell;
  * repentant hypocrites who mend, hold fast to God, and devote religion to Him join believers;
  * bad public words are disliked unless someone is wronged, while open or secret good and
    pardon reflect God's forgiveness and power.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive WomenJusticeHypocritesMoment
  | womenRuling
  | orphanFairness
  | peacefulSettlement
  | suspendedFairnessWarning
  | separationProvision
  | mindfulnessCommand
  | justiceWitness
  | comprehensiveBelief
  | hypocriteAllianceWarning
  | ridiculeSittingWarning
  | hypocritePrayerWavering
  | repentantHypocrites
  | publicBadWordsPardon
deriving DecidableEq, Repr

def womenJusticeHypocritesMoments : List WomenJusticeHypocritesMoment :=
  [ WomenJusticeHypocritesMoment.womenRuling
  , WomenJusticeHypocritesMoment.orphanFairness
  , WomenJusticeHypocritesMoment.peacefulSettlement
  , WomenJusticeHypocritesMoment.suspendedFairnessWarning
  , WomenJusticeHypocritesMoment.separationProvision
  , WomenJusticeHypocritesMoment.mindfulnessCommand
  , WomenJusticeHypocritesMoment.justiceWitness
  , WomenJusticeHypocritesMoment.comprehensiveBelief
  , WomenJusticeHypocritesMoment.hypocriteAllianceWarning
  , WomenJusticeHypocritesMoment.ridiculeSittingWarning
  , WomenJusticeHypocritesMoment.hypocritePrayerWavering
  , WomenJusticeHypocritesMoment.repentantHypocrites
  , WomenJusticeHypocritesMoment.publicBadWordsPardon
  ]

structure WomenJusticeHypocritesPattern where
  womenRulingFromGod : Bool
  orphanGirlsSharesNamed : Bool
  helplessChildrenNamed : Bool
  peaceBest : Bool
  selfishnessAndAmendsNamed : Bool
  godProvidesAfterSeparation : Bool
  heavensEarthBelongGod : Bool
  justiceAgainstSelfKin : Bool
  richPoorGodCares : Bool
  comprehensiveBeliefCommanded : Bool
  disbelieverAlliancePowerRejected : Bool
  ridiculeSittingForbidden : Bool
  hypocriteWaveringNamed : Bool
  lowestDepthsHell : Bool
  repentanceMendingHoldingFast : Bool
  publicWrongPardonNamed : Bool
deriving DecidableEq, Repr

def womenJusticeHypocritesPattern : WomenJusticeHypocritesPattern where
  womenRulingFromGod := true
  orphanGirlsSharesNamed := true
  helplessChildrenNamed := true
  peaceBest := true
  selfishnessAndAmendsNamed := true
  godProvidesAfterSeparation := true
  heavensEarthBelongGod := true
  justiceAgainstSelfKin := true
  richPoorGodCares := true
  comprehensiveBeliefCommanded := true
  disbelieverAlliancePowerRejected := true
  ridiculeSittingForbidden := true
  hypocriteWaveringNamed := true
  lowestDepthsHell := true
  repentanceMendingHoldingFast := true
  publicWrongPardonNamed := true

theorem quran_al_nisa_women_justice_hypocrites_witness :
    womenJusticeHypocritesMoments.length = 13
    ∧ womenJusticeHypocritesMoments.head? = some WomenJusticeHypocritesMoment.womenRuling
    ∧ womenJusticeHypocritesMoments.getLast? = some WomenJusticeHypocritesMoment.publicBadWordsPardon
    ∧ womenJusticeHypocritesPattern.womenRulingFromGod = true
    ∧ womenJusticeHypocritesPattern.orphanGirlsSharesNamed = true
    ∧ womenJusticeHypocritesPattern.helplessChildrenNamed = true
    ∧ womenJusticeHypocritesPattern.peaceBest = true
    ∧ womenJusticeHypocritesPattern.selfishnessAndAmendsNamed = true
    ∧ womenJusticeHypocritesPattern.godProvidesAfterSeparation = true
    ∧ womenJusticeHypocritesPattern.heavensEarthBelongGod = true
    ∧ womenJusticeHypocritesPattern.justiceAgainstSelfKin = true
    ∧ womenJusticeHypocritesPattern.richPoorGodCares = true
    ∧ womenJusticeHypocritesPattern.comprehensiveBeliefCommanded = true
    ∧ womenJusticeHypocritesPattern.disbelieverAlliancePowerRejected = true
    ∧ womenJusticeHypocritesPattern.ridiculeSittingForbidden = true
    ∧ womenJusticeHypocritesPattern.hypocriteWaveringNamed = true
    ∧ womenJusticeHypocritesPattern.lowestDepthsHell = true
    ∧ womenJusticeHypocritesPattern.repentanceMendingHoldingFast = true
    ∧ womenJusticeHypocritesPattern.publicWrongPardonNamed = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlNisaWomenJusticeHypocritesWitness
end Gnosis.Witnesses.Islam
