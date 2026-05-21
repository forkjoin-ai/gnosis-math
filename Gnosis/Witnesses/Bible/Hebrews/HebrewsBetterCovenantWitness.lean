namespace Gnosis.Witnesses.Bible.Hebrews
namespace HebrewsBetterCovenantWitness

/-!
# Hebrews 8 -- True Tabernacle and Better Covenant

Source slice: Hebrews 8:1-13.

Chapter invariant: the high priest's seat determines the ministry's register.
The argument is not anti-tabernacle; Moses' pattern is honored precisely as
pattern. But the priest now ministers at the right hand in the true tabernacle,
pitched by the Lord and not by man.

Primary gap/counterproof: shadow service cannot carry covenant finality. If the
first covenant had been faultless, no second would be sought; if the old covenant
decays, it cannot be treated as the final form of nearness.

Unseen sat: better covenant means interiorized address, not mere replacement
branding. Law is put into mind and written in heart; peoplehood is restored;
knowledge is democratized from least to greatest; mercy includes remembered-no-
more iniquity.

No `sorry`, no new `axiom`.
-/

structure HeavenlySanctuary where
  priestSeatedAtRightHand : Bool := true
  trueTabernaclePitchedByLord : Bool := true
  priestMustHaveOffering : Bool := true
  earthlyServiceIsExampleAndShadow : Bool := true
  mosesFollowsShownPattern : Bool := true
deriving DecidableEq, Repr

def heavenlySanctuary : HeavenlySanctuary := {}

def heavenlySanctuaryWitness (s : HeavenlySanctuary) : Prop :=
  s.priestSeatedAtRightHand = true ∧
  s.trueTabernaclePitchedByLord = true ∧
  s.priestMustHaveOffering = true ∧
  s.earthlyServiceIsExampleAndShadow = true ∧
  s.mosesFollowsShownPattern = true

structure BetterCovenant where
  moreExcellentMinistry : Bool := true
  betterCovenantMediated : Bool := true
  betterPromisesEstablished : Bool := true
  secondSoughtBecauseFirstFaulted : Bool := true
deriving DecidableEq, Repr

def betterCovenant : BetterCovenant := {}

def betterCovenantWitness (c : BetterCovenant) : Prop :=
  c.moreExcellentMinistry = true ∧
  c.betterCovenantMediated = true ∧
  c.betterPromisesEstablished = true ∧
  c.secondSoughtBecauseFirstFaulted = true

structure InternalizedCovenantCounterproof where
  exodusHandLeadingDidNotSecureContinuance : Bool := true
  lawWrittenInMindAndHeart : Bool := true
  godPeopleRelationRestored : Bool := true
  leastToGreatestKnowTheLord : Bool := true
  sinsRememberedNoMore : Bool := true
  oldCovenantReadyToVanish : Bool := true
deriving DecidableEq, Repr

def internalizedCovenantCounterproof : InternalizedCovenantCounterproof := {}

def shadowFinalityRejected (c : InternalizedCovenantCounterproof) : Prop :=
  c.exodusHandLeadingDidNotSecureContinuance = true ∧
  c.lawWrittenInMindAndHeart = true ∧
  c.godPeopleRelationRestored = true ∧
  c.leastToGreatestKnowTheLord = true ∧
  c.sinsRememberedNoMore = true ∧
  c.oldCovenantReadyToVanish = true

theorem hebrews_heavenly_sanctuary :
    heavenlySanctuaryWitness heavenlySanctuary := by
  unfold heavenlySanctuaryWitness heavenlySanctuary
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_better_covenant :
    betterCovenantWitness betterCovenant := by
  unfold betterCovenantWitness betterCovenant
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem hebrews_shadow_finality_rejected :
    shadowFinalityRejected internalizedCovenantCounterproof := by
  unfold shadowFinalityRejected internalizedCovenantCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_better_covenant_witness :
    heavenlySanctuaryWitness heavenlySanctuary ∧
    betterCovenantWitness betterCovenant ∧
    shadowFinalityRejected internalizedCovenantCounterproof := by
  exact ⟨hebrews_heavenly_sanctuary,
    hebrews_better_covenant,
    hebrews_shadow_finality_rejected⟩

end HebrewsBetterCovenantWitness
end Gnosis.Witnesses.Bible.Hebrews
