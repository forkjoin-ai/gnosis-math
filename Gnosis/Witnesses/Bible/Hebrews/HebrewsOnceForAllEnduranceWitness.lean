namespace Gnosis.Witnesses.Bible.Hebrews
namespace HebrewsOnceForAllEnduranceWitness

/-!
# Hebrews 10 -- Once-for-All Offering, Bold Entry, and Endurance

Source slice: Hebrews 10:1-39.

Chapter invariant: repeated sacrifice is not deeper devotion when repetition is
the machine preserving failure. The law's shadow can remember sins yearly, but
if worshippers were once purged the offerings would cease; bulls and goats
cannot take away sins.

Primary gap/counterproof: finality is embodied obedience, not ritual repetition.
The prepared body comes to do God's will, takes away the first to establish the
second, sanctifies by one offering once for all, and sits where daily standing
priests cannot.

Unseen sat: opened access is not spiritual privacy. The new living way through
the flesh-veil creates a people who can stop feeding the old guilt economy:
full assurance, unwavering confession, provoking love and works, assembly,
warning against willful contempt, and patient faith that does not draw back.

No `sorry`, no new `axiom`.
-/

structure ShadowSacrificeCounterproof where
  lawHasShadowNotImage : Bool := true
  yearlySacrificeCannotPerfectComers : Bool := true
  repeatedOfferingRemembersSin : Bool := true
  animalBloodCannotTakeAwaySin : Bool := true
deriving DecidableEq, Repr

def shadowSacrificeCounterproof : ShadowSacrificeCounterproof := {}

def repeatedSacrificeRejected (c : ShadowSacrificeCounterproof) : Prop :=
  c.lawHasShadowNotImage = true ∧
  c.yearlySacrificeCannotPerfectComers = true ∧
  c.repeatedOfferingRemembersSin = true ∧
  c.animalBloodCannotTakeAwaySin = true

structure OnceForAllOffering where
  preparedBodyDoesWill : Bool := true
  firstTakenAwaySecondEstablished : Bool := true
  sanctifiedOnceForAll : Bool := true
  oneOfferingPerfectsForever : Bool := true
  noMoreOfferingWhereRemissionIs : Bool := true
deriving DecidableEq, Repr

def onceForAllOffering : OnceForAllOffering := {}

def onceForAllWitness (o : OnceForAllOffering) : Prop :=
  o.preparedBodyDoesWill = true ∧
  o.firstTakenAwaySecondEstablished = true ∧
  o.sanctifiedOnceForAll = true ∧
  o.oneOfferingPerfectsForever = true ∧
  o.noMoreOfferingWhereRemissionIs = true

structure BoldEntryCommunity where
  boldnessByBloodIntoHoliest : Bool := true
  livingWayThroughFleshVeil : Bool := true
  drawNearWithSprinkledHeart : Bool := true
  holdFastWithoutWavering : Bool := true
  provokeLoveAndGoodWorks : Bool := true
  assembleAndExhortAsDayApproaches : Bool := true
deriving DecidableEq, Repr

def boldEntryCommunity : BoldEntryCommunity := {}

def boldEntryCommunityWitness (b : BoldEntryCommunity) : Prop :=
  b.boldnessByBloodIntoHoliest = true ∧
  b.livingWayThroughFleshVeil = true ∧
  b.drawNearWithSprinkledHeart = true ∧
  b.holdFastWithoutWavering = true ∧
  b.provokeLoveAndGoodWorks = true ∧
  b.assembleAndExhortAsDayApproaches = true

structure WillfulSinEndurance where
  willfulSinLeavesNoMoreSacrifice : Bool := true
  covenantBloodCannotBeMadeUnholy : Bool := true
  livingGodJudgmentIsFearful : Bool := true
  illuminatedAfflictionWasEndured : Bool := true
  confidenceHasGreatReward : Bool := true
  justLiveByFaithWithoutDrawingBack : Bool := true
deriving DecidableEq, Repr

def willfulSinEndurance : WillfulSinEndurance := {}

def enduranceWarningWitness (w : WillfulSinEndurance) : Prop :=
  w.willfulSinLeavesNoMoreSacrifice = true ∧
  w.covenantBloodCannotBeMadeUnholy = true ∧
  w.livingGodJudgmentIsFearful = true ∧
  w.illuminatedAfflictionWasEndured = true ∧
  w.confidenceHasGreatReward = true ∧
  w.justLiveByFaithWithoutDrawingBack = true

theorem hebrews_repeated_sacrifice_rejected :
    repeatedSacrificeRejected shadowSacrificeCounterproof := by
  unfold repeatedSacrificeRejected shadowSacrificeCounterproof
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem hebrews_once_for_all :
    onceForAllWitness onceForAllOffering := by
  unfold onceForAllWitness onceForAllOffering
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_bold_entry_community :
    boldEntryCommunityWitness boldEntryCommunity := by
  unfold boldEntryCommunityWitness boldEntryCommunity
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_endurance_warning :
    enduranceWarningWitness willfulSinEndurance := by
  unfold enduranceWarningWitness willfulSinEndurance
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_once_for_all_endurance_witness :
    repeatedSacrificeRejected shadowSacrificeCounterproof ∧
    onceForAllWitness onceForAllOffering ∧
    boldEntryCommunityWitness boldEntryCommunity ∧
    enduranceWarningWitness willfulSinEndurance := by
  exact ⟨hebrews_repeated_sacrifice_rejected,
    hebrews_once_for_all,
    hebrews_bold_entry_community,
    hebrews_endurance_warning⟩

end HebrewsOnceForAllEnduranceWitness
end Gnosis.Witnesses.Bible.Hebrews
