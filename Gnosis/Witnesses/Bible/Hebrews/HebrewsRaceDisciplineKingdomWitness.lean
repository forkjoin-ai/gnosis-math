namespace Gnosis.Witnesses.Bible.Hebrews
namespace HebrewsRaceDisciplineKingdomWitness

/-!
# Hebrews 12 -- Race, Discipline, Zion, and the Unshaken Kingdom

Source slice: Hebrews 12:1-29.

Chapter invariant: the cloud of witnesses is not audience decoration; it is
pressure to run. The faith ledger becomes motion: lay aside weight, refuse
besetting sin, look to Jesus as author and finisher, and endure without fainting.

Primary gap/counterproof: pain is not automatically rejection, and comfort is
not automatically sonship. Chastening is grievous in the present but yields
peaceable fruit; lack of discipline is the suspicious condition, not proof of
freedom.

Unseen sat: the kingdom is known by what remains after shaking. Sinai's touchable
terror is not the final mountain; Zion gathers living city, firstborn assembly,
perfected spirits, better-speaking blood, and the voice from heaven. What can be
shaken is removed so the unshaken may be received with reverence.

No `sorry`, no new `axiom`.
-/

structure WitnessRace where
  cloudOfWitnessesPressesMotion : Bool := true
  weightAndSinAreLaidAside : Bool := true
  patienceRunsAssignedRace : Bool := true
  jesusAuthorsAndFinishesFaith : Bool := true
  contradictionEnduredAgainstWeariness : Bool := true
deriving DecidableEq, Repr

def witnessRace : WitnessRace := {}

def witnessRaceWitness (r : WitnessRace) : Prop :=
  r.cloudOfWitnessesPressesMotion = true ∧
  r.weightAndSinAreLaidAside = true ∧
  r.patienceRunsAssignedRace = true ∧
  r.jesusAuthorsAndFinishesFaith = true ∧
  r.contradictionEnduredAgainstWeariness = true

structure DisciplineSonship where
  chasteningBelongsToReceivedSons : Bool := true
  fatherOfSpiritsDisciplinesForLife : Bool := true
  holinessIsTheProfitOfDiscipline : Bool := true
  grievousTrainingYieldsPeaceableFruit : Bool := true
  lamePathIsStraightenedForHealing : Bool := true
deriving DecidableEq, Repr

def disciplineSonship : DisciplineSonship := {}

def disciplineSonshipWitness (d : DisciplineSonship) : Prop :=
  d.chasteningBelongsToReceivedSons = true ∧
  d.fatherOfSpiritsDisciplinesForLife = true ∧
  d.holinessIsTheProfitOfDiscipline = true ∧
  d.grievousTrainingYieldsPeaceableFruit = true ∧
  d.lamePathIsStraightenedForHealing = true

structure BitterTradeCounterproof where
  peaceAndHolinessMustBeFollowed : Bool := true
  bitternessDefilesMany : Bool := true
  esauTradesBirthrightForMorsel : Bool := true
  tearsCannotAlwaysRecoverDespisedInheritance : Bool := true
deriving DecidableEq, Repr

def bitterTradeCounterproof : BitterTradeCounterproof := {}

def shortTermTradeRejected (c : BitterTradeCounterproof) : Prop :=
  c.peaceAndHolinessMustBeFollowed = true ∧
  c.bitternessDefilesMany = true ∧
  c.esauTradesBirthrightForMorsel = true ∧
  c.tearsCannotAlwaysRecoverDespisedInheritance = true

structure UnshakenKingdom where
  sinaiTouchableTerrorIsNotFinalMountain : Bool := true
  zionGathersLivingCityAndFirstbornAssembly : Bool := true
  betterBloodSpeaksBeyondAbel : Bool := true
  heavenlyVoiceMustNotBeRefused : Bool := true
  shakingRemovesMadeThings : Bool := true
  unmovableKingdomRequiresReverentService : Bool := true
deriving DecidableEq, Repr

def unshakenKingdom : UnshakenKingdom := {}

def unshakenKingdomWitness (k : UnshakenKingdom) : Prop :=
  k.sinaiTouchableTerrorIsNotFinalMountain = true ∧
  k.zionGathersLivingCityAndFirstbornAssembly = true ∧
  k.betterBloodSpeaksBeyondAbel = true ∧
  k.heavenlyVoiceMustNotBeRefused = true ∧
  k.shakingRemovesMadeThings = true ∧
  k.unmovableKingdomRequiresReverentService = true

theorem hebrews_witness_race :
    witnessRaceWitness witnessRace := by
  unfold witnessRaceWitness witnessRace
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_discipline_sonship :
    disciplineSonshipWitness disciplineSonship := by
  unfold disciplineSonshipWitness disciplineSonship
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_short_term_trade_rejected :
    shortTermTradeRejected bitterTradeCounterproof := by
  unfold shortTermTradeRejected bitterTradeCounterproof
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem hebrews_unshaken_kingdom :
    unshakenKingdomWitness unshakenKingdom := by
  unfold unshakenKingdomWitness unshakenKingdom
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_race_discipline_kingdom_witness :
    witnessRaceWitness witnessRace ∧
    disciplineSonshipWitness disciplineSonship ∧
    shortTermTradeRejected bitterTradeCounterproof ∧
    unshakenKingdomWitness unshakenKingdom := by
  exact ⟨hebrews_witness_race,
    hebrews_discipline_sonship,
    hebrews_short_term_trade_rejected,
    hebrews_unshaken_kingdom⟩

end HebrewsRaceDisciplineKingdomWitness
end Gnosis.Witnesses.Bible.Hebrews
