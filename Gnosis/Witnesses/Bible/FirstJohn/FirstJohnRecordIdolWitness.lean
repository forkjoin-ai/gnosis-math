namespace Gnosis.Witnesses.Bible.FirstJohn
namespace FirstJohnRecordIdolWitness

/-!
# 1 John 5 -- Water, Blood, Spirit, Petition, and the Idol Firewall

Source slice: 1 John 5:1-21.

Chapter invariant: victory over the world is faith attested by converging
witness, not private intensity. Water, blood, and Spirit agree; the record is
received, internalized, and bound to the Son as life.

Primary gap/counterproof: unbelief is not neutral skepticism in this ledger. To
reject the record God gives of the Son makes God a liar, just as chapter 1's
sin-denial did. The book begins and ends by making false claims costly.

Unseen sat: the final "keep yourselves from idols" is not an afterthought. It is
the firewall implied by the whole book: every substitute record, substitute
love, substitute Christ, substitute world, and substitute confidence must be
refused. The water/blood/Spirit witness is also the local hook for a later
Mandaean or Manichaean baptismal cross-check if those source documents are
restored in `docs/ebooks`.

No `sorry`, no new `axiom`.
-/

structure WorldOvercomingFaith where
  christBeliefMarksNewBirth : Bool := true
  godLoveAndCommandKeepingJoined : Bool := true
  commandmentsNotGrievous : Bool := true
  bornOfGodOvercomesWorld : Bool := true
  faithNamesVictory : Bool := true
deriving DecidableEq, Repr

def worldOvercomingFaith : WorldOvercomingFaith := {}

def victoryByFaithLedger (w : WorldOvercomingFaith) : Prop :=
  w.christBeliefMarksNewBirth = true ∧
  w.godLoveAndCommandKeepingJoined = true ∧
  w.commandmentsNotGrievous = true ∧
  w.bornOfGodOvercomesWorld = true ∧
  w.faithNamesVictory = true

structure WaterBloodSpiritRecord where
  cameByWaterAndBlood : Bool := true
  notWaterOnlyButWaterAndBlood : Bool := true
  spiritBearsTruthWitness : Bool := true
  heavenlyRecordNamed : Bool := true
  earthlyWitnessesAgree : Bool := true
  godWitnessGreaterThanHumanWitness : Bool := true
deriving DecidableEq, Repr

def waterBloodSpiritRecord : WaterBloodSpiritRecord := {}

def convergingRecordWitness (r : WaterBloodSpiritRecord) : Prop :=
  r.cameByWaterAndBlood = true ∧
  r.notWaterOnlyButWaterAndBlood = true ∧
  r.spiritBearsTruthWitness = true ∧
  r.heavenlyRecordNamed = true ∧
  r.earthlyWitnessesAgree = true ∧
  r.godWitnessGreaterThanHumanWitness = true

structure LifePetitionIdolFirewall where
  sonHeldMeansLifeHeld : Bool := true
  writtenThatBelieversMayKnowLife : Bool := true
  willAlignedPetitionHeard : Bool := true
  brotherSinNotUntoDeathPrayedFor : Bool := true
  bornOfGodKeptFromWickedTouch : Bool := true
  understandingGivenToKnowTrueOne : Bool := true
  childrenGuardedFromIdols : Bool := true
deriving DecidableEq, Repr

def lifePetitionIdolFirewall : LifePetitionIdolFirewall := {}

def idolFirewallWitness (i : LifePetitionIdolFirewall) : Prop :=
  i.sonHeldMeansLifeHeld = true ∧
  i.writtenThatBelieversMayKnowLife = true ∧
  i.willAlignedPetitionHeard = true ∧
  i.brotherSinNotUntoDeathPrayedFor = true ∧
  i.bornOfGodKeptFromWickedTouch = true ∧
  i.understandingGivenToKnowTrueOne = true ∧
  i.childrenGuardedFromIdols = true

theorem first_john_victory_by_faith :
    victoryByFaithLedger worldOvercomingFaith := by
  unfold victoryByFaithLedger worldOvercomingFaith
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem first_john_converging_record_witness :
    convergingRecordWitness waterBloodSpiritRecord := by
  unfold convergingRecordWitness waterBloodSpiritRecord
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_john_idol_firewall :
    idolFirewallWitness lifePetitionIdolFirewall := by
  unfold idolFirewallWitness lifePetitionIdolFirewall
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_john_record_idol_witness :
    victoryByFaithLedger worldOvercomingFaith ∧
    convergingRecordWitness waterBloodSpiritRecord ∧
    idolFirewallWitness lifePetitionIdolFirewall := by
  exact ⟨first_john_victory_by_faith,
    first_john_converging_record_witness,
    first_john_idol_firewall⟩

end FirstJohnRecordIdolWitness
end Gnosis.Witnesses.Bible.FirstJohn
