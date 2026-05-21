namespace Gnosis.Witnesses.Bible.FirstPeter
namespace FirstPeterLivingStonesWitness

/-!
# 1 Peter 2 -- Living Stones, Honorable Exile, and Suffering Steps

Source slice: 1 Peter 2:1-25.

Chapter invariant: the rejected stone becomes architecture. Coming to the living
stone builds living stones into a spiritual house and holy priesthood; what men
disallow, God makes precious and structural.

Primary gap/counterproof: freedom is not a cloak for malice, and exile conduct
is not respectability theater. Good works silence foolish ignorance because they
expose accusation as oxygen-starved.

Unseen sat: unjust suffering can become patterned witness without becoming
passive falsehood. Christ does not return reviling for reviling; he commits
himself to righteous judgment, bears sins in his body, and returns straying sheep
to the Shepherd and Bishop of souls.

No `sorry`, no new `axiom`.
-/

structure LivingStoneHouse where
  maliceAndGuileLaidAside : Bool := true
  sincereWordMilkGrows : Bool := true
  livingStoneRejectedYetChosen : Bool := true
  livelyStonesBecomeSpiritualHouse : Bool := true
  holyPriesthoodOffersSpiritualSacrifices : Bool := true
  stumblingStoneExposesDisobedience : Bool := true
deriving DecidableEq, Repr

def livingStoneHouse : LivingStoneHouse := {}

def livingStoneHouseWitness (h : LivingStoneHouse) : Prop :=
  h.maliceAndGuileLaidAside = true ∧
  h.sincereWordMilkGrows = true ∧
  h.livingStoneRejectedYetChosen = true ∧
  h.livelyStonesBecomeSpiritualHouse = true ∧
  h.holyPriesthoodOffersSpiritualSacrifices = true ∧
  h.stumblingStoneExposesDisobedience = true

structure PeculiarPeopleExile where
  chosenGenerationShowsPraises : Bool := true
  notPeopleBecomeGodsPeople : Bool := true
  noMercyBecomeMercyReceived : Bool := true
  strangersAbstainFromSoulWarLusts : Bool := true
  honestConductTurnsAccusationTowardGlory : Bool := true
deriving DecidableEq, Repr

def peculiarPeopleExile : PeculiarPeopleExile := {}

def peculiarPeopleWitness (p : PeculiarPeopleExile) : Prop :=
  p.chosenGenerationShowsPraises = true ∧
  p.notPeopleBecomeGodsPeople = true ∧
  p.noMercyBecomeMercyReceived = true ∧
  p.strangersAbstainFromSoulWarLusts = true ∧
  p.honestConductTurnsAccusationTowardGlory = true

structure SufferingStepsCounterproof where
  submissionForLordSakeSilencesIgnorance : Bool := true
  libertyCannotCloakMalice : Bool := true
  wrongfulSufferingCanBeThankworthy : Bool := true
  faultSufferingHasNoGlory : Bool := true
  christLeavesStepsInNonRetaliation : Bool := true
  bodyTreeBearingMakesRighteousLife : Bool := true
  strayingSheepReturnToShepherd : Bool := true
deriving DecidableEq, Repr

def sufferingStepsCounterproof : SufferingStepsCounterproof := {}

def falseLibertyRejected (c : SufferingStepsCounterproof) : Prop :=
  c.submissionForLordSakeSilencesIgnorance = true ∧
  c.libertyCannotCloakMalice = true ∧
  c.wrongfulSufferingCanBeThankworthy = true ∧
  c.faultSufferingHasNoGlory = true ∧
  c.christLeavesStepsInNonRetaliation = true ∧
  c.bodyTreeBearingMakesRighteousLife = true ∧
  c.strayingSheepReturnToShepherd = true

theorem first_peter_living_stone_house :
    livingStoneHouseWitness livingStoneHouse := by
  unfold livingStoneHouseWitness livingStoneHouse
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_peter_peculiar_people :
    peculiarPeopleWitness peculiarPeopleExile := by
  unfold peculiarPeopleWitness peculiarPeopleExile
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem first_peter_false_liberty_rejected :
    falseLibertyRejected sufferingStepsCounterproof := by
  unfold falseLibertyRejected sufferingStepsCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_peter_living_stones_witness :
    livingStoneHouseWitness livingStoneHouse ∧
    peculiarPeopleWitness peculiarPeopleExile ∧
    falseLibertyRejected sufferingStepsCounterproof := by
  exact ⟨first_peter_living_stone_house,
    first_peter_peculiar_people,
    first_peter_false_liberty_rejected⟩

end FirstPeterLivingStonesWitness
end Gnosis.Witnesses.Bible.FirstPeter
