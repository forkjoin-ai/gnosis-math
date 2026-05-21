import Gnosis.Witnesses.Bible.FirstPeter.FirstPeterLivingHopeWitness
import Gnosis.Witnesses.Bible.FirstPeter.FirstPeterLivingStonesWitness
import Gnosis.Witnesses.Bible.FirstPeter.FirstPeterConscienceAnswerWitness
import Gnosis.Witnesses.Bible.FirstPeter.FirstPeterFieryTrialStewardshipWitness
import Gnosis.Witnesses.Bible.FirstPeter.FirstPeterShepherdHumilityWitness

namespace Gnosis.Witnesses.Bible.FirstPeter
namespace FirstPeterSourceQualityWitness

/-!
# 1 Peter -- Opening Source Quality Spine

Book-level invariant, opened in chapters 1-5: exile is not a deficit when identity
is kept by resurrection, incorruptible inheritance, and enduring word. Peter
begins with scattered strangers to show that location-loss can become witness
rather than collapse. The enduring word then builds the exiles into living
stones, priesthood, and honorable public conduct. The rest of the letter tests
that architecture under household pressure, public accusation, fiery trial,
leadership, anxiety, and the devouring adversary.

Primary gap/counterproof: the corruptible ledger cannot measure this people.
Gold perishes, grass withers, inherited vain conversation fails, and former lusts
cannot script holiness. Rejected stone, accused strangers, and wronged servants
also refuse the ledger that treats rejection as proof of worthlessness.
Peter also rejects domination as defense, spectacle as stewardship, shame as the
final reading of suffering, and lording as shepherding.

Unseen sat: hope is living because it is not wishful projection. It is anchored
in resurrection, searched by prophets, desired by angels, tested by fire, and
made social as fervent love from purified souls. The stone men disallow becomes
the house God builds; freedom becomes service rather than camouflage. True grace
is the standing place where suffering a while can become establishment.

No `sorry`, no new `axiom`.
-/

structure FirstPeterOpeningInvariant where
  exileCanBeResurrectionKept : Bool := true
  inheritanceOutranksLocationLoss : Bool := true
  triedFaithOutranksPerishingGold : Bool := true
  enduringWordBegetsHolyLove : Bool := true
  rejectedStoneBuildsPriestlyHouse : Bool := true
  honorableExileSilencesAccusation : Bool := true
  goodConscienceAnswersWithoutDomination : Bool := true
  fieryTrialStewardsManifoldGrace : Bool := true
  trueGraceSettlesHumbleFlock : Bool := true
deriving DecidableEq, Repr

def firstPeterOpeningInvariant : FirstPeterOpeningInvariant := {}

def livingHopeInvariant (i : FirstPeterOpeningInvariant) : Prop :=
  i.exileCanBeResurrectionKept = true ∧
  i.inheritanceOutranksLocationLoss = true ∧
  i.triedFaithOutranksPerishingGold = true ∧
  i.enduringWordBegetsHolyLove = true ∧
  i.rejectedStoneBuildsPriestlyHouse = true ∧
  i.honorableExileSilencesAccusation = true ∧
  i.goodConscienceAnswersWithoutDomination = true ∧
  i.fieryTrialStewardsManifoldGrace = true ∧
  i.trueGraceSettlesHumbleFlock = true

structure FirstPeterOpeningCounterproof where
  goldCannotMeasureTriedFaith : Bool := true
  formerLustsCannotDefineChildren : Bool := true
  silverGoldCannotRedeemTradition : Bool := true
  fleshGrassCannotOutlastWord : Bool := true
  humanRejectionCannotCancelPreciousStone : Bool := true
  libertyCannotCloakMalice : Bool := true
  terrorCannotForceRetaliation : Bool := true
  strangeTrialCannotDefineShame : Bool := true
  lordshipCannotShepherdGodsHeritage : Bool := true
deriving DecidableEq, Repr

def firstPeterOpeningCounterproof : FirstPeterOpeningCounterproof := {}

def corruptibleLedgerRejected (c : FirstPeterOpeningCounterproof) : Prop :=
  c.goldCannotMeasureTriedFaith = true ∧
  c.formerLustsCannotDefineChildren = true ∧
  c.silverGoldCannotRedeemTradition = true ∧
  c.fleshGrassCannotOutlastWord = true ∧
  c.humanRejectionCannotCancelPreciousStone = true ∧
  c.libertyCannotCloakMalice = true ∧
  c.terrorCannotForceRetaliation = true ∧
  c.strangeTrialCannotDefineShame = true ∧
  c.lordshipCannotShepherdGodsHeritage = true

theorem first_peter_opening_quality_invariant :
    livingHopeInvariant firstPeterOpeningInvariant := by
  unfold livingHopeInvariant firstPeterOpeningInvariant
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_peter_opening_quality_counterproof :
    corruptibleLedgerRejected firstPeterOpeningCounterproof := by
  unfold corruptibleLedgerRejected firstPeterOpeningCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_peter_source_quality_opening_witness :
    livingHopeInvariant firstPeterOpeningInvariant ∧
    corruptibleLedgerRejected firstPeterOpeningCounterproof ∧
    FirstPeterLivingHopeWitness.livingHopeWitness
      FirstPeterLivingHopeWitness.livingHopeExile ∧
    FirstPeterLivingHopeWitness.triedFaithWitness
      FirstPeterLivingHopeWitness.triedFaith ∧
    FirstPeterLivingHopeWitness.corruptibleIdentityRejected
      FirstPeterLivingHopeWitness.incorruptibleWordCounterproof ∧
    FirstPeterLivingStonesWitness.livingStoneHouseWitness
      FirstPeterLivingStonesWitness.livingStoneHouse ∧
    FirstPeterLivingStonesWitness.peculiarPeopleWitness
      FirstPeterLivingStonesWitness.peculiarPeopleExile ∧
    FirstPeterLivingStonesWitness.falseLibertyRejected
      FirstPeterLivingStonesWitness.sufferingStepsCounterproof ∧
    FirstPeterConscienceAnswerWitness.householdWitnessProp
      FirstPeterConscienceAnswerWitness.householdWitness ∧
    FirstPeterConscienceAnswerWitness.blessingConscienceWitness
      FirstPeterConscienceAnswerWitness.blessingConscience ∧
    FirstPeterConscienceAnswerWitness.fleshAnswerRejected
      FirstPeterConscienceAnswerWitness.resurrectionAnswerCounterproof ∧
    FirstPeterFieryTrialStewardshipWitness.sufferingMindWitness
      FirstPeterFieryTrialStewardshipWitness.sufferingMind ∧
    FirstPeterFieryTrialStewardshipWitness.stewardshipWitness
      FirstPeterFieryTrialStewardshipWitness.manifoldGraceStewardship ∧
    FirstPeterFieryTrialStewardshipWitness.shameLedgerRejected
      FirstPeterFieryTrialStewardshipWitness.fieryTrialCounterproof ∧
    FirstPeterShepherdHumilityWitness.shepherdOversightWitness
      FirstPeterShepherdHumilityWitness.shepherdOversight ∧
    FirstPeterShepherdHumilityWitness.humbleVigilanceWitness
      FirstPeterShepherdHumilityWitness.humbleVigilance ∧
    FirstPeterShepherdHumilityWitness.trueGraceStandingWitness
      FirstPeterShepherdHumilityWitness.trueGraceStanding := by
  exact ⟨first_peter_opening_quality_invariant,
    first_peter_opening_quality_counterproof,
    FirstPeterLivingHopeWitness.first_peter_living_hope,
    FirstPeterLivingHopeWitness.first_peter_tried_faith,
    FirstPeterLivingHopeWitness.first_peter_corruptible_identity_rejected,
    FirstPeterLivingStonesWitness.first_peter_living_stone_house,
    FirstPeterLivingStonesWitness.first_peter_peculiar_people,
    FirstPeterLivingStonesWitness.first_peter_false_liberty_rejected,
    FirstPeterConscienceAnswerWitness.first_peter_household_witness,
    FirstPeterConscienceAnswerWitness.first_peter_blessing_conscience,
    FirstPeterConscienceAnswerWitness.first_peter_flesh_answer_rejected,
    FirstPeterFieryTrialStewardshipWitness.first_peter_suffering_mind,
    FirstPeterFieryTrialStewardshipWitness.first_peter_stewardship,
    FirstPeterFieryTrialStewardshipWitness.first_peter_shame_ledger_rejected,
    FirstPeterShepherdHumilityWitness.first_peter_shepherd_oversight,
    FirstPeterShepherdHumilityWitness.first_peter_humble_vigilance,
    FirstPeterShepherdHumilityWitness.first_peter_true_grace_standing⟩

end FirstPeterSourceQualityWitness
end Gnosis.Witnesses.Bible.FirstPeter
