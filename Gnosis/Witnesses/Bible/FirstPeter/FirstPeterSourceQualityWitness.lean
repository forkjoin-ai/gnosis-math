import Gnosis.Witnesses.Bible.FirstPeter.FirstPeterLivingHopeWitness
import Gnosis.Witnesses.Bible.FirstPeter.FirstPeterLivingStonesWitness

namespace Gnosis.Witnesses.Bible.FirstPeter
namespace FirstPeterSourceQualityWitness

/-!
# 1 Peter -- Opening Source Quality Spine

Book-level invariant, opened in chapters 1-2: exile is not a deficit when identity
is kept by resurrection, incorruptible inheritance, and enduring word. Peter
begins with scattered strangers to show that location-loss can become witness
rather than collapse. The enduring word then builds the exiles into living
stones, priesthood, and honorable public conduct.

Primary gap/counterproof: the corruptible ledger cannot measure this people.
Gold perishes, grass withers, inherited vain conversation fails, and former lusts
cannot script holiness. Rejected stone, accused strangers, and wronged servants
also refuse the ledger that treats rejection as proof of worthlessness.

Unseen sat: hope is living because it is not wishful projection. It is anchored
in resurrection, searched by prophets, desired by angels, tested by fire, and
made social as fervent love from purified souls. The stone men disallow becomes
the house God builds; freedom becomes service rather than camouflage.

No `sorry`, no new `axiom`.
-/

structure FirstPeterOpeningInvariant where
  exileCanBeResurrectionKept : Bool := true
  inheritanceOutranksLocationLoss : Bool := true
  triedFaithOutranksPerishingGold : Bool := true
  enduringWordBegetsHolyLove : Bool := true
  rejectedStoneBuildsPriestlyHouse : Bool := true
  honorableExileSilencesAccusation : Bool := true
deriving DecidableEq, Repr

def firstPeterOpeningInvariant : FirstPeterOpeningInvariant := {}

def livingHopeInvariant (i : FirstPeterOpeningInvariant) : Prop :=
  i.exileCanBeResurrectionKept = true ∧
  i.inheritanceOutranksLocationLoss = true ∧
  i.triedFaithOutranksPerishingGold = true ∧
  i.enduringWordBegetsHolyLove = true ∧
  i.rejectedStoneBuildsPriestlyHouse = true ∧
  i.honorableExileSilencesAccusation = true

structure FirstPeterOpeningCounterproof where
  goldCannotMeasureTriedFaith : Bool := true
  formerLustsCannotDefineChildren : Bool := true
  silverGoldCannotRedeemTradition : Bool := true
  fleshGrassCannotOutlastWord : Bool := true
  humanRejectionCannotCancelPreciousStone : Bool := true
  libertyCannotCloakMalice : Bool := true
deriving DecidableEq, Repr

def firstPeterOpeningCounterproof : FirstPeterOpeningCounterproof := {}

def corruptibleLedgerRejected (c : FirstPeterOpeningCounterproof) : Prop :=
  c.goldCannotMeasureTriedFaith = true ∧
  c.formerLustsCannotDefineChildren = true ∧
  c.silverGoldCannotRedeemTradition = true ∧
  c.fleshGrassCannotOutlastWord = true ∧
  c.humanRejectionCannotCancelPreciousStone = true ∧
  c.libertyCannotCloakMalice = true

theorem first_peter_opening_quality_invariant :
    livingHopeInvariant firstPeterOpeningInvariant := by
  unfold livingHopeInvariant firstPeterOpeningInvariant
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_peter_opening_quality_counterproof :
    corruptibleLedgerRejected firstPeterOpeningCounterproof := by
  unfold corruptibleLedgerRejected firstPeterOpeningCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

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
      FirstPeterLivingStonesWitness.sufferingStepsCounterproof := by
  exact ⟨first_peter_opening_quality_invariant,
    first_peter_opening_quality_counterproof,
    FirstPeterLivingHopeWitness.first_peter_living_hope,
    FirstPeterLivingHopeWitness.first_peter_tried_faith,
    FirstPeterLivingHopeWitness.first_peter_corruptible_identity_rejected,
    FirstPeterLivingStonesWitness.first_peter_living_stone_house,
    FirstPeterLivingStonesWitness.first_peter_peculiar_people,
    FirstPeterLivingStonesWitness.first_peter_false_liberty_rejected⟩

end FirstPeterSourceQualityWitness
end Gnosis.Witnesses.Bible.FirstPeter
