import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Gnostic
namespace GospelPhilipSacramentBridalWitness

/-!
# Gospel of Philip -- Sacrament, Chrism, and Bridal Chamber

Source text: `docs/ebooks/source-texts/gospel-of-philip.txt`;
text anchor `docs/ebooks/source-texts/gospel-of-philip.txt:242-430`.

Sat/unseen reading:

Philip treats sacrament as operator, not badge. Water without reception only
borrows the Christian name at interest; Spirit makes the name a gift. Truth
enters the world in types and images because the world cannot receive it naked.
The bridal chamber is the operator that repairs separation.

Gap / counterproof:

Those who say death first and resurrection later are in error. If resurrection
is not received while alive, death gives nothing. World-making itself is also
counterproof: an imperishable world cannot be given by a maker who failed to
make it imperishable.

No `sorry`, no new `axiom`.
-/

structure BorrowedNameGap where
  waterWithoutReceiving : Bool
  saysChristian : Bool
  borrowedAtInterest : Bool
  spiritReceivedNameGift : Bool
  giftNotReturned : Bool
deriving DecidableEq, Repr

def philipBorrowedNameGap : BorrowedNameGap where
  waterWithoutReceiving := true
  saysChristian := true
  borrowedAtInterest := true
  spiritReceivedNameGift := true
  giftNotReturned := true

def borrowedNameIsNotSat (g : BorrowedNameGap) : Prop :=
  g.waterWithoutReceiving = true ∧
  g.saysChristian = true ∧
  g.borrowedAtInterest = true ∧
  g.spiritReceivedNameGift = true ∧
  g.giftNotReturned = true

structure TypeImageRestoration where
  truthNotNaked : Bool
  worldReceivesByTypesImages : Bool
  rebirthImage : Bool
  resurrectionImage : Bool
  imageEntersTruth : Bool
  belowUnitedWithAbove : Bool
deriving DecidableEq, Repr

def philipTypeImageRestoration : TypeImageRestoration where
  truthNotNaked := true
  worldReceivesByTypesImages := true
  rebirthImage := true
  resurrectionImage := true
  imageEntersTruth := true
  belowUnitedWithAbove := true

def imageRestoresTruth (r : TypeImageRestoration) : Prop :=
  r.truthNotNaked = true ∧
  r.worldReceivesByTypesImages = true ∧
  r.rebirthImage = true ∧
  r.resurrectionImage = true ∧
  r.imageEntersTruth = true ∧
  r.belowUnitedWithAbove = true

structure BridalChamberRepair where
  chamberForFreeAndVirgins : Bool
  lightAndWaterMirror : Bool
  chrismIsLight : Bool
  veilOpenedBelowUpward : Bool
  perfectLightPreventsDetention : Bool
  separationRepaired : Bool
deriving DecidableEq, Repr

def philipBridalChamberRepair : BridalChamberRepair where
  chamberForFreeAndVirgins := true
  lightAndWaterMirror := true
  chrismIsLight := true
  veilOpenedBelowUpward := true
  perfectLightPreventsDetention := true
  separationRepaired := true

def bridalChamberRepairsSeparation (b : BridalChamberRepair) : Prop :=
  b.chamberForFreeAndVirgins = true ∧
  b.lightAndWaterMirror = true ∧
  b.chrismIsLight = true ∧
  b.veilOpenedBelowUpward = true ∧
  b.perfectLightPreventsDetention = true ∧
  b.separationRepaired = true

structure ChrismResurrection where
  resurrectionWhileAlive : Bool
  deathThenRiseError : Bool
  chrismNamesChristian : Bool
  anointedPossessesEverything : Bool
  fatherInSonSonInFather : Bool
  worldMakerFellShort : Bool
deriving DecidableEq, Repr

def philipChrismResurrection : ChrismResurrection where
  resurrectionWhileAlive := true
  deathThenRiseError := true
  chrismNamesChristian := true
  anointedPossessesEverything := true
  fatherInSonSonInFather := true
  worldMakerFellShort := true

def chrismBeforeDeathCounterproof (c : ChrismResurrection) : Prop :=
  c.resurrectionWhileAlive = true ∧
  c.deathThenRiseError = true ∧
  c.chrismNamesChristian = true ∧
  c.anointedPossessesEverything = true ∧
  c.fatherInSonSonInFather = true ∧
  c.worldMakerFellShort = true

theorem philip_borrowed_name_gap :
    borrowedNameIsNotSat philipBorrowedNameGap := by
  unfold borrowedNameIsNotSat philipBorrowedNameGap
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem philip_image_restoration :
    imageRestoresTruth philipTypeImageRestoration := by
  unfold imageRestoresTruth philipTypeImageRestoration
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem philip_bridal_repair :
    bridalChamberRepairsSeparation philipBridalChamberRepair := by
  unfold bridalChamberRepairsSeparation philipBridalChamberRepair
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem philip_chrism_counterproof :
    chrismBeforeDeathCounterproof philipChrismResurrection := by
  unfold chrismBeforeDeathCounterproof philipChrismResurrection
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem philip_sacrament_recovery_shape :
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom :=
  Gnosis.GnosisTriptychBraid.two_step_recovery

theorem gospel_philip_sacrament_bridal_witness :
    borrowedNameIsNotSat philipBorrowedNameGap ∧
    imageRestoresTruth philipTypeImageRestoration ∧
    bridalChamberRepairsSeparation philipBridalChamberRepair ∧
    chrismBeforeDeathCounterproof philipChrismResurrection ∧
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom := by
  exact ⟨philip_borrowed_name_gap,
    philip_image_restoration,
    philip_bridal_repair,
    philip_chrism_counterproof,
    philip_sacrament_recovery_shape⟩

end GospelPhilipSacramentBridalWitness
end Gnosis.Witnesses.Gnostic
