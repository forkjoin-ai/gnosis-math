import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Gnostic
namespace GospelTruthPleromaPhysicianWitness

/-!
# Gospel of Truth -- Pleroma Physician and Deficiency Filling

Source text: `docs/ebooks/source-texts/gospel-of-truth.txt`;
text anchor `docs/ebooks/source-texts/gospel-of-truth.txt:229-275`.

Sat/unseen reading:

Deficiency is not treated as guilt requiring concealment. The sick place is
where the physician hurries, because the physician has what the sick one lacks.
Pleroma gives itself out without becoming deficient.

Gap / counterproof:

Cold aroma comes from division. The answer is not more division, but the hot
Pleroma of love and the unity of Perfect Thought.

No `sorry`, no new `axiom`.
-/

structure AromaReturn where
  fatherKnowsWhatIsYours : Bool
  restInWhatIsYours : Bool
  aromaManifestsEverywhere : Bool
  spiritDrawsAromaToItself : Bool
  ascendsInEveryFormAndSound : Bool
  unityOfPerfectThoughtPrevails : Bool
deriving DecidableEq, Repr

def gospelAromaReturn : AromaReturn where
  fatherKnowsWhatIsYours := true
  restInWhatIsYours := true
  aromaManifestsEverywhere := true
  spiritDrawsAromaToItself := true
  ascendsInEveryFormAndSound := true
  unityOfPerfectThoughtPrevails := true

def aromaReturnsToRest (a : AromaReturn) : Prop :=
  a.fatherKnowsWhatIsYours = true ∧
  a.restInWhatIsYours = true ∧
  a.aromaManifestsEverywhere = true ∧
  a.spiritDrawsAromaToItself = true ∧
  a.ascendsInEveryFormAndSound = true ∧
  a.unityOfPerfectThoughtPrevails = true

structure PhysicianPleroma where
  physicianHurriesToSickness : Bool
  sickDoesNotHide : Bool
  physicianHasWhatIsLacked : Bool
  pleromaHasNoDeficiency : Bool
  pleromaGivesItselfOut : Bool
  graceTakesFromDeficientArea : Bool
deriving DecidableEq, Repr

def gospelPhysicianPleroma : PhysicianPleroma where
  physicianHurriesToSickness := true
  sickDoesNotHide := true
  physicianHasWhatIsLacked := true
  pleromaHasNoDeficiency := true
  pleromaGivesItselfOut := true
  graceTakesFromDeficientArea := true

def pleromaFillsWithoutLoss (p : PhysicianPleroma) : Prop :=
  p.physicianHurriesToSickness = true ∧
  p.sickDoesNotHide = true ∧
  p.physicianHasWhatIsLacked = true ∧
  p.pleromaHasNoDeficiency = true ∧
  p.pleromaGivesItselfOut = true ∧
  p.graceTakesFromDeficientArea = true

structure OintmentRest where
  troubledReceiveReturn : Bool
  pityAnoints : Bool
  deficientFilledAgain : Bool
  fatherKnowsPlantings : Bool
  paradiseIsRest : Bool
deriving DecidableEq, Repr

def gospelOintmentRest : OintmentRest where
  troubledReceiveReturn := true
  pityAnoints := true
  deficientFilledAgain := true
  fatherKnowsPlantings := true
  paradiseIsRest := true

def anointingReturnsToRest (o : OintmentRest) : Prop :=
  o.troubledReceiveReturn = true ∧
  o.pityAnoints = true ∧
  o.deficientFilledAgain = true ∧
  o.fatherKnowsPlantings = true ∧
  o.paradiseIsRest = true

theorem gospel_aroma_return :
    aromaReturnsToRest gospelAromaReturn := by
  unfold aromaReturnsToRest gospelAromaReturn
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gospel_physician_pleroma :
    pleromaFillsWithoutLoss gospelPhysicianPleroma := by
  unfold pleromaFillsWithoutLoss gospelPhysicianPleroma
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gospel_ointment_rest :
    anointingReturnsToRest gospelOintmentRest := by
  unfold anointingReturnsToRest gospelOintmentRest
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem physician_recovery_shape :
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom :=
  Gnosis.GnosisTriptychBraid.two_step_recovery

theorem gospel_truth_pleroma_physician_witness :
    aromaReturnsToRest gospelAromaReturn ∧
    pleromaFillsWithoutLoss gospelPhysicianPleroma ∧
    anointingReturnsToRest gospelOintmentRest ∧
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom := by
  exact ⟨gospel_aroma_return,
    gospel_physician_pleroma,
    gospel_ointment_rest,
    physician_recovery_shape⟩

end GospelTruthPleromaPhysicianWitness
end Gnosis.Witnesses.Gnostic
