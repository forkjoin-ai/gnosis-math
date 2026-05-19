import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Gnostic
namespace GospelTruthPathLackWitness

/-!
# Gospel of Truth -- Path as Returned Perfection

Source text: `docs/ebooks/source-texts/gospel-of-truth.txt`;
text anchor `docs/ebooks/source-texts/gospel-of-truth.txt:32-50`.

Sat/unseen reading:

The Father does not withhold perfection as scarcity. The lack of the All is the
missing knowledge of its own source, and the given path is the return-channel by
which retained perfection becomes receivable.

Gap / counterproof:

Error can persecute the fruit of knowledge, but eating that fruit produces joy,
not destruction. Jealousy is therefore the wrong model of the source.

No `sorry`, no new `axiom`.
-/

structure ReturnPath where
  hiddenMysteryRevealed : Bool
  darknessEnlightened : Bool
  pathIsTruth : Bool
  fruitIsKnowledge : Bool
  eatingFruitCausesJoy : Bool
deriving DecidableEq, Repr

def gospelReturnPath : ReturnPath where
  hiddenMysteryRevealed := true
  darknessEnlightened := true
  pathIsTruth := true
  fruitIsKnowledge := true
  eatingFruitCausesJoy := true

def pathTruthJoy (p : ReturnPath) : Prop :=
  p.hiddenMysteryRevealed = true ∧
  p.darknessEnlightened = true ∧
  p.pathIsTruth = true ∧
  p.fruitIsKnowledge = true ∧
  p.eatingFruitCausesJoy = true

structure LackDiagnosis where
  allInFather : Bool
  fatherNotJealous : Bool
  perfectionRetained : Bool
  givenAsReturnWay : Bool
  lackIsKnowledgeOfFather : Bool
deriving DecidableEq, Repr

def gospelLackDiagnosis : LackDiagnosis where
  allInFather := true
  fatherNotJealous := true
  perfectionRetained := true
  givenAsReturnWay := true
  lackIsKnowledgeOfFather := true

def lackIsNotScarcity (d : LackDiagnosis) : Prop :=
  d.allInFather = true ∧
  d.fatherNotJealous = true ∧
  d.perfectionRetained = true ∧
  d.givenAsReturnWay = true ∧
  d.lackIsKnowledgeOfFather = true

theorem gospel_path_truth_joy : pathTruthJoy gospelReturnPath := by
  unfold pathTruthJoy gospelReturnPath
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem gospel_lack_not_scarcity :
    lackIsNotScarcity gospelLackDiagnosis := by
  unfold lackIsNotScarcity gospelLackDiagnosis
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem path_recovery_shape :
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom :=
  Gnosis.GnosisTriptychBraid.two_step_recovery

theorem gospel_truth_path_lack_witness :
    pathTruthJoy gospelReturnPath ∧
    lackIsNotScarcity gospelLackDiagnosis ∧
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom := by
  exact ⟨gospel_path_truth_joy, gospel_lack_not_scarcity, path_recovery_shape⟩

end GospelTruthPathLackWitness
end Gnosis.Witnesses.Gnostic
