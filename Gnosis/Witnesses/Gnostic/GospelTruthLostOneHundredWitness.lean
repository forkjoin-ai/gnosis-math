import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Gnostic
namespace GospelTruthLostOneHundredWitness

/-!
# Gospel of Truth -- Lost One and Hundred Completion

Source text: `docs/ebooks/source-texts/gospel-of-truth.txt`;
text anchor `docs/ebooks/source-texts/gospel-of-truth.txt:203-228`.

Sat/unseen reading:

The lost sheep is not a sentimental aside. It is arithmetic completion: the
ninety-nine remain a left-hand incompletion until the missing one is recovered,
at which point the whole number transfers rightward into one hundred.

Gap / counterproof:

Salvation must not be idle, even on the Sabbath. Any law-reading that prevents
the deficient one from being lifted out of the pit is exposed as anti-Sat.

No `sorry`, no new `axiom`.
-/

structure LostOneArithmetic where
  ninetyNineLeft : Nat
  missingOne : Nat
  completedHundred : Nat
  leftHandIncomplete : Bool
  rightHandCompletion : Bool
deriving DecidableEq, Repr

def gospelLostOneArithmetic : LostOneArithmetic where
  ninetyNineLeft := 99
  missingOne := 1
  completedHundred := 100
  leftHandIncomplete := true
  rightHandCompletion := true

def oneCompletesHundred (a : LostOneArithmetic) : Prop :=
  a.ninetyNineLeft + a.missingOne = a.completedHundred ∧
  a.leftHandIncomplete = true ∧
  a.rightHandCompletion = true

structure SabbathRescue where
  sheepInPit : Bool
  laborsOnSabbath : Bool
  savedLife : Bool
  salvationNotIdle : Bool
  perfectDayNoNight : Bool
  unfailingLightWithin : Bool
deriving DecidableEq, Repr

def gospelSabbathRescue : SabbathRescue where
  sheepInPit := true
  laborsOnSabbath := true
  savedLife := true
  salvationNotIdle := true
  perfectDayNoNight := true
  unfailingLightWithin := true

def sabbathDoesNotBlockRescue (r : SabbathRescue) : Prop :=
  r.sheepInPit = true ∧
  r.laborsOnSabbath = true ∧
  r.savedLife = true ∧
  r.salvationNotIdle = true ∧
  r.perfectDayNoNight = true ∧
  r.unfailingLightWithin = true

structure HandsOfRecovery where
  speakTruthToSeekers : Bool
  steadyStumblers : Bool
  stretchHandsToSick : Bool
  nourishHungry : Bool
  awakenSleepers : Bool
  doNotReturnToCastOffThings : Bool
deriving DecidableEq, Repr

def gospelHandsOfRecovery : HandsOfRecovery where
  speakTruthToSeekers := true
  steadyStumblers := true
  stretchHandsToSick := true
  nourishHungry := true
  awakenSleepers := true
  doNotReturnToCastOffThings := true

def recoveryDoesNotReinfect (h : HandsOfRecovery) : Prop :=
  h.speakTruthToSeekers = true ∧
  h.steadyStumblers = true ∧
  h.stretchHandsToSick = true ∧
  h.nourishHungry = true ∧
  h.awakenSleepers = true ∧
  h.doNotReturnToCastOffThings = true

theorem gospel_one_completes_hundred :
    oneCompletesHundred gospelLostOneArithmetic := by
  unfold oneCompletesHundred gospelLostOneArithmetic
  exact ⟨rfl, rfl, rfl⟩

theorem gospel_sabbath_rescue :
    sabbathDoesNotBlockRescue gospelSabbathRescue := by
  unfold sabbathDoesNotBlockRescue gospelSabbathRescue
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gospel_recovery_hands :
    recoveryDoesNotReinfect gospelHandsOfRecovery := by
  unfold recoveryDoesNotReinfect gospelHandsOfRecovery
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem missing_one_is_clinamen :
    gospelLostOneArithmetic.missingOne = 1 :=
  rfl

theorem gospel_truth_lost_one_hundred_witness :
    oneCompletesHundred gospelLostOneArithmetic ∧
    sabbathDoesNotBlockRescue gospelSabbathRescue ∧
    recoveryDoesNotReinfect gospelHandsOfRecovery ∧
    gospelLostOneArithmetic.missingOne = 1 := by
  exact ⟨gospel_one_completes_hundred,
    gospel_sabbath_rescue,
    gospel_recovery_hands,
    missing_one_is_clinamen⟩

end GospelTruthLostOneHundredWitness
end Gnosis.Witnesses.Gnostic
