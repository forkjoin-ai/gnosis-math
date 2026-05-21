import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansLeavenTroublerWitness

/-!
# Galatians 5:7-12 -- Hindered Running, Leaven, and Troubler Judgment

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93886-93900`.

This witness records disruption mechanics. The Galatians had been running well;
the alien persuasion is named as not from the caller, and its small leaven
propagates through the whole lump. The cross remains offensive precisely because
it refuses circumcision capture.

No `sorry`, no new `axiom`.
-/

structure HinderedRun where
  ranWellBefore : Bool := true
  hinderedTruthObedience : Bool := true
  persuasionNotFromCaller : Bool := true
  littleLeavenLeavensWholeLump : Bool := true
deriving DecidableEq, Repr

def hinderedRun : HinderedRun := {}

def leavenDisruptionWitness (h : HinderedRun) : Prop :=
  h.ranWellBefore = true ∧
  h.hinderedTruthObedience = true ∧
  h.persuasionNotFromCaller = true ∧
  h.littleLeavenLeavensWholeLump = true

structure TroublerJudgment where
  confidenceInLordForGalatians : Bool := true
  troublerBearsJudgment : Bool := true
  circumcisionPreachingWouldEndPersecution : Bool := true
  crossOffenceWouldCease : Bool := true
  troublersCutOffDesired : Bool := true
deriving DecidableEq, Repr

def troublerJudgment : TroublerJudgment := {}

def crossOffenceAgainstCapture (t : TroublerJudgment) : Prop :=
  t.confidenceInLordForGalatians = true ∧
  t.troublerBearsJudgment = true ∧
  t.circumcisionPreachingWouldEndPersecution = true ∧
  t.crossOffenceWouldCease = true ∧
  t.troublersCutOffDesired = true

theorem galatians_leaven_disruption :
    leavenDisruptionWitness hinderedRun := by
  unfold leavenDisruptionWitness hinderedRun
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem galatians_cross_offence_against_capture :
    crossOffenceAgainstCapture troublerJudgment := by
  unfold crossOffenceAgainstCapture troublerJudgment
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_leaven_troubler_witness :
    leavenDisruptionWitness hinderedRun ∧
    crossOffenceAgainstCapture troublerJudgment := by
  exact ⟨galatians_leaven_disruption,
    galatians_cross_offence_against_capture⟩

end GalatiansLeavenTroublerWitness
end Gnosis.Witnesses.Bible.Galatians
