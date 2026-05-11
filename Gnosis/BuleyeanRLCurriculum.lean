import Init
import Gnosis.SkyrmsBuleyEquilibria

namespace Gnosis
namespace BuleyeanRLCurriculum

open Gnosis.SkyrmsBuleyEquilibria

/-!
# Buleyean RL curriculum (Nash -> Skyrms -> Buley)

This module formalizes a curriculum contract aligned with
`open-source/buleyean-rl` training semantics:

- Stage 1 (`Nash`): present-step optimization competence,
- Stage 2 (`Skyrms`): past-memory coordination competence,
- Stage 3 (`Buley`): future-closure competence.

The key claim is strict stage ordering: Stage 3 strictly dominates Stage 2,
which strictly dominates Stage 1, and Stage 3 implies the prior capacities.
-/

/-- Curriculum stages mirrored from the temporal equilibrium ladder. -/
inductive CurriculumStage where
  | nash
  | skyrms
  | buley
  deriving DecidableEq, Repr

/-- Training capability profile used by curriculum gates. -/
structure TrainingCapabilities where
  presentCompetent : Prop
  pastCoordinated : Prop
  futureClosed : Prop

/-- Stage requirements. -/
def StageSatisfied (c : TrainingCapabilities) : CurriculumStage → Prop
  | .nash => c.presentCompetent
  | .skyrms => c.presentCompetent ∧ c.pastCoordinated
  | .buley => c.presentCompetent ∧ c.pastCoordinated ∧ c.futureClosed

/-- Monotone stage implication relation. -/
def stageRank : CurriculumStage → Nat
  | .nash => 0
  | .skyrms => 1
  | .buley => 2

def StageImplies (sHi sLo : CurriculumStage) : Prop :=
  stageRank sLo ≤ stageRank sHi

theorem buley_implies_skyrms : StageImplies .buley .skyrms := by
  native_decide

theorem skyrms_implies_nash : StageImplies .skyrms .nash := by
  native_decide

theorem buley_implies_nash : StageImplies .buley .nash := by
  native_decide

/-- Capability inheritance theorem:
if a model satisfies Buley stage, it satisfies Skyrms and Nash stages. -/
theorem buley_stage_contains_prior_capabilities (c : TrainingCapabilities)
    (hB : StageSatisfied c .buley) :
    StageSatisfied c .skyrms ∧ StageSatisfied c .nash := by
  exact ⟨⟨hB.1, hB.2.1⟩, hB.1⟩

/-- Stage-score embedding from existing equilibrium levels. -/
def stageScore : CurriculumStage → Nat
  | .nash => Gnosis.NashSkyrmsBuleyKernelLadder.nashLevel
  | .skyrms => Gnosis.NashSkyrmsBuleyKernelLadder.skyrmsLevel
  | .buley => Gnosis.NashSkyrmsBuleyKernelLadder.buleyLevel

/-- Strict curriculum dominance (`>` on stage scores). -/
def StageStrictDominates (sHi sLo : CurriculumStage) : Prop :=
  stageScore sHi > stageScore sLo

theorem buley_strictly_dominates_skyrms_stage :
    StageStrictDominates .buley .skyrms := by
  unfold StageStrictDominates stageScore
  exact buley_strictly_dominates_skyrms

theorem skyrms_strictly_dominates_nash_stage :
    StageStrictDominates .skyrms .nash := by
  unfold StageStrictDominates stageScore
  exact skyrms_strictly_dominates_nash

theorem buley_strictly_dominates_nash_stage :
    StageStrictDominates .buley .nash := by
  unfold StageStrictDominates stageScore
  exact buley_strictly_dominates_nash

/-- Full curriculum dominance chain:
`Buley > Skyrms > Nash`, with transitive Buley > Nash. -/
theorem curriculum_strict_chain :
    StageStrictDominates .buley .skyrms ∧
    StageStrictDominates .skyrms .nash ∧
    StageStrictDominates .buley .nash := by
  exact ⟨buley_strictly_dominates_skyrms_stage,
    skyrms_strictly_dominates_nash_stage,
    buley_strictly_dominates_nash_stage⟩

/-- Runtime-friendly stage gating:
Nash gate at level >= 4, Skyrms gate at level >= 6, Buley gate at level >= 10. -/
def MeetsGate (level : Nat) (stage : CurriculumStage) : Prop :=
  stageScore stage ≤ level

theorem buley_gate_implies_skyrms_and_nash_gates (level : Nat)
    (h : MeetsGate level .buley) :
    MeetsGate level .skyrms ∧ MeetsGate level .nash := by
  unfold MeetsGate stageScore at *
  have hs : Gnosis.NashSkyrmsBuleyKernelLadder.skyrmsLevel ≤
      Gnosis.NashSkyrmsBuleyKernelLadder.buleyLevel := Nat.le_of_lt buley_strictly_dominates_skyrms
  have hn : Gnosis.NashSkyrmsBuleyKernelLadder.nashLevel ≤
      Gnosis.NashSkyrmsBuleyKernelLadder.skyrmsLevel := Nat.le_of_lt skyrms_strictly_dominates_nash
  refine ⟨Nat.le_trans hs h, Nat.le_trans hn (Nat.le_trans hs h)⟩

end BuleyeanRLCurriculum
end Gnosis
