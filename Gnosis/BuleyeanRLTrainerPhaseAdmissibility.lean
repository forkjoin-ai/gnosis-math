import Init
import Gnosis.BuleyeanRLCurriculum

namespace Gnosis
namespace BuleyeanRLTrainerPhaseAdmissibility

open Gnosis.BuleyeanRLCurriculum

/-!
# Trainer parity phases × curriculum stages (Python bridge)

Each string is the resolver output of `ConvergenceParityDetector.record_step` in

`open-source/buleyean-rl/python/buleyean_rl/convergence_parity.py`,
surfaced by `trainer._latest_parity_phase` / logs `parity_phase` in `trainer.py`.

`TrainerPhaseAdmissible` formalizes **which parity phases may be asserted as compatible**
with a given **Lean curriculum certification** (`CurriculumStage` / `StageSatisfied`):

- **`growing`** / **`parity`**: unconstrained warmup / deficit–curvature coupling — always admissible.
- **`collapsing`**: post-parity descent toward fixation — ruled out while only **present-only**
  competence is asserted (`nash`): collapse presumes richer coordination bookkeeping.
- **`converged`**: KL floor is below the detector threshold — modeled as requiring **full temporal
  closure** certification (`buley` stage), aligned with equilibrium completion not just local fit.
- **`reward_hacking`**: **never admissible** — always contradicts certified training semantics
  mirroring trainer's stop warning.

These are ontology links from runtime metrics to staged contracts, not a guarantee that Python emits
admissible phases in order.
-/

/-- Parity-phase labels mirrored from Python — keep constructor names ASCII for tooling. -/
inductive TrainerParityPhase where
  | growing
  | parity
  | collapsing
  | converged
  | reward_hacking
  deriving DecidableEq, Repr

/--
Admissibility: curriculum stage × trainer-reported parity phase.

`False` certificates are modeled as contradictory with honest staging (not as untyped crashes).
-/
def TrainerPhaseAdmissible (stage : CurriculumStage) (φ : TrainerParityPhase) : Prop :=
  match φ with
  | .reward_hacking => False
  | .growing => True
  | .parity => True
  | .collapsing =>
      match stage with
      | .nash => False
      | .skyrms | .buley => True
  | .converged =>
      match stage with
      | .buley => True
      | .nash | .skyrms => False

theorem reward_hacking_never_admissible (stage : CurriculumStage) :
    ¬ TrainerPhaseAdmissible stage .reward_hacking := by
  intro h
  unfold TrainerPhaseAdmissible at h
  contradiction

theorem growing_always_admissible (stage : CurriculumStage) :
    TrainerPhaseAdmissible stage .growing := trivial

theorem parity_always_admissible (stage : CurriculumStage) :
    TrainerPhaseAdmissible stage .parity := trivial

theorem collapsing_admissible_iff_not_nash_only (stage : CurriculumStage) :
    TrainerPhaseAdmissible stage .collapsing ↔ stage ≠ CurriculumStage.nash := by
  cases stage <;> simp [TrainerPhaseAdmissible, Ne]

theorem converged_admissible_iff_buley (stage : CurriculumStage) :
    TrainerPhaseAdmissible stage .converged ↔ stage = CurriculumStage.buley := by
  cases stage <;> simp [TrainerPhaseAdmissible]

/-- Stronger curricula never lose admissible phases (`StageImplies hi lo` reads “hi dominates lo”). -/
theorem admissible_monotone (hi lo : CurriculumStage) (φ : TrainerParityPhase)
    (hord : StageImplies hi lo) (had : TrainerPhaseAdmissible lo φ) :
    TrainerPhaseAdmissible hi φ := by
  cases φ <;> cases hi <;> cases lo <;> simp_all [TrainerPhaseAdmissible, StageImplies]

/--
If capabilities satisfy Nash stage (`presentCompetent` only),
the parity pipeline must not certify **KL-floor convergence** —
only warmup / curvature-coupled phases (`growing`,`parity`).
-/
theorem nash_stage_excludes_terminal_convergence (_c : TrainingCapabilities)
    (_hN : StageSatisfied _c CurriculumStage.nash) (φ : TrainerParityPhase)
    (had : TrainerPhaseAdmissible CurriculumStage.nash φ) :
    φ = TrainerParityPhase.growing ∨ φ = TrainerParityPhase.parity := by
  cases φ
  · exact Or.inl rfl
  · exact Or.inr rfl
  · contradiction
  · contradiction
  · contradiction

theorem skyrms_stage_excludes_terminal_convergence (_c : TrainingCapabilities)
    (_hS : StageSatisfied _c CurriculumStage.skyrms) (φ : TrainerParityPhase)
    (had : TrainerPhaseAdmissible CurriculumStage.skyrms φ) :
    φ ≠ TrainerParityPhase.converged := by
  intro h
  rw [h] at had
  simp [TrainerPhaseAdmissible] at had

end BuleyeanRLTrainerPhaseAdmissibility
end Gnosis
