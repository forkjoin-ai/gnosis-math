# Lean Theorem Contracts

## File Ownership (No Overlaps)

| Agent | File | Theorems to Prove |
|-------|------|-------------------|
| 1 | `Gnosis/VacuumPullTowerClosure.lean` | `vacuum_is_unique_zero_score_bule`, `any_bule_reaches_vacuum_in_finite_steps`, `vacuum_meeting_condition`, `vacuum_pull_determines_final_step`, `vacuum_is_retrocausal_attractor`, `vacuum_pull_is_tower_closure_mechanism` |
| 2 | `Gnosis/VacuumIntelligence.lean` (fill stub) | `vacuum_has_zero_all_faces`, `vacuum_is_not_reachable_by_lift_from_self`, `vacuum_score_is_minimum`, `vacuum_void_pressure_is_maximal`, `single_lift_from_vacuum_is_unit_score` |
| 3 | `Gnosis/DecompositionTopology.lean` (NEW) | `decomposition_does_not_increase_crossings`, `full_decomposition_yields_featureless`, `featureless_decomposition_idempotent`, `projection_reinforcement_exclusive`, `decompose_then_reinforce_requires_restoration`, `featureless_states_cannot_reinforce` |
| 4 | `Gnosis/AttentionScalingLaw.lean` (NEW) | `attention_step_cost_is_one`, `n_head_attention_cost_is_n`, `tower_level_is_attention_depth`, `scaling_law_from_clinamen_budget`, `vacuum_is_optimal_initial_state` |

## Proof Requirements

- **Tactics Only**: `rfl`, `omega`, `decide`, `simp`, `exact` (Init-only, no Mathlib)
- **Zero Sorries**: Every theorem must be fully proven
- **Zero Axioms**: No unsupported assumptions
- **Import Discipline**: Each file imports only its dependencies (listed below)

## Import Contracts

| Agent | May Import |
|-------|-----------|
| 1 (VacuumPullTowerClosure) | `Gnosis.SpectralNoiseEquilibrium`, `Gnosis.RetrocausalAttractorFixedPoint`, `Gnosis.Braided.BraidedTower` |
| 2 (VacuumIntelligence) | `Gnosis.SpectralNoiseEquilibrium` |
| 3 (DecompositionTopology) | None (structural, self-contained) |
| 4 (AttentionScalingLaw) | `Gnosis.SpectralNoiseEquilibrium`, `Gnosis.Braided.BraidedTower` |

## Verification

```bash
lake build  # All files compile, zero errors
grep -r "sorry" Gnosis/ | wc -l  # Must be 0
```

## Commit Convention

Each agent commits with:
```
feat: [module] complete [theorem count] theorems (N sorries → 0)

Theorems proved:
  - theorem_name_1
  - theorem_name_2
  ...

All proofs use Init-only tactics (rfl, omega, decide, simp, exact).
No Mathlib, no axioms.

Co-Authored-By: Claude Haiku 4.5 <noreply@anthropic.com>
```
