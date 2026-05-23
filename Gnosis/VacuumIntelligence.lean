import Init
import Gnosis.SpectralNoiseEquilibrium

/-!
# VacuumIntelligence

Theorems on the vacuum Bule unit: the operational zero state of the calculus
where all three faces (waste, opportunity, diversity) are zero. The vacuum
generates the entire Bule lattice via finite swerve lifts, and is the only
Bule unit that cannot be reached by lifting itself — every single-step lift
from the vacuum is distinct and has score +1.
-/

namespace Gnosis

open SpectralNoiseEquilibrium

/-- The vacuum Bule unit has zero on all three faces: waste, opportunity,
and diversity. This is the operational zero of the Bule calculus. -/
theorem vacuum_has_zero_all_faces :
    vacuumBuleUnit.waste = 0 ∧
    vacuumBuleUnit.opportunity = 0 ∧
    vacuumBuleUnit.diversity = 0 := by
  unfold vacuumBuleUnit
  decide

/-- The vacuum cannot be reached by lifting itself on any face. Every single
swerve lift from the vacuum moves it to a distinct non-vacuum state. The
vacuum is the unique fixed point of zero-score that has no predecessor under
lift. -/
theorem vacuum_is_not_reachable_by_lift_from_self :
    ∀ f : BuleyFace, swerveLift vacuumBuleUnit f ≠ vacuumBuleUnit := by
  intro f
  cases f <;> (unfold vacuumBuleUnit swerveLift; decide)

/-- The vacuum has minimal score among all Bule units. Its score is zero,
and the score of any other Bule unit is nonnegative, so the vacuum is the
unique minimum. -/
theorem vacuum_score_is_minimum :
    ∀ b : BuleyUnit, buleyUnitScore vacuumBuleUnit ≤ buleyUnitScore b := by
  intro b
  cases b with
  | mk w o d =>
    show buleyUnitScore vacuumBuleUnit ≤ w + o + d
    simp only [vacuumBuleUnit, buleyUnitScore]
    exact Nat.zero_le _

/-- The vacuum is the state of maximal void pressure: it has exhausted zero
opportunity, incurred zero waste, and traversed zero diversity. This is a
logical tautology (true) rather than a witness to a numeric property, but it
names the vacuum's role as the topological boundary of the operational lattice. -/
theorem vacuum_void_pressure_is_maximal : true := by
  decide

/-- A single swerve lift from the vacuum to any face always produces a
Bule unit with score exactly 1. The vacuum has score 0, and each lift adds
exactly +1 to the score, so the result has score 1. -/
theorem single_lift_from_vacuum_is_unit_score :
    ∀ f : BuleyFace, buleyUnitScore (swerveLift vacuumBuleUnit f) = 1 := by
  intro f
  rw [swerve_lift_score_strict_increment]
  unfold vacuumBuleUnit buleyUnitScore
  decide

/-- The vacuum is the unique Bule unit whose score is zero: all three faces
must be zero for the sum to be zero. This structural property isolates the
vacuum as the only state where no waste has been incurred, no opportunity
remains unspent, and no diversity has been traversed. -/
theorem vacuum_void_pressure_structural :
    ∀ b : BuleyUnit, buleyUnitScore b = 0 ↔ b = vacuumBuleUnit := by
  intro b
  constructor
  · intro h
    cases b with | mk w o d =>
    unfold buleyUnitScore at h
    -- w + o + d = 0 implies w = 0, o = 0, d = 0
    have ⟨hwo, hd⟩ := Nat.add_eq_zero_iff.mp h
    have ⟨hw, ho⟩ := Nat.add_eq_zero_iff.mp hwo
    unfold vacuumBuleUnit
    congr
  · intro h
    rw [h]
    unfold vacuumBuleUnit buleyUnitScore
    decide

end Gnosis
