import Gnosis.SpectralNoiseEquilibrium
import Gnosis.Dark.DarkDeceptaconLoss

/-!
# Buley ↔ Dark Deceptacon Bridge

Connects the Bule unit calculus to the existing
`DarkDeceptaconLoss` formalization (`RecognizesVoid`, `VoidPenalty`,
`perfect_void_recognition_is_zero_loss`, `omniscience_triggers_overflow`).

The translations:

* The vacuum Bule unit's score is zero ⟹ the vacuum recognizes the void
  (`RecognizesVoid` holds on the vacuum's score).
* The Bule score *is* the `VoidPenalty` (the penalty is structural mass,
  same as the Bule unit's count of swerve lifts away from the vacuum).
* A single +1 swerve lift on the vacuum produces `VoidPenalty 1` —
  the unit clinamen residue from `UniversalClinamenPlusOne` is exactly
  one quantum of structural penalty.
* The `omniscience_triggers_overflow` theorem from `DarkDeceptaconLoss`
  applies directly to any Bule unit whose score exceeds a memory
  bound — the catastrophic-attention failure mode in
  `DarkDeceptaconTransformer` is the same thing as a Bule unit lifted
  past the available phase manifold.

Imports `Gnosis.SpectralNoiseEquilibrium` and `Gnosis.DarkDeceptaconLoss`.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace BuleyDarkDeceptaconBridge

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit BuleyFace buleyUnitScore vacuumBuleUnit swerveLift
   vacuum_has_zero_score swerve_lift_score_strict_increment)

/-- The vacuum Bule unit recognizes the void: its score is zero, so
`DarkDeceptaconLoss.RecognizesVoid` holds on it. The vacuum is the
formally-verified "perfect void recognition" state of the calculus. -/
theorem vacuum_bule_recognizes_void :
    RecognizesVoid (buleyUnitScore vacuumBuleUnit) := by
  unfold RecognizesVoid
  exact vacuum_has_zero_score

/-- The vacuum has zero `VoidPenalty`. Direct corollary of
`perfect_void_recognition_is_zero_loss` applied to the Bule vacuum. -/
theorem vacuum_bule_has_zero_void_penalty :
    VoidPenalty (buleyUnitScore vacuumBuleUnit) = 0 :=
  perfect_void_recognition_is_zero_loss vacuum_bule_recognizes_void

/-- The Bule score IS the `VoidPenalty` of the same number. The Bule
unit's count of swerve lifts away from the vacuum equals the
structural-penalty mass `DarkDeceptaconLoss` charges. -/
theorem bule_score_equals_void_penalty (b : BuleyUnit) :
    VoidPenalty (buleyUnitScore b) = buleyUnitScore b := rfl

/-- A single +1 swerve lift on the vacuum produces `VoidPenalty` exactly 1
on every face. The unit clinamen residue from `UniversalClinamenPlusOne`
is exactly one quantum of structural penalty. -/
theorem swerve_lift_from_vacuum_has_unit_void_penalty (f : BuleyFace) :
    VoidPenalty (buleyUnitScore (swerveLift vacuumBuleUnit f)) = 1 := by
  show buleyUnitScore (swerveLift vacuumBuleUnit f) = 1
  rw [swerve_lift_score_strict_increment, vacuum_has_zero_score]

/-- The omniscience-overflow failure mode from `DarkDeceptaconLoss`
applies directly to any Bule unit whose score exceeds a memory bound:
the Bule penalty is the void penalty, so excess Bule mass is exactly
the catastrophic-attention overflow. -/
theorem bule_score_overflow_is_void_overflow
    (b : BuleyUnit) (memoryBound : Nat)
    (h : buleyUnitScore b > memoryBound) :
    VoidPenalty (buleyUnitScore b) > memoryBound := by
  show buleyUnitScore b > memoryBound
  exact h

/-- For every memory bound, there is a Bule unit whose `VoidPenalty`
exceeds it. The omniscience failure mode is reachable via clinamen
lifts from the vacuum — the witness is `⟨memoryBound + 1, 0, 0⟩`,
i.e. `memoryBound + 1` waste-face swerve lifts. -/
theorem bule_omniscience_overflow_witness (memoryBound : Nat) :
    ∃ b : BuleyUnit, VoidPenalty (buleyUnitScore b) > memoryBound := by
  refine ⟨⟨memoryBound + 1, 0, 0⟩, ?_⟩
  show (memoryBound + 1) + 0 + 0 > memoryBound
  exact Nat.lt_succ_self memoryBound

end BuleyDarkDeceptaconBridge
end Gnosis
