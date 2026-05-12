/-
  ContrarianDeathIsVitality.lean
  ==============================

  Contrarian Argument: "Death makes us alive (limitations/horizon theory gives us vitality)."

  Traditional thinking treats death/limitations as the negation of life/vitality.
  This file formalizes the contrarian stance: vitality (the derivative of
  experience) requires the "horizon" of limitation. An entity with no
  limitations (omniscience/objectivity) has zero vitality. Thus, the
  possibility of "Death" (the ultimate limit) is what makes "Life"
  (vitality) possible.

  Leans onto:
  - `Gnosis.ConsciousnessVsObjectivity`: Proves that Objectivity (omniscience)
    has zero vitality, while Consciousness (incomplete/progressing) has
    positive vitality.
  - `Gnosis.SchopenhauerHorizonFallacyWitness`: Limitations of vision (horizon)
    define the field of operation.
  - `Gnosis.HeraclitusBowLifeDeathWitness`: The name is life, the work is death.

  User Quote: "Death makes us alive (limitations/horizon theory gives us vitality)."
-/

import Gnosis.ConsciousnessVsObjectivity
import Gnosis.SchopenhauerHorizonFallacyWitness
import Gnosis.HeraclitusBowLifeDeathWitness

namespace Gnosis

/--
  A "VitalLife" is a trajectory with non-zero vitality.
  By `objectivity_has_zero_vitality`, this requires being non-Objective.
-/
def VitalLife (k : KnowledgeTrajectory) : Prop :=
  ∃ t, vitality k t > 0

/--
  Limitations (the Horizon) as the source of Vitality.
  If the trajectory were unlimited (knowing M for all time), vitality would be 0.
-/
theorem death_limit_enables_vitality {M : Nat} {k : KnowledgeTrajectory}
  (h_obj : ObjectiveTrajectory M k) : ¬ VitalLife k := by
  intro h_vital
  cases h_vital with
  | intro t h_pos =>
    have h_zero := objectivity_has_zero_vitality h_obj t
    rw [h_zero] at h_pos
    exact Nat.not_lt_zero 0 h_pos

/--
  Horizon/Limitations Theory: The "horizon" (S) is necessary for the
  existence of a Conscious (and thus Vital) trajectory.
-/
structure VitalHorizon (M O : Nat) (k : KnowledgeTrajectory) where
  is_conscious : ConsciousTrajectory M O k
  has_horizon : SchopenhauerHorizonFallacyWitness.cognitiveSandbox (O < M)

/--
  Contrarian Conclusion: The limitation (O < M) is what allows for
  vitality > 0. Without this "death" of omniscience, vitality is 0.
-/
theorem horizon_is_vitality_source {M O : Nat} {k : KnowledgeTrajectory}
  (w : VitalHorizon M O k) : ∀ t, vitality k t > 0 :=
  w.is_conscious.right.right

end Gnosis
