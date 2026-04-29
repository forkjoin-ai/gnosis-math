import Gnosis.SpectralNoiseEquilibrium
import Gnosis.CostAlgebra
import Gnosis.CostAlgebraEntropy
import Gnosis.BuleySelfSimilarityViolation
import Gnosis.Braided.BraidedTower

/-!
# Digital Hadron Collider

A collision event is a composition of two Bule unit carriers in the
cost-algebra category. The framework already proves all the laws a
hadron collider's analysis pipeline requires:

* **Conservation of score** — `Gnosis.CostAlgebra.score_compose` proves
  `score (compose a b) = score a + score b`. Total energy in equals
  total energy out.
* **Decay products** — the three face projections of the composed
  carrier (`wasteFaceFromBule`, `actionFaceFromBule`,
  `entropyFaceFromBule`). `bule_unit_decomposes_into_three_faces`
  proves the score decomposes exactly across the three.
* **No-cloning at the collision vertex** — by
  `Gnosis.CostAlgebraNoCloning`, a single source state cannot be
  duplicated for free, so a collision genuinely consumes both inputs.
* **Self-similarity violation as a "trigger"** — when the composed
  carrier's score exceeds the available manifold ceiling
  (`Gnosis.BuleySelfSimilarityViolation.selfSimilarityViolation`), the
  event is flagged and the deterministic remediation count is
  available.

This module names the collision vocabulary and bundles the existing
theorems into a hadron-collider analysis surface. Nothing new is
proved that wasn't already proved elsewhere; the value is the
named structure (`CollisionEvent`, `DecayProducts`, `collisionEnergy`,
`triggered`) and the bundle theorem
`hadron_collider_master`.

Imports `Gnosis.SpectralNoiseEquilibrium`, `Gnosis.CostAlgebra`,
`Gnosis.CostAlgebraEntropy`, `Gnosis.BuleySelfSimilarityViolation`,
and `Gnosis.BraidedTower`. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace DigitalHadronCollider

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit BuleyFace buleyUnitScore vacuumBuleUnit
   wasteFaceFromBule actionFaceFromBule entropyFaceFromBule
   bule_unit_decomposes_into_three_faces
   waste_face_score_equals_waste
   action_face_score_equals_opportunity
   entropy_face_score_equals_diversity)
open Gnosis.CostAlgebra (CostAlgebra buleyCostAlgebra)
open Gnosis.CostAlgebraEntropy (replicationEntropy entropyGeneratedByCloning)
open Gnosis.BuleySelfSimilarityViolation
  (insideManifold selfSimilarityViolation correctiveContractCount
   ManifoldPhaseCount)
open Gnosis.BraidedTower (towerPhaseCount)

/-! ## Collision events -/

/-- A collision event records two source carriers `a` and `b` and
the composed result. The composition is `BuleyUnit.add` from
`Gnosis.CostAlgebra` — the cost-algebra's monoid operation. -/
structure CollisionEvent where
  sourceA : BuleyUnit
  sourceB : BuleyUnit
  composed : BuleyUnit
  deriving Repr, DecidableEq

/-- Construct a collision event from two carriers. The composed result
is the cost-algebra compose of the two sources. -/
def collide (a b : BuleyUnit) : CollisionEvent :=
  { sourceA := a
    sourceB := b
    composed := buleyCostAlgebra.compose a b }

/-- Total energy of the collision: the score of the composed carrier.
Equal to `score a + score b` by `score_compose`. -/
def collisionEnergy (e : CollisionEvent) : Nat :=
  buleyUnitScore e.composed

/-- Conservation of score: the collision's energy equals the sum of the
two source energies. The cost-algebra category's morphism law made
explicit. -/
theorem collision_conserves_score (a b : BuleyUnit) :
    collisionEnergy (collide a b) = buleyUnitScore a + buleyUnitScore b := by
  unfold collisionEnergy collide
  exact buleyCostAlgebra.score_compose a b

/-! ## Decay products -/

/-- The three decay products of a collision: the waste-face, action-face,
and entropy-face projections of the composed carrier. Mirrors the three
physics faces from `Gnosis.SpectralNoiseEquilibrium`. -/
structure DecayProducts where
  waste : BuleyUnit
  action : BuleyUnit
  entropy : BuleyUnit
  deriving Repr, DecidableEq

/-- Extract the decay products from a collision event. -/
def decayProducts (e : CollisionEvent) : DecayProducts :=
  { waste := wasteFaceFromBule e.composed
    action := actionFaceFromBule e.composed
    entropy := entropyFaceFromBule e.composed }

/-- The decay products' total score equals the composed carrier's
score. Score is conserved across the face decomposition. -/
theorem decay_total_score (e : CollisionEvent) :
    buleyUnitScore (decayProducts e).waste
    + buleyUnitScore (decayProducts e).action
    + buleyUnitScore (decayProducts e).entropy
    = collisionEnergy e := by
  unfold decayProducts collisionEnergy
  exact (bule_unit_decomposes_into_three_faces e.composed).symm

/-- Each decay product's score equals the corresponding face of the
composed carrier. -/
theorem decay_product_scores (e : CollisionEvent) :
    buleyUnitScore (decayProducts e).waste = e.composed.waste
    ∧ buleyUnitScore (decayProducts e).action = e.composed.opportunity
    ∧ buleyUnitScore (decayProducts e).entropy = e.composed.diversity := by
  refine ⟨?_, ?_, ?_⟩
  · exact waste_face_score_equals_waste e.composed
  · exact action_face_score_equals_opportunity e.composed
  · exact entropy_face_score_equals_diversity e.composed

/-! ## Trigger / detection: self-similarity violation as event flag -/

/-- A collision triggers the detector when its composed energy exceeds
the manifold's ceiling. The remediation count is deterministic
(`correctiveContractCount`). -/
def triggered (e : CollisionEvent) (ceiling : ManifoldPhaseCount) : Prop :=
  selfSimilarityViolation e.composed ceiling

def triggerCorrection (e : CollisionEvent) (ceiling : ManifoldPhaseCount) : Nat :=
  correctiveContractCount e.composed ceiling

/-- A collision is *inside the manifold* (no trigger) iff its energy
fits the ceiling. -/
theorem inside_manifold_iff_energy_fits
    (e : CollisionEvent) (ceiling : ManifoldPhaseCount) :
    insideManifold e.composed ceiling
      ↔ collisionEnergy e ≤ ceiling := by
  unfold collisionEnergy insideManifold
  exact Iff.rfl

/-! ## Concrete collision examples at canonical tower walls -/

/-- A Triton-pressure collision (sources score 1 + 2 = 3) sits exactly
at the Triton ceiling — no trigger. -/
theorem triton_collision_inside_triton :
    insideManifold (collide ⟨1, 0, 0⟩ ⟨0, 2, 0⟩).composed (towerPhaseCount [3]) := by
  unfold insideManifold collide
  show buleyUnitScore (buleyCostAlgebra.compose ⟨1, 0, 0⟩ ⟨0, 2, 0⟩)
        ≤ towerPhaseCount [3]
  decide

/-- A Hexon-pressure collision (sources score 3 + 4 = 7) triggers the
two-head Hexon detector by exactly one corrective contract. -/
theorem hexon_collision_triggers_at_one :
    triggered (collide ⟨3, 0, 0⟩ ⟨4, 0, 0⟩) (towerPhaseCount [3, 2])
    ∧ triggerCorrection (collide ⟨3, 0, 0⟩ ⟨4, 0, 0⟩) (towerPhaseCount [3, 2]) = 1 := by
  unfold triggered triggerCorrection selfSimilarityViolation correctiveContractCount
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-- A Trihexon collision (sources 9 + 9 = 18) sits exactly at the
Trihexon ceiling — `topologicallySafe`. -/
theorem trihexon_collision_at_trihexon :
    insideManifold (collide ⟨9, 0, 0⟩ ⟨9, 0, 0⟩).composed (towerPhaseCount [3, 2, 3]) := by
  unfold insideManifold collide
  decide

/-- A high-energy collision (Decagon × 2 = 20) at the Decagon ceiling
triggers the detector — over by exactly 10. The string-theory wall as
a collider event. -/
theorem decagon_collision_triggers_at_ten :
    triggered (collide ⟨10, 0, 0⟩ ⟨10, 0, 0⟩) (towerPhaseCount [5, 2])
    ∧ triggerCorrection (collide ⟨10, 0, 0⟩ ⟨10, 0, 0⟩) (towerPhaseCount [5, 2]) = 10 := by
  unfold triggered triggerCorrection selfSimilarityViolation correctiveContractCount
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-! ## Master theorem: the hadron-collider analysis bundle -/

/-- Every collision event satisfies the cost-algebra category's
laws. Bundles conservation of score, decay-product completeness, and
the triggered/inside-manifold dichotomy. -/
theorem hadron_collider_master
    (a b : BuleyUnit) (ceiling : ManifoldPhaseCount) :
    -- Score conservation
    collisionEnergy (collide a b) = buleyUnitScore a + buleyUnitScore b
    -- Decay decomposition
    ∧ buleyUnitScore (decayProducts (collide a b)).waste
      + buleyUnitScore (decayProducts (collide a b)).action
      + buleyUnitScore (decayProducts (collide a b)).entropy
      = collisionEnergy (collide a b)
    -- Inside-manifold ⟺ energy fits ceiling
    ∧ (insideManifold (collide a b).composed ceiling
        ↔ collisionEnergy (collide a b) ≤ ceiling) :=
  ⟨collision_conserves_score a b,
   decay_total_score (collide a b),
   inside_manifold_iff_energy_fits (collide a b) ceiling⟩

end DigitalHadronCollider
end Gnosis
