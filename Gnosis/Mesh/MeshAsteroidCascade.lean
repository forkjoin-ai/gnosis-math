import Init
import Gnosis.ArrowBuleDeficit

namespace Gnosis
namespace MeshAsteroidCascade

open ArrowBuleDeficit

inductive CollisionState
  | planetesimalFlow  -- Large stable bodies
  | kesslerCascade    -- Fragmentation friction
  | spaceDustVoid     -- Maximum entropy saturation

inductive OrbitalForce
  | topologicalVacuum   -- Accretion flow
  | collisionalFriction -- Fragmentation noise
  | pauliExclusion      -- Saturation density / Kessler trap

def reduceOrbitalState (s : CollisionState) : OrbitalForce :=
  match s with
  | CollisionState.planetesimalFlow => OrbitalForce.topologicalVacuum
  | CollisionState.kesslerCascade => OrbitalForce.collisionalFriction
  | CollisionState.spaceDustVoid => OrbitalForce.pauliExclusion

structure AsteroidKernel where
  collisionDensity : Nat
  orbitalVelocity : Nat
  validBelt : collisionDensity + orbitalVelocity > 0

def isKesslerCascading (k : AsteroidKernel) : Prop :=
  k.collisionDensity > k.orbitalVelocity

def applyOrbitalEjection (k : AsteroidKernel) (alpha : Nat) : AsteroidKernel :=
  { collisionDensity := k.collisionDensity
    orbitalVelocity := k.orbitalVelocity + alpha
    validBelt :=
      -- Init-only: rewrite associativity and use `h < a + b ≤ (a + b) + alpha`.
      (Nat.add_assoc k.collisionDensity k.orbitalVelocity alpha) ▸
        Nat.lt_of_lt_of_le k.validBelt (Nat.le_add_right _ alpha) }

theorem ejection_clears_cascade (k : AsteroidKernel) :
    ∃ (alpha : Nat), ¬ isKesslerCascading (applyOrbitalEjection k alpha) := by
  refine ⟨k.collisionDensity, ?_⟩
  simp [isKesslerCascading, applyOrbitalEjection]

end MeshAsteroidCascade
end Gnosis