import Init
import Gnosis.VectorMath
import Gnosis.Body.FixedPoint

/-!
# Rigid-Body State and Conservation Invariants

A single rigid segment of the mechanical puppet. All vector quantities reuse
`Gnosis.VectorMath.Vector3` (signed `Int` components, fixed-point scaled); mass
is a positive scaled `Int`. The integrator is semi-implicit Euler: positions and
orientations advance, but the conserved quantities (linear/angular momentum)
are untouched by a force-free / torque-free step. Those are the load-bearing
invariants, and they hold *definitionally* — `rfl` — because the update copies
the conserved field unchanged.
-/

namespace Gnosis.Body.RigidBody

open Gnosis.VectorMath
open Gnosis.Body.FixedPoint

/-- Scalar multiply of a vector by a (fixed-point) integer factor. -/
def scaleVec (k : Int) (v : Vector3) : Vector3 :=
  ⟨k * v.x, k * v.y, k * v.z⟩

/-- State of one rigid body segment. -/
structure RigidBodyState where
  position : Vector3
  orientation : Vector3       -- exponential-coordinate orientation (signed)
  velocity : Vector3          -- linear velocity
  angularVelocity : Vector3
  momentum : Vector3          -- linear momentum p = m·v
  angularMomentum : Vector3   -- L
  mass : Int                  -- scaled mass (> 0)
  deriving Repr

/-- Semi-implicit Euler position update: `x' = x + v·dt`. -/
def stepPosition (s : RigidBodyState) (dt : Int) : RigidBodyState :=
  { s with position := s.position + scaleVec dt s.velocity }

/-- Orientation update: `θ' = θ + ω·dt`. -/
def stepOrientation (s : RigidBodyState) (dt : Int) : RigidBodyState :=
  { s with orientation := s.orientation + scaleVec dt s.angularVelocity }

/-- Apply a linear impulse: `p' = p + F·dt`. -/
def applyForce (s : RigidBodyState) (force : Vector3) (dt : Int) : RigidBodyState :=
  { s with momentum := s.momentum + scaleVec dt force }

/-- Apply a torque impulse: `L' = L + τ·dt`. -/
def applyTorque (s : RigidBodyState) (torque : Vector3) (dt : Int) : RigidBodyState :=
  { s with angularMomentum := s.angularMomentum + scaleVec dt torque }

/-- **Conservation of linear momentum**: a position step does not change `p`. -/
theorem momentum_conserved_under_position_step (s : RigidBodyState) (dt : Int) :
    (stepPosition s dt).momentum = s.momentum := rfl

/-- **Conservation of angular momentum**: an orientation step does not change `L`. -/
theorem angular_momentum_conserved_under_orientation_step (s : RigidBodyState) (dt : Int) :
    (stepOrientation s dt).angularMomentum = s.angularMomentum := rfl

/-- A position step never alters mass. -/
theorem mass_invariant_under_position_step (s : RigidBodyState) (dt : Int) :
    (stepPosition s dt).mass = s.mass := rfl

end Gnosis.Body.RigidBody
