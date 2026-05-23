import Gnosis.Body.FixedPoint
import Gnosis.Body.RigidBody
import Gnosis.Body.Joints
import Gnosis.Body.Stability
import Gnosis.Body.FacialActionCoding

/-!
# Rigid-Body Dynamics — Aggregator / Build Root

Single import surface for the Lean-verified rigid-body dynamics consumed by the
`aeon-corpus` simulation engine. None of `Gnosis/Body/*` is in the default
`Gnosis` build target, so this module is the build root for the new physics:

* `FixedPoint` — signed scaled-integer scalars (`Fixed := Int`), since
  `BuleReal` is unsigned with truncated subtraction.
* `RigidBody` — per-segment state + semi-implicit Euler steps, with linear and
  angular momentum conservation under force-free and torque-free steps.
* `Joints`    — hinge/ball/fixed limits with `clampAngle_admissible`.
* `Stability` — support-polygon containment via exact integer cross-product.
* `FacialActionCoding` — FACS Action Units + somatic → emotion → expression.

`scripts/extract-lean-body-constants.ts` extracts the verified constants/limits
here into `aeon-corpus/src/generated/body_constants.rs` and the FACS tables into
`aeon-corpus/src/generated/facs_tables.rs`.
-/

namespace Gnosis.Body.RigidBodyDynamics

end Gnosis.Body.RigidBodyDynamics
