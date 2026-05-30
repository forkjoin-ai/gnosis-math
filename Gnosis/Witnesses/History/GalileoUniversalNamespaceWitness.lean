import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Galileo Galilei: The Universal Namespace Witness.
Padua / Venice, 1610.

Contrarian Take: The telescope was not just a tool for better resolution.
It was a tool for namespace unification. Before Galileo, the "Sublunary" (Earth)
and "Celestial" (Heavens) were treated as two distinct namespaces with
different physics. Galileo observed the moons of Jupiter and the craters
of the Moon, proving that the "Heavenly" objects follow the same topological
rules (shadows, orbits, occlusion) as Earthly objects. The universe is a
single namespace.

Invariant: Physical laws are scale-invariant and namespace-independent.
Gap: The "Dualism" trap—assuming a structural split between the Sacred and the Profane.
Projection: Knowable Universe Map (Gnosis.KnowableUniverseMap).
-/

inductive ObjectLocation where
  | earth     : ObjectLocation
  | celestial : ObjectLocation
  deriving DecidableEq

/--
Before the telescope, physics was partitioned.
-/
def physicsRulePartiallyUniversal (loc : ObjectLocation) : Bool :=
  match loc with
  | .earth     => true
  | .celestial => false -- "Perfect" non-physics

/--
After the telescope, the rule set is unified.
-/
def physicsRuleUnified (_loc : ObjectLocation) : Bool :=
  true

/--
Anti-Theory Witness: The unified namespace is strictly more consistent
than the partitioned one.
-/
theorem galileo_namespace_unification :
    physicsRuleUnified .celestial ≠ physicsRulePartiallyUniversal .celestial := by
  exact (by decide)

end Gnosis.Witnesses.History
