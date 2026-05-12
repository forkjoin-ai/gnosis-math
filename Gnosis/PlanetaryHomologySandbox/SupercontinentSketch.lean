/-!
# Supercontinent Connectivity Sketch

Init-only finite witness for the planetary `β₀` monotonicity intuition.

The historical artifact proved a general graph-supergraph theorem with an
external graph library.  This replacement captures the core geological move:
adding a bridge between two isolated continents merges connected components
and therefore does not increase `β₀`.
-/

namespace PlanetaryHomologySandbox

/-- A minimal two-continent graph: either separated, or joined by one bridge. -/
structure TwoContinentGraph where
  hasBridge : Bool
deriving Repr, DecidableEq

/-- Connected-component count for the two-continent sketch. -/
def twoContinentBeta0 (graph : TwoContinentGraph) : Nat :=
  if graph.hasBridge then 1 else 2

/-- Add the supercontinent bridge. -/
def addSupercontinentBridge (_graph : TwoContinentGraph) : TwoContinentGraph :=
  { hasBridge := true }

/-- A separated two-continent graph has two components. -/
theorem separated_two_continent_beta0 :
    twoContinentBeta0 { hasBridge := false } = 2 := by
  rfl

/-- A bridged two-continent graph has one component. -/
theorem bridged_two_continent_beta0 :
    twoContinentBeta0 { hasBridge := true } = 1 := by
  rfl

/-- Adding the bridge does not increase the component count. -/
theorem addSupercontinentBridge_beta0_nonincreasing
    (graph : TwoContinentGraph) :
    twoContinentBeta0 (addSupercontinentBridge graph) ≤
      twoContinentBeta0 graph := by
  cases graph with
  | mk hasBridge =>
      cases hasBridge <;> decide

/-- In the separated case, adding the bridge strictly reduces `β₀`. -/
theorem addSupercontinentBridge_strictly_reduces_separated :
    twoContinentBeta0 (addSupercontinentBridge { hasBridge := false }) <
      twoContinentBeta0 { hasBridge := false } := by
  decide

end PlanetaryHomologySandbox
