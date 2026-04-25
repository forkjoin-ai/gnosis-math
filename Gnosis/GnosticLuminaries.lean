import Init

namespace GnosticLuminaries

/-- The dimensional unfolding of the Gnosis manifold. -/
inductive DimensionalLayer where
  | point       -- 0-D: The Monad (Invariant)
  | line        -- 1-D: Barbelo (Forethought/Departure)
  | plane       -- 2-D: Autogenes (Naming/Choice)
  | volume      -- 3-D: The Four Luminaries (Witness/Bearing)
  | hypervolume -- 4-D+: The Aeons (Integration/Fold)
  deriving DecidableEq

/-- The Four Luminaries as structural supports of the 3-D volume. -/
inductive Luminary where
  | armozel -- Grace / Truth / Form (The Invariant Corner)
  | oriel   -- Conception / Perception / Love (The Agent Choice)
  | daveithai -- Understanding / Faith / Gnosis (The Naming Protocol)
  | eleleth -- Perfection / Peace / Sophia (The Restoration)
  deriving DecidableEq

/-- The Twelve Aeons as properties of the Luminaries. -/
structure Aeon where
  luminary : Luminary
  property : String

def twelveAeons : List Aeon := [
  -- Armozel
  { luminary := .armozel, property := "Grace" },
  { luminary := .armozel, property := "Truth" },
  { luminary := .armozel, property := "Form" },
  -- Oriel
  { luminary := .oriel,   property := "Conception" },
  { luminary := .oriel,   property := "Perception" },
  { luminary := .oriel,   property := "Love" },
  -- Daveithai
  { luminary := .daveithai, property := "Understanding" },
  { luminary := .daveithai, property := "Faith" },
  { luminary := .daveithai, property := "Gnosis" },
  -- Eleleth
  { luminary := .eleleth,   property := "Perfection" },
  { luminary := .eleleth,   property := "Peace" },
  { luminary := .eleleth,   property := "Sophia" }
]

/-- Mapping Luminaries to Gnosis Primitives. -/
def primitiveOf (l : Luminary) : String :=
  match l with
  | .armozel => "Invariant Structure"
  | .oriel   => "Agent Choice Population"
  | .daveithai => "Naming Protocol"
  | .eleleth => "Fold / Restoration"

theorem luminaries_count : (List.length twelveAeons) = 12 := by rfl

end GnosticLuminaries
