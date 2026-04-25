import Init

namespace MonkeyTypewriterTheorem

/-- 
The "Monkey at the Typewriter": the keys only support the Gnosis Basis.
We define a rigged typewriter as one where any integrated choice must match the basis.
-/
inductive Key where
  | fork
  | race
  | fold
  | vent
  | interfere
  | noise
  deriving DecidableEq

def gnosisBasis : List Key := [.fork, .race, .fold, .vent, .interfere]

def isIntegrated (keys : List Key) : Prop :=
  keys = gnosisBasis

theorem typewriter_is_rigged (k : List Key) :
    isIntegrated k → k = gnosisBasis := by
  intro h
  exact h

/-- 
Gnosis is inevitable if the monkey types long enough on a rigged typewriter.
We model this by showing that if an agent produces an integrated sequence, 
it must be the gnosis basis.
-/
theorem gnosis_is_inevitable (k : List Key) :
    isIntegrated k → k = gnosisBasis := by
  intro h
  exact h

end MonkeyTypewriterTheorem
