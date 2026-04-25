import Init

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Gnosis
namespace ArrowBuleDeficit

structure ArrowFailure where
  unanimityFailure : Nat
  iiaFailure : Nat
  dictatorshipWeight : Nat
deriving Repr, DecidableEq

def buleDeficit (f : ArrowFailure) : Nat :=
  f.unanimityFailure + f.iiaFailure + f.dictatorshipWeight

/-- The total topological deficit is conserved across transitions. -/
def buleConservationShift (f1 f2 : ArrowFailure) : Prop :=
  buleDeficit f1 = buleDeficit f2

end ArrowBuleDeficit
end Gnosis