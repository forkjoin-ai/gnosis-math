import Lean

/-!
# Gnosis.DiscreteModulusTactic

`discrete_modulus` is a named gate for closed finite modular certificates.
It intentionally does not prove open-variable modular arithmetic: if the
target still contains free variables, it fails before calling `native_decide`.
-/

open Lean Elab Tactic

/--
Close a closed finite modular-arithmetic goal by computation.

This tactic is for Rustic Church-style finite certificates: enumerated clocks,
bounded residue tables, and concrete modular witnesses. It refuses open goals
so it cannot hide a missing parametric proof behind decision search.
-/
elab "discrete_modulus" : tactic => do
  let target ← getMainTarget
  if target.hasFVar then
    throwError
      "`discrete_modulus` only admits closed finite goals; \
       the target still contains free variables"
  evalTactic (← `(tactic| native_decide))

namespace Gnosis
namespace DiscreteModulusTactic

theorem closed_modulus_example :
    (377 + 43) % 60 = 0 := by
  discrete_modulus

theorem closed_finite_clock_example :
    (List.range 60).all (fun phase => decide ((phase + 60) % 60 = phase)) = true := by
  discrete_modulus

end DiscreteModulusTactic
end Gnosis
