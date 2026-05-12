import Gnosis.GnosisMathPrelude
import Gnosis.GnosisMath.ListNat
import Gnosis.GnosisMath.Fibonacci

/-!
# GnosisMath.Basic — barrel import

Stable surface for consumers that want the Init-only prelude plus list/Nat lemmas and the
Zeckendorf-aligned [`Fibonacci`](./Fibonacci.lean) weights without importing each file separately.
See [`GnosisMathPrelude`](../GnosisMathPrelude.lean), [`ListNat`](./ListNat.lean).
-/

namespace GnosisMath

/--
The `GnosisMath.Basic` barrel exposes the prelude power helper, list/Nat helper,
and Zeckendorf-aligned Fibonacci helper from a single import.
-/
theorem basic_barrel_exposes_prelude_listnat_and_fibonacci :
    powNat 2 3 = 2 * 2 * 2 ∧
    List.length ([fibZ 0, fibZ 1, fibZ 2] : List Nat) = 3 ∧
    fibZ 4 = 5 := by
  constructor
  · exact powNat_three 2
  · constructor
    · rfl
    · exact fibZ_four

end GnosisMath
