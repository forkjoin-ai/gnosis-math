/-!
# Stratigraphy Steno Sketch

Init-only order witnesses for superposition, cross-cutting, and unconformity.
-/

namespace PlanetaryHomologySandbox

structure StenoStratumStack where
  time : Nat → Nat
  monotone : ∀ {i j : Nat}, i < j → time i < time j

theorem steno_superposition_transitive
    (stack : StenoStratumStack)
    {i j k : Nat}
    (hij : i < j)
    (hjk : j < k) :
    stack.time i < stack.time k := by
  exact Nat.lt_trans (stack.monotone hij) (stack.monotone hjk)

structure CrossCuttingEvent where
  faultTime : Nat
  stratumTime : Nat → Nat
  youngerThanAll : ∀ i, stratumTime i < faultTime

theorem cross_cutting_younger_than_all
    (event : CrossCuttingEvent)
    (i : Nat) :
    event.stratumTime i < event.faultTime :=
  event.youngerThanAll i

structure UnconformityGap where
  lowerPackageTop : Nat
  upperPackageBase : Nat
  gap : lowerPackageTop < upperPackageBase

theorem unconformity_gap_lt
    (gap : UnconformityGap) :
    gap.lowerPackageTop < gap.upperPackageBase :=
  gap.gap

end PlanetaryHomologySandbox
