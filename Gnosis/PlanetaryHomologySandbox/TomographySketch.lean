/-!
# Finite Tomography Collision Sketch

Concrete finite observation collisions for pair and vector forward maps.
-/

namespace PlanetaryHomologySandbox

inductive Hidden3 where
  | h0 | h1 | h2
deriving DecidableEq, Repr

inductive ObsUnit where
  | seen
deriving DecidableEq, Repr

def pairForward (_left _right : Hidden3 → ObsUnit) (_h : Hidden3) : ObsUnit × ObsUnit :=
  (ObsUnit.seen, ObsUnit.seen)

def vecForward (_stations : Nat) (_family : Nat → Hidden3 → ObsUnit)
    (_h : Hidden3) : Nat → ObsUnit :=
  fun _ => ObsUnit.seen

theorem pairForward_h0_h1_collision
    (left right : Hidden3 → ObsUnit) :
    pairForward left right Hidden3.h0 =
      pairForward left right Hidden3.h1 := by
  rfl

theorem hidden3_h0_ne_h1 : Hidden3.h0 ≠ Hidden3.h1 := by
  intro h
  cases h

theorem pairForward_not_injective_concrete
    (left right : Hidden3 → ObsUnit) :
    ¬ Function.Injective (pairForward left right) := by
  intro hInjective
  exact hidden3_h0_ne_h1 (hInjective (pairForward_h0_h1_collision left right))

theorem vecForward_h0_h1_collision
    (stations : Nat)
    (family : Nat → Hidden3 → ObsUnit) :
    vecForward stations family Hidden3.h0 =
      vecForward stations family Hidden3.h1 := by
  rfl

theorem vecForward_not_injective_concrete
    (stations : Nat)
    (family : Nat → Hidden3 → ObsUnit) :
    ¬ Function.Injective (vecForward stations family) := by
  intro hInjective
  exact hidden3_h0_ne_h1 (hInjective (vecForward_h0_h1_collision stations family))

end PlanetaryHomologySandbox
