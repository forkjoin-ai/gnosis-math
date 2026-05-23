import Init
import Gnosis.Body.FixedPoint

/-!
# Static Stability via Support-Polygon Containment

A standing body is statically stable when the ground projection of its centre
of mass lies within its base of support. We model the base as a CCW triangle of
ground-contact points (the minimal non-degenerate polygon — three contacts) and
test containment with an *exact* integer 2D cross-product sign, so the predicate
is decidable and carries no floating-point error. The Rust integrator mirrors
`crossSign` / `Support.contains` bit-for-bit.
-/

namespace Gnosis.Body.Stability

open Gnosis.Body.FixedPoint

/-- A 2D ground-plane point (signed fixed-point `Int`). -/
structure P2 where
  x : Int
  y : Int
  deriving Repr, DecidableEq

/-- z-component of `(b - a) × (p - a)`: positive when `p` is left of `a→b`. -/
def crossSign (a b p : P2) : Int :=
  (b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x)

/-- `p` is left of, or exactly on, the directed edge `a→b`. -/
def leftOfOrOn (a b p : P2) : Prop := 0 ≤ crossSign a b p

/-- A triangular base of support, vertices in CCW order. -/
structure Support where
  a : P2
  b : P2
  c : P2
  deriving Repr

/-- `p` is inside (or on the boundary of) the support triangle: left-of-or-on
    every directed edge. -/
def Support.contains (s : Support) (p : P2) : Prop :=
  leftOfOrOn s.a s.b p ∧ leftOfOrOn s.b s.c p ∧ leftOfOrOn s.c s.a p

/-- Static stability: the COM ground projection lies within the support base. -/
def stable (s : Support) (com : P2) : Prop := s.contains com

/-- **Containment implies stability** — the bridge the controller relies on. -/
theorem stable_of_contains (s : Support) (com : P2) (h : s.contains com) :
    stable s com := h

/-- The cross sign at the edge's own start vertex is exactly zero. -/
theorem crossSign_start_zero (a b : P2) : crossSign a b a = 0 := by
  unfold crossSign
  rw [Int.sub_self a.y, Int.sub_self a.x, Int.mul_zero, Int.mul_zero, Int.sub_zero]

/-- A vertex is never strictly outside the edge that starts at it. -/
theorem leftOfOrOn_start (a b : P2) : leftOfOrOn a b a := by
  unfold leftOfOrOn
  rw [crossSign_start_zero]
  exact Int.le_refl 0

end Gnosis.Body.Stability
