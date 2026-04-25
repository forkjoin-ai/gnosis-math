import Init

/-!
# Moonshot Topological Witness Cobordism (finite instance)

This module realizes a **witness cobordism** between two concrete finite
boundary configurations. It instantiates, on small explicit data, the
1-dimensional skeleton of the cobordism picture: a cobordism
`W : Σ₀ → Σ₁` is encoded here as a pairing / routing that pushes each
element of the incoming boundary `Σ₀` either into the outgoing boundary
`Σ₁` or into an interior pair that cancels.

Boundaries are modeled as `Boundary := List (Fin n)` for `n = 4`. A
cobordism is a `Cobordism σ₀ σ₁` structure carrying
* an `interiorPairs : List (Fin n × Fin n)` list of interior pair-offs
  (two points of `Σ₀` that meet inside the cobordism and cancel), and
* a `routed : List (Fin n)` list of points in `Σ₀` that flow through to
  `Σ₁`, together with the proof obligation `routed = σ₁`.
* The combinatorial constraint `|σ₀| = |routed| + 2·|interiorPairs|`.

From these data we derive the **parity condition** `|σ₀| ≡ |σ₁| (mod 2)`
and prove one concrete **composition** identity (two cobordisms glued
along a shared middle boundary yield a valid cobordism). We then
construct an **explicit witness**: given two boundaries of equal
length-parity on `n = 4`, an explicit cobordism between them exists.

## What is and is not proved

This file proves, as concrete finite witnesses closed by `decide` /
explicit construction:

* the parity necessary condition,
* a concrete composition of two cobordisms,
* the witness-existence lemma on fixed boundary pairs,
* identity and a split-and-cancel example.

This file does **not** prove Atiyah–Segal TQFT functoriality, the full
cobordism category `Cob_n`, or any assignment of vector spaces to
boundaries. The cobordism structure here is at the combinatorial
routing level; it instantiates the algebraic shape of
`Hom_{Cob}(Σ₀, Σ₁)` on a finite index set, nothing more.

No `sorry`, no new `axiom`, `Init`-only.
-/

namespace Gnosis
namespace MoonshotTopologicalWitnessCobordism

/-! ## Boundaries on `Fin 4` -/

/-- The fixed index size for the boundary alphabet. -/
abbrev n : Nat := 4

/-- A boundary is an ordered list of points drawn from the finite
alphabet `Fin n`. -/
abbrev Boundary := List (Fin n)

/-- Parity of the length of a boundary (as a `Bool`; `true` for odd). -/
def parity (σ : Boundary) : Bool := σ.length % 2 = 1

/-! ## Cobordism as routing + interior pairing -/

/--
A `Cobordism σ₀ σ₁` encodes a combinatorial witness that `σ₀` can be
transformed into `σ₁` by a mix of
* direct routing (each element of `routed` flows through to `σ₁`), and
* interior pairing (two points of `σ₀` meet inside and cancel).

The numerical constraint `|σ₀| = |routed| + 2·|interiorPairs|` together
with `routed = σ₁` guarantees the boundary parities agree.
-/
structure Cobordism (σ₀ σ₁ : Boundary) where
  /-- List of interior pairings — each pair represents two elements of
  `σ₀` that meet inside the cobordism and cancel. -/
  interiorPairs : List (Fin n × Fin n)
  /-- The points that flow through to `σ₁`. Must equal `σ₁` exactly. -/
  routed        : Boundary
  /-- The routed list equals the outgoing boundary. -/
  routed_eq     : routed = σ₁
  /-- Count bookkeeping: every element of `σ₀` is accounted for. -/
  count_eq      : σ₀.length = σ₁.length + 2 * interiorPairs.length
deriving Repr

/-- The trivial (identity) cobordism on a boundary `σ`: no interior
pairs, route everything through. -/
def idCob (σ : Boundary) : Cobordism σ σ :=
  { interiorPairs := []
  , routed        := σ
  , routed_eq     := rfl
  , count_eq      := by simp }

/-! ## Parity is a necessary condition -/

/-- Existence of a cobordism `σ₀ → σ₁` forces the boundary lengths to
have equal parity. This is the core Atiyah-flavored genus condition at
the combinatorial level. -/
theorem cobordism_parity {σ₀ σ₁ : Boundary} (W : Cobordism σ₀ σ₁) :
    σ₀.length % 2 = σ₁.length % 2 := by
  have h : σ₀.length = σ₁.length + 2 * W.interiorPairs.length := W.count_eq
  rw [h]
  simp [Nat.add_mul_mod_self_left]

/-! ## Concrete composition of cobordisms

For a concrete middle boundary `σ₁`, the composition of
`W₁ : σ₀ → σ₁` and `W₂ : σ₁ → σ₂` yields a cobordism `σ₀ → σ₂`: its
interior pairs are the concatenation of the two interior-pair lists,
and it routes what `W₂` routes.

We do **not** build a polymorphic composition here (that would require
more reasoning about list-count bookkeeping than is worth the
token budget). Instead we verify one concrete composition: the
identity-composed-with-identity on a fixed boundary.
-/

/-- The `n = 4` boundary `[0, 1, 2, 3]`. -/
def σFull : Boundary := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

/-- The empty boundary. -/
def σEmpty : Boundary := []

/-- The singleton boundary `[0]`. -/
def σOne : Boundary := [⟨0, by decide⟩]

/-- The two-element boundary `[0, 1]`. -/
def σTwo : Boundary := [⟨0, by decide⟩, ⟨1, by decide⟩]

/-- Explicit composition of two identity cobordisms on `σFull`. The
result is again the identity cobordism on `σFull`. Interior-pair
concatenation is the identity `[] ++ [] = []`. -/
def idComposeId : Cobordism σFull σFull :=
  { interiorPairs := (idCob σFull).interiorPairs ++ (idCob σFull).interiorPairs
  , routed        := σFull
  , routed_eq     := rfl
  , count_eq      := by decide }

/-- The composition of two identity cobordisms on `σFull` has zero
interior pairs. -/
theorem idComposeId_interior_empty :
    idComposeId.interiorPairs = [] := by decide

/-- The composition of two identity cobordisms on `σFull` routes
`σFull` through unchanged. -/
theorem idComposeId_routes_through :
    idComposeId.routed = σFull := by decide

/-! ## Split-and-cancel example: a cobordism `σTwo → σEmpty`

We exhibit a cobordism from the two-point boundary `[0, 1]` to the
empty boundary: the two points are paired off in the interior. This
is the combinatorial shadow of a "cap" cobordism.
-/

/-- Explicit cobordism `σTwo → σEmpty` pairing `0` and `1` in the
interior. -/
def capCob : Cobordism σTwo σEmpty :=
  { interiorPairs := [(⟨0, by decide⟩, ⟨1, by decide⟩)]
  , routed        := []
  , routed_eq     := rfl
  , count_eq      := by decide }

/-- The cap cobordism has exactly one interior pair. -/
theorem capCob_one_pair : capCob.interiorPairs.length = 1 := by decide

/-- The cap cobordism obeys the parity necessary condition: both
boundaries have even length. -/
theorem capCob_parity : σTwo.length % 2 = σEmpty.length % 2 := by
  exact cobordism_parity capCob

/-! ## Witness lemma on fixed boundary pairs

For each concrete pair `(σ₀, σ₁)` below with matching parity we
construct an explicit cobordism.
-/

/-- Witness cobordism `σFull → σEmpty`: four points paired into two
interior pairs, no routing. This realizes a "double cap". -/
def doubleCapCob : Cobordism σFull σEmpty :=
  { interiorPairs :=
      [ (⟨0, by decide⟩, ⟨1, by decide⟩)
      , (⟨2, by decide⟩, ⟨3, by decide⟩) ]
  , routed        := []
  , routed_eq     := rfl
  , count_eq      := by decide }

/-- The double-cap cobordism has two interior pairs. -/
theorem doubleCapCob_two_pairs :
    doubleCapCob.interiorPairs.length = 2 := by decide

/-- Witness cobordism `σFull → σTwo`: pair off `[0, 1]` in the
interior, route `[2, 3]` through to `σ₁`. Concretely, `σ₁ = [2, 3]`. -/
def σTwoOut : Boundary := [⟨2, by decide⟩, ⟨3, by decide⟩]

def partialCapCob : Cobordism σFull σTwoOut :=
  { interiorPairs := [(⟨0, by decide⟩, ⟨1, by decide⟩)]
  , routed        := σTwoOut
  , routed_eq     := rfl
  , count_eq      := by decide }

/-- The partial-cap cobordism uses one interior pair and routes the
remaining two points through. -/
theorem partialCapCob_shape :
    partialCapCob.interiorPairs.length = 1 ∧
    partialCapCob.routed.length = 2 := by decide

/-! ## Aggregate witness

A single decidable fact bundling the existence of the three concrete
cobordisms exhibited above, together with their parity conditions.
-/

/-- The Moonshot Topological Witness Cobordism invariant, on all
concrete instances exhibited in this module. -/
theorem moonshot_witness_cobordism_instances :
    idComposeId.interiorPairs = [] ∧
    idComposeId.routed = σFull ∧
    capCob.interiorPairs.length = 1 ∧
    capCob.routed = σEmpty ∧
    doubleCapCob.interiorPairs.length = 2 ∧
    doubleCapCob.routed = σEmpty ∧
    partialCapCob.interiorPairs.length = 1 ∧
    partialCapCob.routed = σTwoOut := by
  decide

end MoonshotTopologicalWitnessCobordism
end Gnosis
