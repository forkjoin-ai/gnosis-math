import Init
import Gnosis.SkymeshTeleport

namespace Gnosis
namespace RhizomeRouting

open SkymeshTeleport

/-!
# Rhizome routing soundness — Init-only (Rustic Church)

Mirrors `open-source/aeon-shell/src/rhizome/{types,world,resolver}.ts`.

A rhizome world is a set of nodes and a set of directed edges (`source -> target`).
An address `resolves` when the resolver can produce a route: a path from a source
node to a target node. Resolution is therefore reachability — there EXISTS a path
whose head is the source and whose last node is the target.

We keep the carrier finite and explicit:

  - nodes are `Nat` ids,
  - the edge set is a `List (Nat × Nat)` of directed pairs,
  - a route is a `List Nat` of node ids,
  - `IsPath` is an inductive predicate: every consecutive pair is an edge.

Per the Rustic Church bridge rule, the network/transport truth (mailbox delivery,
encryption, presence peers) stays OUTSIDE Lean; here we prove only the finite
routing-soundness algebra:

  1. a routed path is made of real edges (`path_steps_are_edges`),
  2. a route connects its declared endpoints (`path_endpoints`),
  3. an address resolves IFF its target is reachable (`resolves_iff_reachable`),
  4. a disconnected target does NOT resolve — fail honest, no phantom route
     (`disconnected_target_unresolved`, `empty_world_resolves_nothing`),
  5. a resolved holder served over the Skymesh teleport replays at
     `geodesicLength = 0` (`resolve_then_teleport_is_geodesic_zero`).

No `omega`, no `simp`/`decide` on open goals; `decide` only on closed numerics.
-/

/-! ## The rhizome world: nodes and directed edges -/

/-- An edge `a -> b` is present when the directed pair is in the edge list. -/
def IsEdge (edges : List (Nat × Nat)) (a b : Nat) : Prop :=
  (a, b) ∈ edges

/--
A route is an `IsPath` over the edge set: every consecutive pair of node ids in
the list is a real directed edge. Structural / inductive on the list.

  - `nil` and a single node `[v]` are (degenerate) paths,
  - `a :: b :: rest` is a path when `a -> b` is an edge AND `b :: rest` is a path.
-/
inductive IsPath (edges : List (Nat × Nat)) : List Nat → Prop where
  /-- The empty route is a path. -/
  | nil : IsPath edges []
  /-- A single node is a path. -/
  | single (v : Nat) : IsPath edges [v]
  /-- Extend a path by a leading edge `a -> b`. -/
  | cons {a b : Nat} {rest : List Nat}
      (he : IsEdge edges a b) (hp : IsPath edges (b :: rest)) :
      IsPath edges (a :: b :: rest)

/-! ## 1. Every step of a route is a real edge -/

/--
`path_steps_are_edges`: for a route `a :: b :: rest`, the leading step `a -> b`
is a genuine edge. By construction of `IsPath.cons`.
-/
theorem path_steps_are_edges {edges : List (Nat × Nat)} {a b : Nat}
    {rest : List Nat} (h : IsPath edges (a :: b :: rest)) :
    IsEdge edges a b := by
  cases h with
  | cons he _ => exact he

/--
The tail of a route is itself a route: dropping the head of a path leaves a path.
Lets us walk the whole route step by step, each step a real edge.
-/
theorem path_tail_is_path {edges : List (Nat × Nat)} {a b : Nat}
    {rest : List Nat} (h : IsPath edges (a :: b :: rest)) :
    IsPath edges (b :: rest) := by
  cases h with
  | cons _ hp => exact hp

/-! ## 2. A route connects its endpoints -/

/--
`path_endpoints` (head): a non-empty route's head is exactly the declared source.
`List.head?` of `from :: via` is `some from`, with no edge reasoning needed.
-/
theorem path_endpoints_head (from_ : Nat) (via : List Nat) :
    (from_ :: via).head? = some from_ := rfl

/--
`getLast?` walks to the end of a non-empty route. Structural induction on the
remaining tail; the single-node base is `rfl`, the cons step recurses.
-/
theorem getLast_cons_cons (a b : Nat) (rest : List Nat) :
    (a :: b :: rest).getLast? = (b :: rest).getLast? := rfl

/--
`path_endpoints`: a route ending in `to_` reports `to_` as its last node. We state
it on the canonical "route ends at `to_`" shape `via ++ [to_]`: the last node is
always the declared target, for any prefix `via`. Structural induction on `via`.
-/
theorem path_endpoints (to_ : Nat) (via : List Nat) :
    (via ++ [to_]).getLast? = some to_ := by
  induction via with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      -- (x :: y :: ys) ++ [to_] = x :: ((y :: ys) ++ [to_])
      show ((y :: ys) ++ [to_]).getLast? = some to_
      exact ih

/-! ## 3. Resolution is reachability -/

/--
Reachability: the target `to_` is reachable from the source `from_` when there
EXISTS a route `p` that is a real path, starts at `from_`, and ends at `to_`.
This is exactly the resolver's job — find a route connecting the two.
-/
def Reachable (edges : List (Nat × Nat)) (from_ to_ : Nat) : Prop :=
  ∃ p, IsPath edges p ∧ p.head? = some from_ ∧ p.getLast? = some to_

/--
The resolver verdict: an address `(from_, to_)` resolves in `edges` exactly when
a connecting route exists. We define `resolve` AS reachability (the resolver
returns `resolved = true` iff it found such a path), keeping the soundness link
definitional and honest.
-/
def resolve (edges : List (Nat × Nat)) (from_ to_ : Nat) : Prop :=
  Reachable edges from_ to_

/--
`resolves_iff_reachable`: an address resolves IFF the target is reachable from
the source. Definitional — the resolver does not invent routes it cannot walk.
-/
theorem resolves_iff_reachable (edges : List (Nat × Nat)) (from_ to_ : Nat) :
    resolve edges from_ to_ ↔ Reachable edges from_ to_ :=
  Iff.rfl

/--
A witnessed route resolves the address it connects: given a real path from
`from_` to `to_`, the resolver succeeds. Soundness in the positive direction.
-/
theorem route_resolves {edges : List (Nat × Nat)} {from_ to_ : Nat}
    {p : List Nat} (hp : IsPath edges p)
    (hh : p.head? = some from_) (hl : p.getLast? = some to_) :
    resolve edges from_ to_ :=
  ⟨p, hp, hh, hl⟩

/--
A direct edge `from_ -> to_` resolves: the two-node route `[from_, to_]` is a
real path with the right endpoints. The base case of routing.
-/
theorem edge_resolves {edges : List (Nat × Nat)} {from_ to_ : Nat}
    (he : IsEdge edges from_ to_) :
    resolve edges from_ to_ :=
  route_resolves
    (IsPath.cons he (IsPath.single to_))
    rfl
    rfl

/-! ## 4. Fail honest: disconnected / empty worlds resolve nothing -/

/--
A non-empty route in the EMPTY world can only be a single node: there are no
edges, so no two-node step can ever be taken. Eliminates the `cons` case via the
impossible `IsEdge [] a b` (membership in the empty list).
-/
theorem empty_world_path_is_single {p : List Nat} (h : IsPath [] p) :
    p = [] ∨ ∃ v, p = [v] := by
  cases h with
  | nil => exact Or.inl rfl
  | single v => exact Or.inr ⟨v, rfl⟩
  | cons he _ =>
    -- he : IsEdge [] a b ≡ (a, b) ∈ [] — impossible
    exact absurd he List.not_mem_nil

/--
`empty_world_resolves_nothing`: in a world with NO edges, no DISTINCT target is
reachable. A route from `from_` to a different `to_` would need at least one
step, but the empty world has no edges to step on — so the resolver fails honest
rather than fabricating a phantom route.
-/
theorem empty_world_resolves_nothing {from_ to_ : Nat} (hne : from_ ≠ to_) :
    ¬ resolve [] from_ to_ := by
  intro h
  obtain ⟨p, hp, hh, hl⟩ := h
  rcases empty_world_path_is_single hp with hnil | ⟨v, hv⟩
  · -- p = [] : head? = none ≠ some from_
    rw [hnil] at hh
    exact absurd hh (by intro hc; cases hc)
  · -- p = [v] : head? = some v = some from_ and getLast? = some v = some to_
    rw [hv] at hh hl
    -- hh : some v = some from_, hl : some v = some to_
    have hvf : v = from_ := by cases hh; rfl
    have hvt : v = to_ := by cases hl; rfl
    exact hne (hvf ▸ hvt)

/--
`disconnected_target_unresolved`: if NO route connects `from_` to `to_`, the
address does not resolve. Contrapositive of `resolves_iff_reachable` — the
resolver never returns `resolved` without a witnessing path.
-/
theorem disconnected_target_unresolved (edges : List (Nat × Nat))
    (from_ to_ : Nat) (h : ¬ Reachable edges from_ to_) :
    ¬ resolve edges from_ to_ :=
  fun hr => h ((resolves_iff_reachable edges from_ to_).mp hr)

/-! ## 5. Tie to Skymesh: a resolved holder teleports at geodesicLength = 0 -/

/--
`resolve_then_teleport_is_geodesic_zero`: if an address resolves to a holder AND
the holder passes the protocol69 Skymesh admission, the served cached replay
traverses no compute space (`geodesicLength = 0`). The reachable route witnesses
WHO holds the volume; `SkymeshTeleport.Admitted` witnesses that it may be served;
`SkymeshTeleport.geodesic_is_zero` gives the zero-length replay. Clean corollary —
no extra hypotheses, the route and the admission combine.
-/
theorem resolve_then_teleport_is_geodesic_zero
    {edges : List (Nat × Nat)} {from_ to_ : Nat}
    (hResolved : resolve edges from_ to_)
    (a : Admission) (hAdmitted : Admitted a) :
    Reachable edges from_ to_ ∧ Admitted a ∧ geodesicLength = 0 :=
  ⟨(resolves_iff_reachable edges from_ to_).mp hResolved,
   hAdmitted,
   geodesic_is_zero⟩

/--
The same corollary keyed on the underlying gates: a resolved route plus a holder
whose own four Skymesh gates all hold yields the zero-geodesic replay. Mirrors
`SkymeshProperties.skymesh_pillars` SOVEREIGN clause — admission is the holder's
own key alone, and a resolved route plus that key serves at geodesicLength = 0.
-/
theorem resolved_sovereign_holder_teleports
    {edges : List (Nat × Nat)} {from_ to_ : Nat}
    (hResolved : resolve edges from_ to_)
    (a : Admission)
    (hl : a.locked) (hag : a.agree) (hp : a.projectionOk) (hf : a.foilOk) :
    Reachable edges from_ to_ ∧ Admitted a ∧ geodesicLength = 0 :=
  resolve_then_teleport_is_geodesic_zero hResolved a ⟨hl, hag, hp, hf⟩

end RhizomeRouting
end Gnosis
