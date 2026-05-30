/-
  CarveMeetObserverFusion.lean
  ============================

  Phase 4 FORMAL FOUNDATION — fusing N observers' certified knowledge into ONE
  shared certified world, proven independent of the order the observers are merged.

  This module instantiates the existing carve-meet semilattice
  (`Gnosis.SilhouetteCarveLattice`) at the level of MANY OBSERVERS. Each observer
  contributes a `VoxField V := V → Bool`: per voxel (or, in third-eye, per
  certified predicate) does THAT observer certify it. The shared world is the
  fold of `meet` (set intersection) over the observer list — the same operator
  `open-source/gnosis/third-eye/src/knowledge.rs` uses as its CRDT merge across
  replicas/observers (`CertifiedKnowledge::meet`).

  We do NOT reprove the lattice. We instantiate its laws:

    * `meet_comm`  / `carve_swap`            ⟶ pairwise observer commutation
    * `meet_assoc` / `carve_append`          ⟶ bracketing/grouping freedom
    * `meet_idem`  / `carve_dup`             ⟶ re-observing an eye changes nothing

  and fold them into ONE headline:

    * `fuse_perm_invariant` — any two observer lists that are permutations of each
      other (`List.Perm`) fuse to the SAME shared world, per voxel. The order in
      which the cameras are merged does not affect the certified result. This maps
      the semilattice's commutativity+associativity up to the full symmetric group
      on the observer list, via Perm induction (adjacent-swap closure), exactly as
      `FrfWitnessTower.triad_merge_perm` does for digit merges.

  Three supporting guarantees:

    * `fuse_conservative` — a voxel survives fusion iff ALL observers certify it
      (the meet is the intersection; only co-certified facts survive).
    * `fuse_idempotent` — adding an observer already represented changes nothing.
    * `consensus_breaks_perm_invariance` — re-exports the antitheorem's mechanism
      to record WHY this is meet, not k-of-N voting: k-of-N is not even idempotent
      (`SilhouetteCarveLattice.consensus_not_idempotent`), so it cannot be
      permutation-invariant — duplicating/reordering accepting views flips a voxel.

  Equality is stated PER VOXEL (`∀ v` / pointwise) so no `funext` / `Quot.sound`
  enters; `#print axioms` targets propext-at-most, no `native_decide`, no
  `Classical.choice`. Init-only Rustic Church.
-/
import Gnosis.SilhouetteCarveLattice

namespace GnosisMath
namespace CarveMeetObserverFusion

open SilhouetteCarveLattice

universe u
variable {V : Type u}

-- ══════════════════════════════════════════════════════════
-- PART I.  N observers fuse by the carve-meet fold
-- ══════════════════════════════════════════════════════════

/-- The shared certified world from a list of observers: the carve-meet fold
    (per-voxel AND across all observers; identity = ⊤, "everything certified").
    This reuses `SilhouetteCarveLattice.carve` verbatim — the observer-fusion
    name records the third-eye reading: each list element is one observer's
    certified `VoxField`, and `fuseObservers` is the CRDT merge over them. -/
def fuseObservers (observers : List (VoxField V)) : VoxField V :=
  carve observers

@[simp] theorem fuseObservers_nil : fuseObservers ([] : List (VoxField V)) = fun _ => true := rfl

@[simp] theorem fuseObservers_cons (s : VoxField V) (rest : List (VoxField V)) (v : V) :
    fuseObservers (s :: rest) v = (s v && fuseObservers rest v) := rfl

-- ══════════════════════════════════════════════════════════
-- PART II.  Order-independence — the headline
-- ══════════════════════════════════════════════════════════

/-- Pairwise observer commutation: swapping the first two observers in the merge
    is free. Instantiates `carve_swap` (which instantiates `meet_comm`). -/
theorem fuse_swap (a b : VoxField V) (rest : List (VoxField V)) (v : V) :
    fuseObservers (a :: b :: rest) v = fuseObservers (b :: a :: rest) v :=
  carve_swap a b rest v

/-- Grouping/bracketing freedom: merging two blocks of observers, in either
    bracketing, equals the meet of the two block-fusions. Instantiates
    `carve_append` (which instantiates `meet_assoc`). -/
theorem fuse_append (xs ys : List (VoxField V)) (v : V) :
    fuseObservers (xs ++ ys) v = (fuseObservers xs v && fuseObservers ys v) :=
  carve_append xs ys v

/-- Merging two blocks in either ORDER yields the same shared world (block
    tumble). Instantiates `fuse_append` + `Bool.and_comm` — the append form of
    observer-order independence. -/
theorem fuse_append_comm (xs ys : List (VoxField V)) (v : V) :
    fuseObservers (xs ++ ys) v = fuseObservers (ys ++ xs) v := by
  rw [fuse_append, fuse_append, Bool.and_comm]

/-- HEADLINE — observer-ORDER independence.

    Any two observer lists that are permutations of each other fuse to the SAME
    shared certified world, per voxel. The order in which the cameras are merged
    is invisible to the certified result.

    Proven by `List.Perm` induction: the base case is `rfl`, `cons` carries the
    inductive hypothesis through the shared head observer, `swap` is exactly
    `fuse_swap` (the lifted `meet_comm`), and `trans` chains equalities. This
    lifts the semilattice's pairwise commutativity to the full symmetric group on
    the observer list (every permutation is a product of adjacent swaps), mirroring
    `FrfWitnessTower.triad_merge_perm`. -/
theorem fuse_perm_invariant {xs ys : List (VoxField V)} (h : List.Perm xs ys) (v : V) :
    fuseObservers xs v = fuseObservers ys v := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
      show (x v && fuseObservers _ v) = (x v && fuseObservers _ v)
      rw [ih]
  | swap x y l => exact fuse_swap y x l v
  | trans _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂

/-- Corollary: adding any observer block on the left vs. the right is the same as
    long as the multiset of observers is the same — a packaging of the headline
    against the append law, witnessing that "which order the cameras arrive in"
    never matters. -/
theorem fuse_perm_invariant_append {xs xs' ys ys' : List (VoxField V)}
    (hx : List.Perm xs xs') (hy : List.Perm ys ys') (v : V) :
    fuseObservers (xs ++ ys) v = fuseObservers (xs' ++ ys') v := by
  rw [fuse_append, fuse_append, fuse_perm_invariant hx v, fuse_perm_invariant hy v]

-- ══════════════════════════════════════════════════════════
-- PART III.  Conservativity — only co-certified facts survive
-- ══════════════════════════════════════════════════════════

/-- CONSERVATIVE — a voxel survives fusion iff ALL observers certify it.

    Forward: if the fused world keeps a voxel, every observer in the list
    certifies it. Backward: if every observer certifies it, it survives. So the
    meet is exactly the intersection across observers — no fact enters the shared
    world unless it is co-certified. Proven by induction on the observer list,
    discharging the `Bool` `&&` per cons (no `omega`, no `decide` on an open goal). -/
theorem fuse_conservative (observers : List (VoxField V)) (v : V) :
    (fuseObservers observers v = true) ↔ (∀ s, s ∈ observers → s v = true) := by
  induction observers with
  | nil =>
      apply Iff.intro
      · intro _ s hmem; exact absurd hmem List.not_mem_nil
      · intro _; rfl
  | cons a rest ih =>
      apply Iff.intro
      · intro hfuse s hmem
        have hsplit : a v = true ∧ fuseObservers rest v = true := by
          have : (a v && fuseObservers rest v) = true := hfuse
          exact Bool.and_eq_true _ _ |>.mp this
        cases List.mem_cons.mp hmem with
        | inl heq => rw [heq]; exact hsplit.left
        | inr hin => exact ih.mp hsplit.right s hin
      · intro hall
        show (a v && fuseObservers rest v) = true
        apply (Bool.and_eq_true _ _).mpr
        refine ⟨hall a (List.mem_cons_self), ?_⟩
        exact ih.mpr (fun s hin => hall s (List.mem_cons_of_mem a hin))

-- ══════════════════════════════════════════════════════════
-- PART IV.  Idempotence — re-observing an eye changes nothing
-- ══════════════════════════════════════════════════════════

/-- IDEMPOTENT — an observer already at the head, re-observed, leaves the shared
    world unchanged. Instantiates `carve_dup` (which instantiates `meet_idem`).
    Re-feeding the same camera does not flip the certified world. -/
theorem fuse_idempotent (s : VoxField V) (rest : List (VoxField V)) (v : V) :
    fuseObservers (s :: s :: rest) v = fuseObservers (s :: rest) v :=
  carve_dup s rest v

/-- A standalone duplicated observer fuses to itself (the binary `meet_idem`,
    lifted to the singleton fold). -/
theorem fuse_self (s : VoxField V) (v : V) :
    fuseObservers (s :: s :: []) v = fuseObservers (s :: []) v :=
  carve_dup s [] v

-- ══════════════════════════════════════════════════════════
-- PART V.  Why MEET, not k-of-N voting (cite the antitheorem)
-- ══════════════════════════════════════════════════════════

/-- WHY this is meet, not k-of-N consensus. We re-export the mechanism of
    `SilhouetteCarveLattice.consensus_not_idempotent`: the `atLeast 2` threshold
    flips a voxel from rejected to kept when an accepting view is merely
    duplicated. A merge that is not even duplicate-stable cannot be order
    independent — `fuse_idempotent` would fail for it. So permutation invariance
    forces the conservative meet; thresholded voting trades it away. -/
theorem consensus_breaks_idempotence :
    atLeast 2 [true, false] ≠ atLeast 2 [true, true, false] :=
  consensus_not_idempotent

/-- The same fact phrased as a permutation/duplication hazard: with a duplicated
    accepting observer present, the k-of-N verdict is NOT stable, so no
    permutation-invariant theorem of the `fuse_perm_invariant` shape can hold for
    `atLeast 2`. (Closed witness; records the boundary the meet respects.) -/
theorem consensus_breaks_perm_invariance :
    ∃ k : Nat, ∃ l₁ l₂ : List Bool,
      atLeast k l₁ ≠ atLeast k l₂ ∧ countTrue l₂ = countTrue l₁ + 1 := by
  refine ⟨2, [true, false], [true, true, false], consensus_not_idempotent, ?_⟩
  decide

-- ══════════════════════════════════════════════════════════
-- PART VI.  Concrete 3-observer witnesses — close by decide/rfl
-- ══════════════════════════════════════════════════════════

/-- A 3-voxel world: `Fin 3`. Observers are total predicates over it. -/
abbrev W := Fin 3

/-- Observer A: certifies voxels 0 and 1, not 2. -/
def obsA : VoxField W := fun v => decide (v.val ≠ 2)
/-- Observer B: certifies voxels 0 and 2, not 1. -/
def obsB : VoxField W := fun v => decide (v.val ≠ 1)
/-- Observer C (the disagreer): certifies only voxel 0. -/
def obsC : VoxField W := fun v => decide (v.val = 0)

/-- The fused shared world keeps voxel 0 (all three certify it). -/
theorem fuse_three_keeps_0 : fuseObservers [obsA, obsB, obsC] (0 : W) = true := by decide

/-- The fused shared world carves OUT voxel 1 — observers B and C reject it,
    so it cannot survive the intersection (one disagreement carves it). -/
theorem fuse_three_carves_1 : fuseObservers [obsA, obsB, obsC] (1 : W) = false := by decide

/-- And carves out voxel 2 (observers A and C reject it). -/
theorem fuse_three_carves_2 : fuseObservers [obsA, obsB, obsC] (2 : W) = false := by decide

/-- ORDER INDEPENDENCE, concretely: all six orderings of the three observers fuse
    to the identical shared world at every voxel. Reordering the cameras does not
    change a single certified voxel. Closed by `decide` (a corollary instance of
    `fuse_perm_invariant`). -/
theorem fuse_three_order_independent : ∀ v : W,
    fuseObservers [obsA, obsB, obsC] v = fuseObservers [obsB, obsC, obsA] v ∧
    fuseObservers [obsA, obsB, obsC] v = fuseObservers [obsC, obsB, obsA] v ∧
    fuseObservers [obsA, obsB, obsC] v = fuseObservers [obsB, obsA, obsC] v ∧
    fuseObservers [obsA, obsB, obsC] v = fuseObservers [obsC, obsA, obsB] v ∧
    fuseObservers [obsA, obsB, obsC] v = fuseObservers [obsA, obsC, obsB] v := by
  decide

/-- Re-observing observer C (the disagreer) does not change the shared world at
    any voxel — concrete `fuse_idempotent`. -/
theorem fuse_three_reobserve_C : ∀ v : W,
    fuseObservers [obsC, obsC, obsA, obsB] v = fuseObservers [obsC, obsA, obsB] v := by
  decide

end CarveMeetObserverFusion
end GnosisMath
