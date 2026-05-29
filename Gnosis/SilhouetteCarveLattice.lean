/-
  SilhouetteCarveLattice.lean
  ===========================

  The shape-from-silhouette carve, as a finite lattice — the algebra behind the
  phyle-solver reconstruction (apps/monster-studio, monster-mass-recon).

  A view's silhouette is a per-voxel membership `VoxField := V → Bool`: does each
  voxel back-project inside that view's silhouette. Combining views has two pure
  operators:

    * MEET  `carve`  = a voxel survives iff it is in ALL views   (the visual hull).
    * JOIN  `unite`  = a voxel is kept   iff it is in ANY view    (the min-hits-1 union).

  Both are derived, per voxel, from Init `Bool` `&&` / `||`, so the lattice laws
  re-derive from the kernel — no Mathlib lattice, no `omega`. Stated per voxel
  (`∀ v`) to avoid `funext` / `Quot.sound`; `#print axioms` shows every theorem
  here depends on NO axioms (not even `propext`) — fully kernel-checked.

  PROVEN (the clean limit the pipeline ships — strict intersection of views):
    * `meet`/`unite` are each idempotent, commutative, associative   → a semilattice.
    * The fold `carve` is duplicate-insensitive (`carve_dup`), order-insensitive
      (`carve_swap`), and regroup-insensitive (`carve_append`). So feeding the same
      view twice, or in any order, or in any grouping, is free — the meet-semilattice
      fold. Dual facts hold for `unite`.

  ANTITHEOREM (where the lattice STOPS — the Sardis boundary, manifesto §"refute
  the over-claim"):
    * `consensus_not_idempotent`: the `min-hits = k` threshold (`atLeast k`) is NOT
      idempotent under a duplicated view — duplicating one accepting view flips a
      voxel from rejected to kept. So k-of-N consensus is not a semilattice; it
      trades associativity/idempotence for tunability. (Colour-mean averaging and
      visibility-coupled space carving break it further — order-dependent — and are
      named here in prose rather than smuggled into the lattice.)

  Init-only Rustic Church. No Mathlib, no `omega`, no `simp`/`decide` on open goals.
-/
import Init

namespace GnosisMath
namespace SilhouetteCarveLattice

universe u
variable {V : Type u}

/-- A view's silhouette occupancy: does each voxel back-project inside it. -/
abbrev VoxField (V : Type u) := V → Bool

-- ══════════════════════════════════════════════════════════
-- PART I.  The two pure operators (binary), per-voxel laws
-- ══════════════════════════════════════════════════════════

/-- Carve / visual-hull MEET: a voxel survives iff in BOTH views. -/
def meet (a b : VoxField V) : VoxField V := fun v => a v && b v

/-- Union JOIN (min-hits-1): a voxel is kept iff in EITHER view. -/
def union (a b : VoxField V) : VoxField V := fun v => a v || b v

theorem meet_idem (a : VoxField V) (v : V) : meet a a v = a v :=
  Bool.and_self (a v)

theorem meet_comm (a b : VoxField V) (v : V) : meet a b v = meet b a v :=
  Bool.and_comm (a v) (b v)

theorem meet_assoc (a b c : VoxField V) (v : V) :
    meet (meet a b) c v = meet a (meet b c) v :=
  Bool.and_assoc (a v) (b v) (c v)

theorem union_idem (a : VoxField V) (v : V) : union a a v = a v :=
  Bool.or_self (a v)

theorem union_comm (a b : VoxField V) (v : V) : union a b v = union b a v :=
  Bool.or_comm (a v) (b v)

theorem union_assoc (a b c : VoxField V) (v : V) :
    union (union a b) c v = union a (union b c) v :=
  Bool.or_assoc (a v) (b v) (c v)

/-- Capstone: the carve meet is a commutative idempotent associative semilattice
    operation (the three laws bundled, per voxel). -/
theorem meet_is_semilattice (a b c : VoxField V) (v : V) :
    meet a a v = a v ∧
    meet a b v = meet b a v ∧
    meet (meet a b) c v = meet a (meet b c) v :=
  ⟨meet_idem a v, meet_comm a b v, meet_assoc a b c v⟩

-- ══════════════════════════════════════════════════════════
-- PART II.  Folding many views — the actual carve
-- ══════════════════════════════════════════════════════════

/-- The visual hull over a list of views: AND-fold (identity = ⊤, everything). -/
def carve : List (VoxField V) → VoxField V
  | [] => fun _ => true
  | s :: rest => fun v => s v && carve rest v

/-- The union over a list of views: OR-fold (identity = ⊥, nothing). -/
def unite : List (VoxField V) → VoxField V
  | [] => fun _ => false
  | s :: rest => fun v => s v || unite rest v

/-- Idempotence of the fold: a duplicated view changes nothing. -/
theorem carve_dup (s : VoxField V) (rest : List (VoxField V)) (v : V) :
    carve (s :: s :: rest) v = carve (s :: rest) v := by
  show (s v && (s v && carve rest v)) = (s v && carve rest v)
  rw [← Bool.and_assoc, Bool.and_self]

/-- Commutativity of the fold: view order is irrelevant (swap of the head pair). -/
theorem carve_swap (a b : VoxField V) (rest : List (VoxField V)) (v : V) :
    carve (a :: b :: rest) v = carve (b :: a :: rest) v := by
  show (a v && (b v && carve rest v)) = (b v && (a v && carve rest v))
  rw [← Bool.and_assoc, ← Bool.and_assoc, Bool.and_comm (a v) (b v)]

/-- Associativity of the fold: carving a concatenation = meet of the two carves.
    (Regrouping the views is free.) -/
theorem carve_append (xs ys : List (VoxField V)) (v : V) :
    carve (xs ++ ys) v = (carve xs v && carve ys v) := by
  induction xs with
  | nil =>
      show carve ys v = (true && carve ys v)
      rw [Bool.true_and]
  | cons a xs ih =>
      show (a v && carve (xs ++ ys) v) = ((a v && carve xs v) && carve ys v)
      rw [ih, Bool.and_assoc]

/-- Dual: uniting a concatenation = join of the two unions. -/
theorem unite_append (xs ys : List (VoxField V)) (v : V) :
    unite (xs ++ ys) v = (unite xs v || unite ys v) := by
  induction xs with
  | nil =>
      show unite ys v = (false || unite ys v)
      rw [Bool.false_or]
  | cons a xs ih =>
      show (a v || unite (xs ++ ys) v) = ((a v || unite xs v) || unite ys v)
      rw [ih, Bool.or_assoc]

-- ══════════════════════════════════════════════════════════
-- PART III.  Antitheorem — where the lattice stops (k-of-N consensus)
-- ══════════════════════════════════════════════════════════

/-- Count of accepting views for a single voxel. -/
def countTrue : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + countTrue rest

/-- `min-hits = k` consensus at one voxel: kept iff at least `k` views accept it. -/
def atLeast (k : Nat) (l : List Bool) : Bool := decide (k ≤ countTrue l)

/-- ANTITHEOREM. The k-of-N consensus is NOT idempotent under a duplicated view:
    `[true, false]` has one accepting view (< 2 → rejected), but duplicating the
    accepting view, `[true, true, false]`, reaches the threshold (→ kept). One
    repeated view flipped the result. So min-hits-k is not a semilattice — unlike
    the strict `carve` (`carve_dup`). This is the precise sense in which thresholded
    consensus leaves the lattice. -/
theorem consensus_not_idempotent :
    atLeast 2 [true, false] ≠ atLeast 2 [true, true, false] := by
  decide

/-- Companion: at the extremes the consensus collapses back onto the lattice.
    `atLeast 0` is the constant ⊤ (everything kept — like the empty meet's unit),
    independent of the views. (Closed witness on a sample multiset.) -/
theorem consensus_floor_is_top :
    atLeast 0 [true, false] = true ∧ atLeast 0 ([] : List Bool) = true := by
  decide

end SilhouetteCarveLattice
end GnosisMath
