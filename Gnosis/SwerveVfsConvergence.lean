/-
  SwerveVfsConvergence.lean
  =========================

  A machine-checked law behind the swerve runtime's CRDT-VFS.

  swerve (open-source/swerve) models a container rootfs as the FOLD of a
  write-only, content-addressed knot op-log. Its `root_key` (src/vfs.rs) is a
  bitwise `bitwise::PortalKey` XOR-fold over the resolved per-path state, and its
  `merge` is the union of two logs. The runtime CLAIMS two things about that:

    1. the root is an *order-invariant* content identity — two independent builds
       of the same content, or two different merge orders, converge to the SAME
       root;
    2. a duplicated contribution cancels (XOR self-inverse) — the dedup property.

  This module proves the algebra those claims rest on. The relationship is
  precise (not an identity claim): the PortalKey merge is XOR, XOR is a
  commutative monoid (per bit: `(Bool, xor, false)`), and an XOR-fold of a list
  is therefore invariant under append-order and under any permutation. The full
  PortalKey folds bitwise, so the invariance lifts coordinatewise.

  Rustic Church: no Mathlib, no `omega`, no `simp`/`decide` on open goals — only
  Init lemmas and structural induction. The Bool monoid laws are closed per
  constructor (`cases <;> rfl`); the fold laws are structural induction on the
  carrier list / on `List.Perm`.
-/

namespace SwerveVfsConvergence

-- ══════════════════════════════════════════════════════════
-- PARAMETRIC CORE — a commutative-monoid fold over a log
-- ══════════════════════════════════════════════════════════
-- A "log" is a `List α` of per-path contributions; the "root" is its right
-- fold under `op` with unit `e`. `merge` is `++`. We carry the monoid laws as
-- explicit hypotheses so the core is reusable for any width of PortalKey.

variable {α : Type}

/-- Left-commutativity from commutativity + associativity — the swap lemma. -/
theorem op_left_comm (op : α → α → α)
    (assoc : ∀ x y z, op (op x y) z = op x (op y z))
    (comm : ∀ x y, op x y = op y x)
    (x y z : α) : op x (op y z) = op y (op x z) := by
  rw [← assoc, comm x y, assoc]

/-- The root of a merge (`++`) factors through `op`: folding the concatenation
    equals `op` of the two folds. Structural induction on the first log. -/
theorem fold_append (op : α → α → α) (e : α)
    (idl : ∀ x, op e x = x)
    (assoc : ∀ x y z, op (op x y) z = op x (op y z))
    (xs ys : List α) :
    List.foldr op e (xs ++ ys)
      = op (List.foldr op e xs) (List.foldr op e ys) := by
  induction xs with
  | nil =>
      show List.foldr op e ys = op e (List.foldr op e ys)
      rw [idl]
  | cons a t ih =>
      show op a (List.foldr op e (t ++ ys))
          = op (op a (List.foldr op e t)) (List.foldr op e ys)
      rw [ih, assoc]

/-- Merge order-independence: the root of `a ++ b` equals the root of `b ++ a`.
    This is the CRDT "merge order does not matter" law. -/
theorem fold_merge_comm (op : α → α → α) (e : α)
    (idl : ∀ x, op e x = x)
    (assoc : ∀ x y z, op (op x y) z = op x (op y z))
    (comm : ∀ x y, op x y = op y x)
    (xs ys : List α) :
    List.foldr op e (xs ++ ys) = List.foldr op e (ys ++ xs) := by
  rw [fold_append op e idl assoc xs ys, fold_append op e idl assoc ys xs, comm]

/-- Merge associativity: `(a ++ b) ++ c` and `a ++ (b ++ c)` fold to the same
    root (the union is associative). -/
theorem fold_merge_assoc (op : α → α → α) (e : α)
    (xs ys zs : List α) :
    List.foldr op e ((xs ++ ys) ++ zs)
      = List.foldr op e (xs ++ (ys ++ zs)) := by
  rw [List.append_assoc]

/-- The strong statement: the root is invariant under ANY permutation of the
    log — convergent histories that reach the same multiset of contributions
    share a root. Induction on `List.Perm`. -/
theorem fold_perm (op : α → α → α) (e : α)
    (assoc : ∀ x y z, op (op x y) z = op x (op y z))
    (comm : ∀ x y, op x y = op y x)
    {xs ys : List α} (h : List.Perm xs ys) :
    List.foldr op e xs = List.foldr op e ys := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (op a) ih
  | swap a b l =>
      show op b (op a (List.foldr op e l)) = op a (op b (List.foldr op e l))
      exact op_left_comm op assoc comm b a (List.foldr op e l)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

-- ══════════════════════════════════════════════════════════
-- THE PORTALKEY BIT — concrete witness: (Bool, xor, false)
-- ══════════════════════════════════════════════════════════
-- The PortalKey merge is XOR. Per bit that is `Bool.xor`; the laws are closed
-- per constructor, so `cases <;> rfl` (no decide-on-open).

theorem bxor_comm (a b : Bool) : Bool.xor a b = Bool.xor b a := by
  cases a <;> cases b <;> rfl

theorem bxor_assoc (a b c : Bool) :
    Bool.xor (Bool.xor a b) c = Bool.xor a (Bool.xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem false_bxor (a : Bool) : Bool.xor false a = a := by
  cases a <;> rfl

theorem bxor_self (a : Bool) : Bool.xor a a = false := by
  cases a <;> rfl

/-- The per-bit PortalKey root of a log of bit-contributions: the XOR-fold. The
    full PortalKey is this folded coordinatewise across bits. -/
def portalRoot (log : List Bool) : Bool := List.foldr Bool.xor false log

-- ══════════════════════════════════════════════════════════
-- THE SWERVE LAWS (concrete corollaries)
-- ══════════════════════════════════════════════════════════

/-- swerve `merge` order-independence (per bit): the root of `a ++ b` equals the
    root of `b ++ a`. Two merge orders converge to the same PortalKey root. -/
theorem portal_root_merge_order_invariant (a b : List Bool) :
    portalRoot (a ++ b) = portalRoot (b ++ a) :=
  fold_merge_comm Bool.xor false false_bxor bxor_assoc bxor_comm a b

/-- swerve `merge` associativity (per bit). -/
theorem portal_root_merge_assoc (a b c : List Bool) :
    portalRoot ((a ++ b) ++ c) = portalRoot (a ++ (b ++ c)) :=
  fold_merge_assoc Bool.xor false a b c

/-- The order-invariant content identity (per bit): any permutation of the log
    folds to the same PortalKey root — independent builds of the same content
    converge. -/
theorem portal_root_perm_invariant {a b : List Bool} (h : List.Perm a b) :
    portalRoot a = portalRoot b :=
  fold_perm Bool.xor false bxor_assoc bxor_comm h

/-- Dedup / idempotence (per bit): a duplicated contribution cancels, because
    XOR is self-inverse. `x :: x :: rest` folds to the root of `rest`. -/
theorem portal_root_dup_cancels (x : Bool) (rest : List Bool) :
    portalRoot (x :: x :: rest) = portalRoot rest := by
  show Bool.xor x (Bool.xor x (portalRoot rest)) = portalRoot rest
  rw [← bxor_assoc, bxor_self, false_bxor]

/-- The swerve CRDT-VFS convergence law, bundled: per bit the PortalKey root is
    independent of merge order, associative under merge, invariant under any
    permutation of the log (the content-identity / dedup-hydration key), and a
    duplicated contribution cancels. These are exactly the properties
    `src/vfs.rs` relies on for `merge` to be a convergent CRDT and `root_key` to
    be an order-invariant identity. -/
theorem swerve_vfs_convergence (a b : List Bool) (x : Bool) (rest : List Bool) :
    portalRoot (a ++ b) = portalRoot (b ++ a)
    ∧ (∀ c, portalRoot ((a ++ b) ++ c) = portalRoot (a ++ (b ++ c)))
    ∧ (List.Perm a b → portalRoot a = portalRoot b)
    ∧ portalRoot (x :: x :: rest) = portalRoot rest := by
  refine ⟨portal_root_merge_order_invariant a b, ?_, ?_, portal_root_dup_cancels x rest⟩
  · intro c; exact portal_root_merge_assoc a b c
  · intro h; exact portal_root_perm_invariant h

-- ── Next exploration (B34a handoff) ───────────────────────────────────────
-- Lift the per-bit witness to the full key: model PortalKey as `List Bool`
-- (a fixed-width bitvector) with pointwise xor, prove the same four laws hold
-- coordinatewise (they follow from the Bool laws under `List.zipWith`), and
-- connect `portalRoot` to swerve's LWW `state()` so the carrier is the resolved
-- per-path winner set rather than a raw bit list. Stays Init-only: zipWith
-- recursion + the Bool lemmas above; no Mathlib, no omega.

end SwerveVfsConvergence
