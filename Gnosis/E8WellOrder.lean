/-
  E8WellOrder
  ===========

  The canonical well-order on the 240 E_8 roots that makes the
  Hope-Jar discharge deterministic and replayable.  This fills the
  `WellOrder` gap in gnosis-math: prior to this file the project had
  no ordinal / total-order certificate, only Nat-indexed lists.

  Design — order by a positional code
  -----------------------------------
  Each root has entries in {−2, −1, 0, 1, 2}.  Shifting by +4 puts
  them in {2, …, 6} ⊂ [0, 8), so reading the length-8 vector as an
  8-digit base-8 number gives an injective `code : root → Nat`.

  Ordering roots by `code` then inherits the hard properties for
  free from `Nat`:

      transitivity  ←  Nat.lt_trans          (general, not brute-forced)
      totality      ←  Nat.lt_trichotomy
      irreflexivity ←  Nat.lt_irrefl

  and the only fact that needs the concrete root set is that the
  codes are pairwise distinct (`codes_nodup`), which upgrades the
  Nat pre-order to a strict linear order on the 240 roots.  Distinct
  roots + a count of 240 (from `E8Lattice.e8_root_count`) is exactly
  the bijection with `Fin 240` — the deterministic discharge index.

  Relation to the coset tower
  ---------------------------
  This well-order ranks the 240 roots (the top coset E8/E7, one Weyl
  orbit).  The full 696729600-key discharge walk composes THIS order
  on lanes with the recursive coset-tower walk 240·56·27·16·120 over
  the Weyl group (see `E8Lattice.cosetTower`; the order proof of the
  whole tower is staged in `E8WeylOrder.lean`).  The recursion is
  what gives the `.rknot` its self-similar block layout — one
  pointer-table block per tower level.

  No axioms beyond `native_decide`'s; no sorry.
-/

import Gnosis.E8Lattice

namespace E8WellOrder

open E8Lattice

-- ══════════════════════════════════════════════════════════
-- POSITIONAL CODE  (injective root → Nat)
-- ══════════════════════════════════════════════════════════

/-- Read a length-8 root (entries in [−2,2]) as an 8-digit base-8
    number after shifting each digit into [2,6] ⊂ [0,8). -/
def code (v : List Int) : Nat :=
  v.foldl (fun acc x => acc * 8 + (x + 4).toNat) 0

/-- The codes of the 240 roots are pairwise distinct: `code` is
    injective on the root set, so it linearises them faithfully. -/
theorem codes_nodup : (e8Roots.map code).Nodup := by native_decide

/-- The roots themselves are pairwise distinct — the foundation of
    the `Fin 240` indexing. -/
theorem e8_roots_nodup : e8Roots.Nodup := by native_decide

-- ══════════════════════════════════════════════════════════
-- THE CANONICAL STRICT ORDER
-- ══════════════════════════════════════════════════════════

/-- Canonical strict order on roots: by ascending code. -/
def rootLt (a b : List Int) : Prop := code a < code b

instance : DecidableRel rootLt :=
  fun a b => inferInstanceAs (Decidable (code a < code b))

/-- Boolean form for finite enumeration. -/
def rootLtB (a b : List Int) : Bool := decide (code a < code b)

/-- Transitivity — inherited from `Nat`, fully general (no brute
    force over the 240³ triples). -/
theorem rootLt_trans {a b c : List Int}
    (h1 : rootLt a b) (h2 : rootLt b c) : rootLt a c :=
  Nat.lt_trans h1 h2

/-- Irreflexivity — inherited from `Nat`. -/
theorem rootLt_irrefl (a : List Int) : ¬ rootLt a a :=
  Nat.lt_irrefl (code a)

/-- Trichotomy on the root set: for any two roots, either they are
    equal or exactly one precedes the other.  Distinctness of codes
    makes the equal case coincide with equal codes. -/
theorem rootLt_trichotomy :
    e8Roots.all (fun a => e8Roots.all (fun b =>
      (a == b) || rootLtB a b || rootLtB b a)) = true := by native_decide

/-- Antisymmetry on the root set: no two roots each precede the
    other. -/
theorem rootLt_antisymm :
    e8Roots.all (fun a => e8Roots.all (fun b =>
      !(rootLtB a b && rootLtB b a))) = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- THE Fin 240 DISCHARGE BIJECTION
-- ══════════════════════════════════════════════════════════

/-- The discharge sequence: the 240 roots are distinct keys indexed
    by `Fin 240`.  Distinctness + the count of 240 is the bijection
    `Fin 240 ↔ roots` that makes the Hope-Jar lane walk a
    permutation with no collisions. -/
theorem fin240_bijection :
    e8Roots.length = 240 ∧ e8Roots.Nodup :=
  ⟨E8Lattice.e8_root_count, e8_roots_nodup⟩

/-- Index a lane by its position in the canonical list.  With
    `e8_roots_nodup` (no duplicates) this map is injective, so it is
    a genuine bijection from `Fin 240` onto the roots: the Hope-Jar
    lane walk is a collision-free permutation. -/
def laneRoot (i : Fin e8Roots.length) : List Int := e8Roots.get i

/-- The canonical lane codes are pairwise distinct — the concrete,
    `native_decide`-checked witness that `laneRoot` collides nowhere
    (this is `codes_nodup` re-stated as the lane-injectivity fact the
    runtime depends on). -/
theorem lane_codes_distinct : (e8Roots.map code).Nodup := codes_nodup

/-- Every code is bounded by 8^8, so the discharge index fits in a
    u32 lane id — the rknot wire constraint. -/
theorem code_bounded :
    e8Roots.all (fun v => decide (code v < 8 ^ 8)) = true := by native_decide

end E8WellOrder
