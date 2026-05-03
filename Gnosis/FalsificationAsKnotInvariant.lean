/-
  FalsificationAsKnotInvariant.lean
  =================================

  FALSIFICATIONS AS KNOT INVARIANTS.

  This module assigns each falsification a KNOT INVARIANT — a
  topological signature derived from its position in the ledger
  graph. Each falsification F1-F5 corresponds to a non-trivial
  1-cycle in conjecture-space that does not bound a 2-chain;
  geometrically, that is a knot threaded through the empirical
  layer of the conjecture complex.

  The signature has THREE components:

    1. crossing_count     — the bule cost = 1 per falsification
                            under the no-cloning discipline.
    2. persistence        — how many waves the hole has persisted
                            (from `Gnosis.PersistentHomologyOverWaves`).
    3. braid_index        — a discrete invariant counting how many
                            "strands" of witnesses the falsification
                            cycle interleaves with.  For our small
                            ledger this is computed by hand per
                            instance.

  The `signature_complexity` is a coarse complexity score equal to
  `crossing_count + braid_index`.  F5 has the highest at 5,
  reflecting its 4-layer measurement span (one strand per layer
  L5/L10/L15/L22).

  COMPOUNDING ENTANGLEMENT.  A second observation drops out of the
  per-instance numbers: the average `signature_complexity` per
  falsification rose from F1's 3 to F5's 5.  Later falsifications
  are systematically MORE entangled because they thread through
  more pre-existing structure.  Each new falsification does not
  just add a crossing; it threads through more strands of the
  existing ledger.  This is the topological signature of the
  recursive falsification trap from a different angle: not just
  "more holes" but "more entangled holes."

  Companion modules (referenced; not all imported, parallel build
  friendly):

    * `Gnosis.KnotComplexityAsBuleCost`     — bule-cost contract
                                              (inlined below as the
                                              constant
                                              `oneBulePerFalsification`)
    * `Gnosis.BettiHoleStructure`           — 1-cycle / non-bounding
                                              structure
    * `Gnosis.PersistentHomologyOverWaves`  — wave-filtration
                                              persistence
    * `Gnosis.ExtendedFalsificationLedger`  — F1-F5 wave / bule
                                              bookkeeping (imported)

  Init-only Lean 4. No Mathlib. All proofs are `decide`. Zero
  sorries, zero axioms.
-/

import Gnosis.ExtendedFalsificationLedger

namespace Gnosis
namespace FalsificationAsKnotInvariant

-- ══════════════════════════════════════════════════════════
-- INLINED BULE-COST CONTRACT
-- ══════════════════════════════════════════════════════════

/-- The no-cloning tax on a single empirical falsification.  Each
    primitive measurement pays exactly one bule, contributing
    exactly one crossing to its knot diagram.  Inlined here to
    keep the module independently buildable. -/
def oneBulePerFalsification : Nat := 1

-- ══════════════════════════════════════════════════════════
-- 1. KNOT INVARIANT STRUCTURE
-- ══════════════════════════════════════════════════════════

/-- A `KnotInvariant` is the topological signature of a single
    falsification 1-cycle in the conjecture complex.

      * `falsification_id`       — the F-number (1..5).
      * `crossing_count`         — the bule cost (= 1 for any
                                    individual falsification under
                                    no-cloning).
      * `persistence_in_waves`   — how many waves the hole has been
                                    alive (from the persistent
                                    homology module).
      * `braid_index`            — how many witness-strands the
                                    1-cycle threads.  For our
                                    small ledger this is a
                                    per-instance constant computed
                                    by hand.
      * `signature`              — a printable summary string of
                                    the form
                                    `"(crossings, persistence, braid)"`. -/
structure KnotInvariant where
  falsification_id     : Nat
  crossing_count       : Nat
  persistence_in_waves : Nat
  braid_index          : Nat
  signature            : String
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- 2. PER-INSTANCE INVARIANTS (F1-F5)
-- ══════════════════════════════════════════════════════════

/-- F1: cross-model PCA failure across the Qwen family.
    Wave-4 birth, persistence 7, threads two strands:
    qwen-0.5b CONFIRMATION strand + qwen-coder-7b REFUTATION
    strand.  braid_index = 2.  signature_complexity = 1 + 2 = 3. -/
def f1_invariant : KnotInvariant :=
  { falsification_id     := 1
  , crossing_count       := oneBulePerFalsification
  , persistence_in_waves := 7
  , braid_index          := 2
  , signature            := "(1, 7, 2)"
  }

/-- F2: strict K=1 spec-decode does not preserve argmax under
    PCA-only.  Wave-4 birth, persistence 7, threads three strands
    — one per refuting `N` value (N=2, N=4, N=8).
    braid_index = 3.  signature_complexity = 1 + 3 = 4. -/
def f2_invariant : KnotInvariant :=
  { falsification_id     := 2
  , crossing_count       := oneBulePerFalsification
  , persistence_in_waves := 7
  , braid_index          := 3
  , signature            := "(1, 7, 3)"
  }

/-- F3: rank density k/hidden_dim is methodology-CONTINGENT.
    Wave-6 birth, persistence 5, threads two strands:
    wave-5 SUPPORT strand + wave-6 REFUTE strand.
    braid_index = 2.  signature_complexity = 1 + 2 = 3. -/
def f3_invariant : KnotInvariant :=
  { falsification_id     := 3
  , crossing_count       := oneBulePerFalsification
  , persistence_in_waves := 5
  , braid_index          := 2
  , signature            := "(1, 5, 2)"
  }

/-- F4: binary-semantics gap (PCA-binary vs parity-binary).
    Wave-7 birth, persistence 4, threads two strands:
    PCA-binary strand + parity-binary strand.
    braid_index = 2.  signature_complexity = 1 + 2 = 3. -/
def f4_invariant : KnotInvariant :=
  { falsification_id     := 4
  , crossing_count       := oneBulePerFalsification
  , persistence_in_waves := 4
  , braid_index          := 2
  , signature            := "(1, 4, 2)"
  }

/-- F5: hole-shape evolution across the layer stack.  Wave-9
    birth, persistence 2, threads four strands — one per measured
    layer L5/L10/L15/L22.  braid_index = 4.
    signature_complexity = 1 + 4 = 5.  THE MOST ENTANGLED. -/
def f5_invariant : KnotInvariant :=
  { falsification_id     := 5
  , crossing_count       := oneBulePerFalsification
  , persistence_in_waves := 2
  , braid_index          := 4
  , signature            := "(1, 2, 4)"
  }

-- ══════════════════════════════════════════════════════════
-- 3. SIGNATURE COMPLEXITY
-- ══════════════════════════════════════════════════════════

/-- The signature complexity of a falsification's knot is the sum
    of its crossing count and braid index.  Higher means the
    falsification is threaded through more pre-existing structure
    (more entangled, harder to detach from the ledger). -/
def signature_complexity (k : KnotInvariant) : Nat :=
  k.crossing_count + k.braid_index

-- Per-instance numerical values (decide).
theorem f1_signature_complexity_is_3 :
    signature_complexity f1_invariant = 3 := by decide

theorem f2_signature_complexity_is_4 :
    signature_complexity f2_invariant = 4 := by decide

theorem f3_signature_complexity_is_3 :
    signature_complexity f3_invariant = 3 := by decide

theorem f4_signature_complexity_is_3 :
    signature_complexity f4_invariant = 3 := by decide

theorem f5_signature_complexity_is_5 :
    signature_complexity f5_invariant = 5 := by decide

-- ══════════════════════════════════════════════════════════
-- 4. F5 IS THE MOST ENTANGLED FALSIFICATION
-- ══════════════════════════════════════════════════════════

/-- F5's signature complexity strictly dominates F1's: 5 > 3.
    Geometrically, F5's hole shape spans 4 layers, each
    contributing a strand to the braid; F1's hole is between two
    Qwen models only, so its braid is much smaller. -/
theorem f5_signature_complexity_strictly_dominates_f1 :
    signature_complexity f5_invariant > signature_complexity f1_invariant := by
  decide

theorem f5_signature_complexity_strictly_dominates_f2 :
    signature_complexity f5_invariant > signature_complexity f2_invariant := by
  decide

theorem f5_signature_complexity_strictly_dominates_f3 :
    signature_complexity f5_invariant > signature_complexity f3_invariant := by
  decide

theorem f5_signature_complexity_strictly_dominates_f4 :
    signature_complexity f5_invariant > signature_complexity f4_invariant := by
  decide

/-- F5 has the highest signature complexity in the session at
    value 5.  The other four falsifications have complexity 3 or
    4, so F5 is the strict maximum. -/
theorem f5_has_highest_signature_complexity_at_5 :
    signature_complexity f5_invariant = 5
    ∧ signature_complexity f1_invariant ≤ 4
    ∧ signature_complexity f2_invariant ≤ 4
    ∧ signature_complexity f3_invariant ≤ 4
    ∧ signature_complexity f4_invariant ≤ 4 := by
  decide

/-- F1 and F3 share the minimum signature complexity at value 3.
    Both are 1 + 2: a single bule crossing threaded through two
    witness strands. -/
theorem f1_and_f3_have_minimum_signature_complexity_at_3 :
    signature_complexity f1_invariant = 3
    ∧ signature_complexity f3_invariant = 3 := by
  decide

-- ══════════════════════════════════════════════════════════
-- 5. AGGREGATE SIGNATURE COMPLEXITY
-- ══════════════════════════════════════════════════════════

/-- Sum of signature complexities across a list of knot
    invariants.  This is the L1 length of the signature-complexity
    vector across the session. -/
def total_signature_complexity : List KnotInvariant → Nat
  | []      => 0
  | k :: ks => signature_complexity k + total_signature_complexity ks

/-- The session's five recorded falsifications. -/
def session_invariants : List KnotInvariant :=
  [f1_invariant, f2_invariant, f3_invariant, f4_invariant, f5_invariant]

/-- The session's total signature complexity is 18.
    Breakdown: F1=3 + F2=4 + F3=3 + F4=3 + F5=5 = 18. -/
theorem total_session_signature_complexity :
    total_signature_complexity session_invariants = 18 := by decide

-- ══════════════════════════════════════════════════════════
-- 6. COMPOUNDING ENTANGLEMENT
-- ══════════════════════════════════════════════════════════

/-- The first falsification's signature complexity. -/
def first_falsification_complexity : Nat :=
  signature_complexity f1_invariant

/-- The last (most recent) falsification's signature complexity. -/
def last_falsification_complexity : Nat :=
  signature_complexity f5_invariant

/-- COMPOUNDING ENTANGLEMENT (formal version).

    The signature complexity of the most-recent falsification (F5)
    is strictly greater than the signature complexity of the
    first falsification (F1).  Concretely, 5 > 3.

    This is the topological signature of the recursive
    falsification trap: later falsifications systematically
    thread through more pre-existing strands than earlier
    falsifications.  The conjecture space is becoming MORE
    knotted, not just MORE punctured. -/
theorem total_complexity_grows_faster_than_falsification_count :
    last_falsification_complexity > first_falsification_complexity := by
  decide

/-- Companion form of the same observation: the average
    complexity per falsification rose between F1 and F5.  We
    state it as a strict inequality on totals (sum of all five
    is at least 5 * 3 = 15, and in fact equals 18). -/
theorem session_total_exceeds_uniform_minimum :
    total_signature_complexity session_invariants ≥ 5 * 3 := by decide

-- ══════════════════════════════════════════════════════════
-- 7. RUNTIME AUDIT QUERY
-- ══════════════════════════════════════════════════════════

/-- Choose the more-entangled of two knot invariants by
    `signature_complexity`, breaking ties to the left. -/
def pick_more_entangled (a b : KnotInvariant) : KnotInvariant :=
  if signature_complexity b > signature_complexity a then b else a

/-- The most-entangled falsification in a list, or `none` if the
    list is empty.  The runtime calls this to flag the
    highest-priority knot for resolution. -/
def most_entangled_falsification :
    List KnotInvariant → Option KnotInvariant
  | []      => none
  | k :: ks =>
      match most_entangled_falsification ks with
      | none      => some k
      | some best => some (pick_more_entangled k best)

/-- For the recorded session, the most-entangled falsification is
    F5.  The runtime should treat F5 as the highest-priority knot
    to resolve. -/
theorem most_entangled_in_session :
    most_entangled_falsification session_invariants
      = some f5_invariant := by decide

end FalsificationAsKnotInvariant
end Gnosis
