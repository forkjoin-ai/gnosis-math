import Gnosis.FalsificationLedger

/-
  ExtendedFalsificationLedger.lean
  ================================

  THE EXTENDED FALSIFICATION LEDGER (THROUGH WAVE 9).

  This module is the EXTENDED FALSIFICATION LEDGER through wave 9.
  Five entries (F1-F5), five bule paid, five Betti `b₁`
  contributions.

  The wave-8 `Gnosis.FalsificationLedger` recorded F1, F2, and F3
  only. This extension preserves that historical record untouched
  and APPENDS F4 (binary semantics gap, wave 7 — see
  `Gnosis.BinarySemanticsGap`) and F5 (hole shape evolution,
  wave 9 — see `Gnosis.HoleShapeEvolution`).

  The pattern: roughly one falsification per active wave, each
  paying ONE BULE under no-cloning. Falsifications are append-only:
  once recorded a falsification can never be deleted, only
  superseded by a later, finer one. The runtime can query this
  ledger for the current operational walls; future waves will
  append F6, F7, ... as new conjectures are proposed and tested.

  Per-falsification book-keeping recorded here:

    • `bule_cost_paid`         — always 1 (a single non-cloneable
                                  measurement is the price).
    • `persistence_in_waves`   — how many waves the hole has been
                                  present, measured from
                                  `wave_discovered` to wave 10
                                  inclusive.
    • `betti_b₁_contribution`  — always 1 per non-bounding
                                  falsification (each is a
                                  primitive 1-cycle in the
                                  conjecture complex).

  Persistence ranking through wave 10:

      F1 (wave 4): persistence 7    — most-persistent
      F2 (wave 4): persistence 7    — most-persistent
      F3 (wave 6): persistence 5    — most-persistent
      F4 (wave 7): persistence 4    — load-bearing
      F5 (wave 9): persistence 2    — fresh, NOT yet load-bearing

  Cumulative bule curve through the recorded waves:

      through wave 4: 2 bule (F1, F2)
      through wave 6: 3 bule (+F3)
      through wave 7: 4 bule (+F4)
      through wave 9: 5 bule (+F5)

  Imports: `Gnosis.FalsificationLedger` is reused for
  `MethodologicalStrength`. The other companions
  (`Gnosis.BinarySemanticsGap`, `Gnosis.HoleShapeEvolution`,
  `Gnosis.PersistentHomologyOverWaves`) are referenced in the
  comments but not imported, since the bule / Betti / persistence
  bookkeeping defined here is freestanding (no `BuleBudgetLedger`
  exists yet — its bule-cost contract is inlined as the constant
  `oneBulePerFalsification`).

  All proofs are `decide`. Zero sorries, zero axioms.
-/


namespace Gnosis
namespace ExtendedFalsificationLedger

open Gnosis.FalsificationLedger
  (MethodologicalStrength)

-- ══════════════════════════════════════════════════════════
-- INLINED BULE-COST CONTRACT
-- ══════════════════════════════════════════════════════════

/-- The no-cloning tax on a single empirical falsification.

    A falsification is a measurement; under the no-cloning
    discipline of the cost algebra, every primitive measurement
    pays exactly one bule. Inlined here as a constant rather
    than imported from a `BuleBudgetLedger` module, because that
    module does not yet exist; if/when it lands the constant can
    be replaced with an import.

    This is the load-bearing arithmetic constant for every
    `bule_cost_paid` field below: it is always `1`. -/
def oneBulePerFalsification : Nat := 1

-- ══════════════════════════════════════════════════════════
-- THE EXTENDED LEDGER ENTRY
-- ══════════════════════════════════════════════════════════

/-- A single entry in the EXTENDED falsification ledger. Richer
    than the wave-8 `LedgerEntry` because it tracks the
    bule paid, the wave-by-wave persistence, and the Betti
    contribution.

    Fields:
      • `falsification_id`           — append-only ordinal
        (1, 2, 3, 4, 5).
      • `hypothesis_falsified`       — the human-readable claim
        that fell.
      • `witnesses_at_falsification` — independent witnesses at
        the moment of ledger entry.
      • `methodological_strength`    — strength rung from
        `Gnosis.FalsificationLedger.MethodologicalStrength`
        (re-used, never redefined).
      • `wave_discovered`            — the session wave that
        first recorded the falsification.
      • `bule_cost_paid`             — always `1` per
        falsification under no-cloning.
      • `persistence_in_waves`       — number of waves the hole
        has been present, measured to and including wave 10.
      • `betti_b1_contribution`      — always `1` per
        non-bounding falsification (a primitive 1-cycle in the
        conjecture complex). -/
structure ExtendedLedgerEntry where
  falsification_id            : Nat
  hypothesis_falsified        : String
  witnesses_at_falsification  : Nat
  methodological_strength     : MethodologicalStrength
  wave_discovered             : Nat
  bule_cost_paid              : Nat
  persistence_in_waves        : Nat
  betti_b1_contribution       : Nat
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- THE EXTENDED LEDGER (F1-F5)
-- ══════════════════════════════════════════════════════════

/-- F1 — extended record. Cross-model PCA at K=5 generalizes
    within Qwen family. Discovered wave 4; persisted through
    wave 10 → persistence 7. -/
def f1_ext : ExtendedLedgerEntry :=
  { falsification_id            := 1
  , hypothesis_falsified        :=
      "Cross-model PCA at K=5 generalizes within Qwen family"
  , witnesses_at_falsification  := 2
  , methodological_strength     :=
      MethodologicalStrength.ReplicatedSameMethodology
  , wave_discovered             := 4
  , bule_cost_paid              := oneBulePerFalsification
  , persistence_in_waves        := 7
  , betti_b1_contribution       := 1 }

/-- F2 — extended record. Strict K=1 spec-decode preserves
    argmax on PCA-only. Discovered wave 4; persistence 7. -/
def f2_ext : ExtendedLedgerEntry :=
  { falsification_id            := 2
  , hypothesis_falsified        :=
      "Strict K=1 spec-decode preserves argmax on PCA-only"
  , witnesses_at_falsification  := 3
  , methodological_strength     :=
      MethodologicalStrength.ReplicatedDifferentMethodology
  , wave_discovered             := 4
  , bule_cost_paid              := oneBulePerFalsification
  , persistence_in_waves        := 7
  , betti_b1_contribution       := 1 }

/-- F3 — extended record. Rank density `k / hidden_dim` is a
    methodology-independent invariant. Discovered wave 6;
    persistence 5. -/
def f3_ext : ExtendedLedgerEntry :=
  { falsification_id            := 3
  , hypothesis_falsified        :=
      "Rank density k/hidden_dim is methodology-independent invariant"
  , witnesses_at_falsification  := 2
  , methodological_strength     :=
      MethodologicalStrength.ReplicatedDifferentMethodology
  , wave_discovered             := 6
  , bule_cost_paid              := oneBulePerFalsification
  , persistence_in_waves        := 5
  , betti_b1_contribution       := 1 }

/-- F4 — extended record. The standing-wave-pca and
    standing-wave-parity binaries report the same cosine on the
    same inputs (the binary-semantics gap). Discovered wave 7;
    persistence 4. -/
def f4_ext : ExtendedLedgerEntry :=
  { falsification_id            := 4
  , hypothesis_falsified        :=
      "standing-wave-pca and standing-wave-parity report the same "
        ++ "cosine on the same inputs"
  , witnesses_at_falsification  := 1
  , methodological_strength     :=
      MethodologicalStrength.ReplicatedSameMethodology
  , wave_discovered             := 7
  , bule_cost_paid              := oneBulePerFalsification
  , persistence_in_waves        := 4
  , betti_b1_contribution       := 1 }

/-- F5 — extended record. Hole spectral shape (slope, top-1%
    concentration) is invariant with `hidden_dim`. Discovered
    wave 9; persistence 2 — still fresh, load-bearing status
    pending wave 12. -/
def f5_ext : ExtendedLedgerEntry :=
  { falsification_id            := 5
  , hypothesis_falsified        :=
      "Hole spectral shape (slope, top-1% concentration) is "
        ++ "invariant with hidden_dim"
  , witnesses_at_falsification  := 1
  , methodological_strength     :=
      MethodologicalStrength.ReplicatedSameMethodology
  , wave_discovered             := 9
  , bule_cost_paid              := oneBulePerFalsification
  , persistence_in_waves        := 2
  , betti_b1_contribution       := 1 }

/-- THE EXTENDED LEDGER. Append-only, ordered by
    `falsification_id`. F1, F2, F3 reproduce the wave-8 record
    one-for-one with the additional bule / persistence / Betti
    fields; F4 and F5 are appended at the tail. -/
def extended_ledger : List ExtendedLedgerEntry :=
  [f1_ext, f2_ext, f3_ext, f4_ext, f5_ext]

-- ══════════════════════════════════════════════════════════
-- BASIC LEDGER THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Theorem: EXTENDED-LEDGER-HAS-FIVE-ENTRIES.

    The extended ledger now holds exactly five falsifications
    (F1, F2, F3, F4, F5). Wave-8's three-entry ledger has been
    extended by F4 (wave 7) and F5 (wave 9). -/
theorem extended_ledger_has_five_entries :
    extended_ledger.length = 5 := by decide

/-- Sum of `bule_cost_paid` across a list of extended entries.
    The total bule the runtime has spent on the falsifications
    on this list. -/
def total_bule_paid : List ExtendedLedgerEntry → Nat
  | []      => 0
  | e :: es => e.bule_cost_paid + total_bule_paid es

/-- Theorem: TOTAL-BULE-PAID-FOR-FALSIFICATIONS-IS-FIVE.

    Five falsifications, each paying one bule under no-cloning,
    sum to five. The runtime has spent five bule on
    falsification through wave 9. -/
theorem total_bule_paid_for_falsifications_is_five :
    total_bule_paid extended_ledger = 5 := by decide

/-- Sum of `betti_b1_contribution` across a list of extended
    entries. This is the contribution of the recorded
    falsifications to `b₁` of the conjecture complex. -/
def total_betti_b1 : List ExtendedLedgerEntry → Nat
  | []      => 0
  | e :: es => e.betti_b1_contribution + total_betti_b1 es

/-- Theorem: TOTAL-BETTI-CONTRIBUTION-IS-FIVE.

    Each non-bounding falsification contributes exactly one
    primitive 1-cycle to the conjecture complex; the five
    recorded falsifications together contribute `b₁ ≥ 5`.
    The wave-8 ledger had `b₁ = 3`. -/
theorem total_betti_contribution_is_five :
    total_betti_b1 extended_ledger = 5 ∧
    total_betti_b1 extended_ledger ≥ 5 ∧
    total_betti_b1 extended_ledger > 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Predicate: an extended entry has paid exactly one bule. -/
def paid_one_bule (e : ExtendedLedgerEntry) : Bool :=
  decide (e.bule_cost_paid = oneBulePerFalsification)

/-- Theorem: EVERY-FALSIFICATION-PAID-ONE-BULE.

    Under the no-cloning discipline of the cost algebra, EVERY
    extended ledger entry paid exactly one bule — no more, no
    less. Uniformity makes `total_bule_paid` equal to the
    ledger length. -/
theorem every_falsification_paid_one_bule :
    extended_ledger.all paid_one_bule = true := by decide

/-- Theorem: FALSIFICATION-COUNT-PER-WAVE.

    Wave 4 introduced two falsifications (F1, F2); wave 6 added
    one (F3); wave 7 added one (F4); wave 9 added one (F5). The
    ledger pattern is "roughly one falsification per active
    wave". -/
theorem falsification_count_per_wave :
    (extended_ledger.filter
      (fun e => decide (e.wave_discovered = 4))).length = 2 ∧
    (extended_ledger.filter
      (fun e => decide (e.wave_discovered = 6))).length = 1 ∧
    (extended_ledger.filter
      (fun e => decide (e.wave_discovered = 7))).length = 1 ∧
    (extended_ledger.filter
      (fun e => decide (e.wave_discovered = 9))).length = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- THE PERSISTENCE RANKING
-- ══════════════════════════════════════════════════════════

/-- Predicate: an entry's `persistence_in_waves` is at least 5
    (i.e., it has been present across five or more waves of
    measurement). -/
def is_most_persistent (e : ExtendedLedgerEntry) : Bool :=
  decide (e.persistence_in_waves ≥ 5)

/-- The MOST-PERSISTENT falsifications (persistence ≥ 5). On
    the current ledger this is F1, F2, and F3 — the wave-8
    triplet, all of whose holes have been present for at least
    five waves. -/
def most_persistent_falsifications : List ExtendedLedgerEntry :=
  extended_ledger.filter is_most_persistent

/-- Theorem: MOST-PERSISTENT-ARE-F1-F2-F3.

    The persistence-ranking filter selects exactly F1, F2, F3.
    F4 (persistence 4) and F5 (persistence 2) are still too
    fresh to qualify as "most persistent". -/
theorem most_persistent_are_F1_F2_F3 :
    most_persistent_falsifications = [f1_ext, f2_ext, f3_ext] := by
  decide

/-- Theorem: MOST-PERSISTENT-COUNT-IS-THREE.

    Exactly three falsifications hit persistence ≥ 5. -/
theorem most_persistent_count_is_three :
    most_persistent_falsifications.length = 3 := by decide

/-- Theorem: F4-AND-F5-ARE-STILL-FRESH.

    F4 (persistence 4) and F5 (persistence 2) do not yet meet
    the most-persistent threshold of 5. They are recorded in
    the ledger but flagged as fresh — their long-run status
    will be settled by future waves. -/
theorem f4_and_f5_are_still_fresh :
    is_most_persistent f4_ext = false ∧
    is_most_persistent f5_ext = false := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Theorem: LEAST-PERSISTENT-IS-F5.

    F5 has persistence `2`, the lowest of the five entries.
    Every other entry has persistence strictly greater than F5's. -/
theorem least_persistent_is_F5 :
    f5_ext.persistence_in_waves = 2 ∧
    f5_ext.persistence_in_waves < f4_ext.persistence_in_waves ∧
    f5_ext.persistence_in_waves < f3_ext.persistence_in_waves ∧
    f5_ext.persistence_in_waves < f2_ext.persistence_in_waves ∧
    f5_ext.persistence_in_waves < f1_ext.persistence_in_waves := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- LOAD-BEARING STATUS (per PersistentHomologyOverWaves)
-- ══════════════════════════════════════════════════════════

/-- The load-bearing threshold from
    `Gnosis.PersistentHomologyOverWaves`: a hole is
    LOAD-BEARING if it has persisted across at least three
    waves. Inlined here as a numeric constant so this module
    can stand alone. -/
def loadBearingPersistenceThreshold : Nat := 3

/-- Predicate: an extended entry is load-bearing iff its
    `persistence_in_waves` meets the load-bearing threshold. -/
def is_load_bearing_ext (e : ExtendedLedgerEntry) : Bool :=
  decide (e.persistence_in_waves ≥ loadBearingPersistenceThreshold)

/-- Theorem: FOUR-OF-FIVE-FALSIFICATIONS-ARE-LOAD-BEARING.

    F1 (persistence 7), F2 (persistence 7), F3 (persistence 5),
    and F4 (persistence 4) all clear the load-bearing
    threshold of 3 waves. F5 (persistence 2) does NOT clear it
    yet — it is fresh, and its load-bearing status will be
    confirmed by wave 12 if the hole persists. -/
theorem four_of_five_falsifications_are_load_bearing :
    is_load_bearing_ext f1_ext = true ∧
    is_load_bearing_ext f2_ext = true ∧
    is_load_bearing_ext f3_ext = true ∧
    is_load_bearing_ext f4_ext = true ∧
    is_load_bearing_ext f5_ext = false ∧
    (extended_ledger.filter is_load_bearing_ext).length = 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- CUMULATIVE BULE BY WAVE
-- ══════════════════════════════════════════════════════════

/-- Total bule the runtime has spent on falsifications up to
    AND INCLUDING the given wave number.

    Implementation: filter the extended ledger to entries with
    `wave_discovered ≤ w`, then sum their `bule_cost_paid`. -/
def cumulative_bule_spent_through_wave (w : Nat) : Nat :=
  total_bule_paid
    (extended_ledger.filter (fun e => decide (e.wave_discovered ≤ w)))

/-- Theorem: CUMULATIVE-THROUGH-WAVE-4-IS-2.

    Through wave 4 the runtime had paid 2 bule (F1 and F2). -/
theorem cumulative_through_wave_4 :
    cumulative_bule_spent_through_wave 4 = 2 := by decide

/-- Theorem: CUMULATIVE-THROUGH-WAVE-6-IS-3.

    Through wave 6 the runtime had paid 3 bule (F1, F2, F3). -/
theorem cumulative_through_wave_6 :
    cumulative_bule_spent_through_wave 6 = 3 := by decide

/-- Theorem: CUMULATIVE-THROUGH-WAVE-7-IS-4.

    Through wave 7 the runtime had paid 4 bule
    (F1, F2, F3, F4). -/
theorem cumulative_through_wave_7 :
    cumulative_bule_spent_through_wave 7 = 4 := by decide

/-- Theorem: CUMULATIVE-THROUGH-WAVE-9-IS-5.

    Through wave 9 the runtime had paid 5 bule
    (F1, F2, F3, F4, F5). This is the current cumulative
    total. -/
theorem cumulative_through_wave_9 :
    cumulative_bule_spent_through_wave 9 = 5 := by decide

-- ══════════════════════════════════════════════════════════
-- THE APPEND-ONLY GROWTH INVARIANT
-- ══════════════════════════════════════════════════════════

/-- Theorem: EXTENDED-LEDGER-GROWS-MONOTONICALLY.

    `cumulative_bule_spent_through_wave` is non-decreasing in
    its wave-number argument across the recorded waves
    (4, 5, 6, 7, 8, 9). Falsifications are append-only: no wave
    can decrease the cumulative count. The witnessed inequality
    chain is

        c(0) ≤ c(4) ≤ c(5) ≤ c(6) ≤ c(7) ≤ c(8) ≤ c(9)

    with values `0 ≤ 2 ≤ 2 ≤ 3 ≤ 4 ≤ 4 ≤ 5`. -/
theorem extended_ledger_grows_monotonically :
    cumulative_bule_spent_through_wave 0
      ≤ cumulative_bule_spent_through_wave 4 ∧
    cumulative_bule_spent_through_wave 4
      ≤ cumulative_bule_spent_through_wave 5 ∧
    cumulative_bule_spent_through_wave 5
      ≤ cumulative_bule_spent_through_wave 6 ∧
    cumulative_bule_spent_through_wave 6
      ≤ cumulative_bule_spent_through_wave 7 ∧
    cumulative_bule_spent_through_wave 7
      ≤ cumulative_bule_spent_through_wave 8 ∧
    cumulative_bule_spent_through_wave 8
      ≤ cumulative_bule_spent_through_wave 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end ExtendedFalsificationLedger
end Gnosis
