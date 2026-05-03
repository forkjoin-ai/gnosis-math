/-
  FalsificationLedger.lean
  ========================

  THE FALSIFICATION LEDGER.

  Companion to `AntiTheory.lean`. Where `AntiTheory` carries the LIVE
  conjectures-with-falsifying-experiments, this module carries the
  DEAD ones — the append-only, rank-ordered record of hypotheses that
  have actually been falsified by measurement.

  The ledger is APPEND-ONLY and RANK-ORDERED by methodological
  strength. It is the durable scientific record. Conjectures live
  elsewhere; falsifications live here. The Theory's empirical content
  IS this ledger plus the list of yet-unfalsified conjectures with
  their falsifying experiments.

  Three falsifications recorded so far:
    F1 (wave 4) — "Cross-model PCA at K=5 generalizes within Qwen
                   family" (2 witnesses, ReplicatedSameMethodology)
    F2 (wave 4) — "Strict K=1 spec-decode preserves argmax on
                   PCA-only" (3 witnesses,
                   ReplicatedDifferentMethodology)
    F3 (wave 6) — "Rank density k/hidden_dim is methodology-
                   independent invariant" (2 witnesses,
                   ReplicatedDifferentMethodology)

  F1 is NOT yet durable: it carries only `ReplicatedSameMethodology`
  strength. Wave 7's methodology reconciliation will either upgrade
  F1 to durable (the cross-model failure is real under any
  methodology) or contest it (the failure is a methodology artifact).
  The conjecture `wave_7_methodology_reconciliation_will_resolve_f1`
  is recorded as commented intent below; it is a future commitment,
  not a proved theorem.

  All proofs are `decide`. Zero sorries, zero axioms.

  Imports: parallel to `Gnosis.AntiTheory` — the parallel module
  defines `EmpiricalClaimStatus` and `FalsifyingExperiment`. To keep
  this module buildable independently while the AntiTheory work is in
  flight, the two relevant types are defined inline here under the
  `Gnosis.FalsificationLedger.AntiTheoryShim` namespace. If/when
  `Gnosis.AntiTheory` lands, the shim can be deleted in favor of an
  `import Gnosis.AntiTheory`; the shape of the definitions matches
  the AntiTheory contract.
-/

namespace Gnosis
namespace FalsificationLedger

-- ══════════════════════════════════════════════════════════
-- ANTI-THEORY SHIM
-- ══════════════════════════════════════════════════════════

-- Inline mirror of the two types `Gnosis.AntiTheory` is expected
-- to export. Kept narrow so that swapping in
-- `import Gnosis.AntiTheory` later is a one-line change.
namespace AntiTheoryShim

/-- The status of an empirical claim under the anti-theory
    bookkeeping. A claim is either still live (`Conjectured`),
    refuted by measurement (`Falsified`), or upheld under all probes
    so far (`Corroborated`). The ledger only ever stores `Falsified`
    claims. -/
inductive EmpiricalClaimStatus where
  | Conjectured
  | Falsified
  | Corroborated
  deriving Repr, DecidableEq

/-- An experiment whose negative result would falsify a given
    conjecture. The string fields are intentionally human-readable —
    the ledger entry carries the same hypothesis text. -/
structure FalsifyingExperiment where
  hypothesis    : String
  experiment    : String
  deriving Repr, DecidableEq

end AntiTheoryShim

open AntiTheoryShim

-- ══════════════════════════════════════════════════════════
-- METHODOLOGICAL STRENGTH
-- ══════════════════════════════════════════════════════════

/-- The strength of the methodological evidence behind a
    falsification entry. Ordered from weakest to strongest:

    • `SingleMeasurement` — one run; the failure may be noise. Not
      yet durable.
    • `ReplicatedSameMethodology` — multiple runs of the same probe
      reproduce the failure. Stronger than a single run, but the
      probe itself could be biased. Still not durable.
    • `ReplicatedDifferentMethodology` — multiple runs across
      DIFFERENT probes reproduce the failure. The failure is robust
      to probe choice. DURABLE.
    • `CrossWitnessTriangulated` — three or more independent
      witnesses (probes / labs / models) reproduce the failure.
      DURABLE and triangulated. -/
inductive MethodologicalStrength where
  | SingleMeasurement
  | ReplicatedSameMethodology
  | ReplicatedDifferentMethodology
  | CrossWitnessTriangulated
  deriving Repr, DecidableEq

/-- Ordinal rank of a methodological strength, for `≥` comparisons
    used by `all_ledger_entries_have_replication`. -/
def MethodologicalStrength.rank : MethodologicalStrength → Nat
  | .SingleMeasurement              => 0
  | .ReplicatedSameMethodology      => 1
  | .ReplicatedDifferentMethodology => 2
  | .CrossWitnessTriangulated       => 3

-- ══════════════════════════════════════════════════════════
-- LEDGER ENTRY
-- ══════════════════════════════════════════════════════════

/-- A single falsification, durably recorded.

    Fields:
      • `falsification_id` — append-only ordinal (1, 2, 3, ...)
        assigned in the order the falsification was discovered.
      • `hypothesis_falsified` — the human-readable claim that fell.
      • `witnesses_at_falsification` — how many independent
        witnesses had reproduced the failure at the moment of
        ledger entry.
      • `methodological_strength` — the strength rung the entry
        currently sits on. May upgrade in later waves; never
        downgrades, never disappears.
      • `wave_discovered` — the session wave that first recorded
        the falsification. -/
structure LedgerEntry where
  falsification_id            : Nat
  hypothesis_falsified        : String
  witnesses_at_falsification  : Nat
  methodological_strength     : MethodologicalStrength
  wave_discovered             : Nat
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- THE LEDGER
-- ══════════════════════════════════════════════════════════

/-- F1: Cross-model PCA at K=5 generalizes within Qwen family.
    Falsified in wave 4. Two witnesses confirmed; same probe
    methodology across both. NOT yet durable — wave 7 will pin
    methodology and either upgrade or contest. -/
def f1 : LedgerEntry :=
  { falsification_id            := 1
  , hypothesis_falsified        :=
      "Cross-model PCA at K=5 generalizes within Qwen family"
  , witnesses_at_falsification  := 2
  , methodological_strength     :=
      MethodologicalStrength.ReplicatedSameMethodology
  , wave_discovered             := 4 }

/-- F2: Strict K=1 spec-decode preserves argmax on PCA-only.
    Falsified in wave 4. Three witnesses across three different N
    values — each N counts as a different probe for this hypothesis.
    DURABLE. -/
def f2 : LedgerEntry :=
  { falsification_id            := 2
  , hypothesis_falsified        :=
      "Strict K=1 spec-decode preserves argmax on PCA-only"
  , witnesses_at_falsification  := 3
  , methodological_strength     :=
      MethodologicalStrength.ReplicatedDifferentMethodology
  , wave_discovered             := 4 }

/-- F3: Rank density k/hidden_dim is methodology-independent
    invariant. Falsified in wave 6 by the wave-5/wave-6 disagreement
    on Qwen2.5-0.5B L13. Two witnesses (wave-5 reading vs wave-6
    reading) using different probes. DURABLE. -/
def f3 : LedgerEntry :=
  { falsification_id            := 3
  , hypothesis_falsified        :=
      "Rank density k/hidden_dim is methodology-independent invariant"
  , witnesses_at_falsification  := 2
  , methodological_strength     :=
      MethodologicalStrength.ReplicatedDifferentMethodology
  , wave_discovered             := 6 }

/-- THE LEDGER. Append-only, ordered by `falsification_id` (which
    is also discovery order). New falsifications are added at the
    tail; existing entries never move and never disappear. -/
def ledger : List LedgerEntry := [f1, f2, f3]

-- ══════════════════════════════════════════════════════════
-- BASIC LEDGER THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Theorem: LEDGER-HAS-THREE-ENTRIES.

    The current ledger holds exactly three falsifications. -/
theorem ledger_has_three_entries : ledger.length = 3 := by decide

/-- Theorem: LEDGER-FIRST-ENTRY-IS-CROSS-MODEL-PCA.

    F1 — the cross-model PCA generalization claim — is the head of
    the ledger. Append-only ordering preserves this. -/
theorem ledger_first_entry_is_cross_model_pca :
    (ledger.head?).map (fun e => e.hypothesis_falsified) =
      some "Cross-model PCA at K=5 generalizes within Qwen family" := by
  decide

/-- Predicate: an entry has at least `ReplicatedSameMethodology`
    strength (rank ≥ 1). -/
def hasReplication (e : LedgerEntry) : Bool :=
  decide (e.methodological_strength.rank ≥ 1)

/-- Theorem: ALL-LEDGER-ENTRIES-HAVE-REPLICATION.

    Every entry on the ledger is at least
    `ReplicatedSameMethodology` strong. The ledger does not record
    single-measurement noise; entries are promoted in only after
    at least one replication. -/
theorem all_ledger_entries_have_replication :
    ledger.all hasReplication = true := by decide

/-- Theorem: WAVE-4-CONTRIBUTED-TWO-FALSIFICATIONS.

    Wave 4 added F1 and F2 to the ledger. -/
theorem wave_4_contributed_two_falsifications :
    (ledger.filter (fun e => decide (e.wave_discovered = 4))).length = 2 := by
  decide

/-- Theorem: WAVE-6-CONTRIBUTED-ONE-FALSIFICATION.

    Wave 6 added F3 to the ledger. -/
theorem wave_6_contributed_one_falsification :
    (ledger.filter (fun e => decide (e.wave_discovered = 6))).length = 1 := by
  decide

-- ══════════════════════════════════════════════════════════
-- DURABILITY
-- ══════════════════════════════════════════════════════════

/-- A falsification is DURABLE iff its methodological strength is
    `ReplicatedDifferentMethodology` or `CrossWitnessTriangulated`.
    Single measurements and same-methodology replications are not
    yet durable; they may be revised by a future wave that pins the
    methodology. -/
def is_durable (e : LedgerEntry) : Bool :=
  match e.methodological_strength with
  | .ReplicatedDifferentMethodology => true
  | .CrossWitnessTriangulated       => true
  | _                               => false

/-- Theorem: F1-IS-NOT-DURABLE-YET.

    F1 sits at `ReplicatedSameMethodology`. Two witnesses, same
    probe — robust enough to enter the ledger, not yet robust
    enough to be durable. Wave 7's methodology reconciliation will
    either upgrade or contest it. -/
theorem f1_is_NOT_durable_yet : is_durable f1 = false := by decide

/-- Theorem: F2-IS-DURABLE.

    F2 carries `ReplicatedDifferentMethodology` because the three
    witnesses come from three different N values; each N is treated
    as a different probe for this hypothesis. -/
theorem f2_is_durable : is_durable f2 = true := by decide

/-- Theorem: F3-IS-DURABLE.

    F3 was witnessed across the wave-5 and wave-6 measurement
    protocols — two genuinely different probes. Durable. -/
theorem f3_is_durable : is_durable f3 = true := by decide

-- ══════════════════════════════════════════════════════════
-- THE APPEND-ONLY INVARIANT
-- ══════════════════════════════════════════════════════════

/-- The state of the ledger immediately before any wave-4 entries
    were added. Empty by historical record — F1 and F2 are the
    first ledger entries. -/
def ledger_before_wave_4 : List LedgerEntry := []

/-- The state of the ledger after wave 4 closed: F1 and F2 added,
    in that order. -/
def ledger_after_wave_4 : List LedgerEntry := [f1, f2]

/-- The state of the ledger after wave 6 closed: F3 appended at the
    tail. Equal to the current `ledger`. -/
def ledger_after_wave_6 : List LedgerEntry := [f1, f2, f3]

/-- Theorem: LEDGER-IS-MONOTONICALLY-GROWING.

    Across the recorded waves, ledger length only increases:
      • before wave 4: 0 entries
      • after  wave 4: 2 entries (F1, F2 added)
      • after  wave 6: 3 entries (F3 added)
    No wave removes an entry. The current `ledger` equals
    `ledger_after_wave_6`. -/
theorem ledger_is_monotonically_growing :
    ledger_before_wave_4.length = 0 ∧
    ledger_after_wave_4.length  = 2 ∧
    ledger_after_wave_6.length  = 3 ∧
    ledger_before_wave_4.length ≤ ledger_after_wave_4.length ∧
    ledger_after_wave_4.length  ≤ ledger_after_wave_6.length ∧
    ledger = ledger_after_wave_6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- THE WAVE-7 RECONCILIATION CONJECTURE
-- ══════════════════════════════════════════════════════════

/-
  CONJECTURE (NOT a theorem):
    `wave_7_methodology_reconciliation_will_resolve_f1`

  Once wave 7 pins the measurement protocol for the cross-model PCA
  generalization claim, F1 will admit one of two terminal verdicts:

    (a) UPGRADE TO DURABLE — the cross-model failure is real under
        any reasonable methodology. F1's strength rung is promoted
        from `ReplicatedSameMethodology` to at least
        `ReplicatedDifferentMethodology`. F1 stays on the ledger,
        with strength bumped.

    (b) CONTEST — the failure is a methodology artifact. F1 is not
        removed (the ledger is append-only) but a companion
        `LedgerEntry` is appended noting the contest, and a new
        wave-7 falsifying experiment is added against the
        methodology rather than the claim.

  Either way the ledger only grows; F1 is never deleted. This
  conjecture is RECORDED, not proved — its proof is a wave-7+
  empirical commitment.
-/

-- ══════════════════════════════════════════════════════════
-- LEDGER SUMMARY QUERY
-- ══════════════════════════════════════════════════════════

/-- A lightweight aggregate over the ledger:
      • `total_entries`   — total length of the ledger.
      • `durable_entries` — count of entries with `is_durable = true`.
      • `pending_entries` — count of entries still awaiting
        methodology reconciliation. -/
structure LedgerSummary where
  total_entries   : Nat
  durable_entries : Nat
  pending_entries : Nat
  deriving Repr, DecidableEq

/-- The summary of a ledger: count totals, durable entries, and
    pending entries by walking the list once. -/
def ledger_summary (es : List LedgerEntry) : LedgerSummary :=
  let total   := es.length
  let durable := (es.filter is_durable).length
  let pending := total - durable
  { total_entries := total
  , durable_entries := durable
  , pending_entries := pending }

/-- The summary of the ledger AS IT STANDS now: 3 entries total,
    2 durable (F2, F3), 1 pending (F1). -/
def current_summary : LedgerSummary :=
  { total_entries   := 3
  , durable_entries := 2
  , pending_entries := 1 }

/-- Theorem: CURRENT-SUMMARY-MATCHES-LEDGER.

    The recorded `current_summary` agrees with what
    `ledger_summary` computes from the live ledger. -/
theorem current_summary_matches_ledger :
    ledger_summary ledger = current_summary := by decide

/-- Theorem: PENDING-PLUS-DURABLE-EQUALS-TOTAL.

    Bookkeeping sanity: every entry is either durable or pending,
    so the two counts add to the total. -/
theorem pending_plus_durable_equals_total :
    current_summary.pending_entries + current_summary.durable_entries
      = current_summary.total_entries := by decide

end FalsificationLedger
end Gnosis
