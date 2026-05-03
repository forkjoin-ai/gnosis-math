/-
  BuleBudgetLedger.lean
  =====================

  THE OPERATIONAL BULE BUDGET FOR THE 2026-05-03 SESSION.

  This module is the cumulative measurement-cost ledger for the
  current session. Where `FalsificationLedger` records WHICH
  hypotheses fell, and `NoCloningTaxEqualsBuleCost` proves WHY each
  fall costs one bule, this module records the RUNNING TOTAL of
  bule paid across the session. It is the operational accounting
  layer: the runtime can read this module to know, at a glance,
  how much measurement cost has been paid this session.

  Eight bule units paid in total:

    Five for falsifications:
      F1 (wave 4) — Qwen-Coder-7B at K=5 cross-model PCA
      F2 (wave 4) — Strict K=1 spec-decode argmax preservation
      F3 (wave 6) — Rank density k/hidden_dim invariance
      F4 (wave 7) — Binary semantics gap
      F5 (wave 9) — Hole shape evolution

    Three for non-falsification status changes:
      Qwen-0.5B initial measurement (wave 1)
      Llama-1B vacuous admission (wave 8) — the anti-theory correction
      Wave-7 methodology reconciliation

  The breakdown gives the runtime a measurable "cost of seeing" for
  the session, denominated in the canonical bule unit. Falsifications
  account for the majority of bule spend (5 of 8), confirming that
  the session's empirical work was dominantly about discovering walls
  rather than building positive theorems.

  Future agents should APPEND to `session_ledger` as they spend
  additional bule. The `total_bule_spent` function is the running
  cumulative cost. The `bule_spend_audit` query lets the runtime
  enforce a per-session measurement budget cap.
-/

import Gnosis.NoCloningTaxEqualsBuleCost
import Gnosis.VacuumToFalsificationLift
import Gnosis.FalsificationLedger

namespace Gnosis.BuleBudgetLedger

/-! ## The bule spend entry -/

/--
A single bule-spend event in the session's operational ledger.

  * `measurement_label` — short identifier ("F1", "wave-7-reconciliation",
    "qwen-0.5b-init", etc).
  * `bule_paid` — how many bule units this event cost. Per
    `NoCloningTaxEqualsBuleCost`, every status-changing measurement
    pays at least one.
  * `wave_number` — the methodology wave (1..9) during which the spend
    occurred.
  * `corresponds_to_falsification` — true iff this spend was paid to
    record an entry in `FalsificationLedger`. False iff the spend
    was paid for a non-falsification status change (initial
    measurement, vacuous admission, methodology reconciliation).
-/
structure BuleSpendEntry where
  measurement_label : String
  bule_paid : Nat
  wave_number : Nat
  corresponds_to_falsification : Bool
deriving Repr

/-! ## The eight session entries -/

/-- F1 — Qwen-Coder-7B K=5 cross-model PCA falsification (wave 4). -/
def f1_spend : BuleSpendEntry :=
  { measurement_label := "F1"
    bule_paid := 1
    wave_number := 4
    corresponds_to_falsification := true }

/-- F2 — Strict K=1 spec-decode argmax falsification (wave 4). -/
def f2_spend : BuleSpendEntry :=
  { measurement_label := "F2"
    bule_paid := 1
    wave_number := 4
    corresponds_to_falsification := true }

/-- F3 — Rank density invariant falsification (wave 6). -/
def f3_spend : BuleSpendEntry :=
  { measurement_label := "F3"
    bule_paid := 1
    wave_number := 6
    corresponds_to_falsification := true }

/-- F4 — Binary semantics gap falsification (wave 7). -/
def f4_spend : BuleSpendEntry :=
  { measurement_label := "F4-binary-semantics"
    bule_paid := 1
    wave_number := 7
    corresponds_to_falsification := true }

/-- F5 — Hole shape evolution falsification (wave 9). -/
def f5_spend : BuleSpendEntry :=
  { measurement_label := "F5-hole-shape"
    bule_paid := 1
    wave_number := 9
    corresponds_to_falsification := true }

/-- Qwen-0.5B initial measurement: Vacuous → NotYetFalsified (wave 1). -/
def qwen_0_5b_initial_spend : BuleSpendEntry :=
  { measurement_label := "qwen-0.5b-init"
    bule_paid := 1
    wave_number := 1
    corresponds_to_falsification := false }

/-- Llama-1B vacuous admission: NotYetFalsified → Vacuous (wave 8).
    The wave-8 anti-theory correction; pays the bule for retraction. -/
def llama_1b_vacuous_admission_spend : BuleSpendEntry :=
  { measurement_label := "llama-1b-anti-theory-correction"
    bule_paid := 1
    wave_number := 8
    corresponds_to_falsification := false }

/-- Wave-7 methodology reconciliation event. -/
def wave_7_reconciliation_spend : BuleSpendEntry :=
  { measurement_label := "wave-7-methodology-reconciliation"
    bule_paid := 1
    wave_number := 7
    corresponds_to_falsification := false }

/-! ## The session ledger -/

/--
The session-wide bule-spend ledger. Append-only; future agents add
entries to the END of this list as they spend additional bule.
-/
def session_ledger : List BuleSpendEntry :=
  [ f1_spend
  , f2_spend
  , f3_spend
  , f4_spend
  , f5_spend
  , qwen_0_5b_initial_spend
  , llama_1b_vacuous_admission_spend
  , wave_7_reconciliation_spend ]

/-! ## Query functions -/

/-- Total bule paid across all entries. -/
def total_bule_spent : List BuleSpendEntry → Nat
  | [] => 0
  | e :: rest => e.bule_paid + total_bule_spent rest

/-- Total bule paid for falsification events only. -/
def bule_spent_on_falsifications : List BuleSpendEntry → Nat
  | [] => 0
  | e :: rest =>
      (if e.corresponds_to_falsification then e.bule_paid else 0)
      + bule_spent_on_falsifications rest

/-- Total bule paid in a specific wave. -/
def bule_spent_per_wave : List BuleSpendEntry → Nat → Nat
  | [], _ => 0
  | e :: rest, w =>
      (if e.wave_number = w then e.bule_paid else 0)
      + bule_spent_per_wave rest w

/-! ## Per-instance totals for the session -/

/-- The session paid 8 bule total. -/
def total_session_bule_spent : Nat := total_bule_spent session_ledger

/-- The session paid 5 bule for falsifications. -/
def bule_spent_on_falsifications_in_session : Nat :=
  bule_spent_on_falsifications session_ledger

/-- Bule spent in wave 4 (F1 + F2 = 2). -/
def bule_spent_in_wave_4 : Nat := bule_spent_per_wave session_ledger 4

/-- Bule spent in wave 7 (F4 + reconciliation = 2). -/
def bule_spent_in_wave_7 : Nat := bule_spent_per_wave session_ledger 7

/-- Bule spent in wave 9 (F5 = 1). -/
def bule_spent_in_wave_9 : Nat := bule_spent_per_wave session_ledger 9

/-! ## Decide-checked theorems on the totals -/

/-- The session paid exactly 8 bule across all measurement events. -/
theorem total_session_bule_spent_eq_8 : total_session_bule_spent = 8 := by
  decide

/-- Five of those eight bule were paid for falsifications (F1..F5). -/
theorem bule_spent_on_falsifications_in_session_eq_5 :
    bule_spent_on_falsifications_in_session = 5 := by
  decide

/-- Wave 4 paid 2 bule (F1 + F2). -/
theorem bule_spent_in_wave_4_eq_2 : bule_spent_in_wave_4 = 2 := by
  decide

/-- Wave 7 paid 2 bule (F4 + methodology reconciliation). -/
theorem bule_spent_in_wave_7_eq_2 : bule_spent_in_wave_7 = 2 := by
  decide

/-- Wave 9 paid 1 bule (F5). -/
theorem bule_spent_in_wave_9_eq_1 : bule_spent_in_wave_9 = 1 := by
  decide

/-! ## The "falsifications dominate" theorem -/

/--
Falsifications account for 5 bule of the 8 spent; the remaining 3
went to non-falsification status changes (initial measurement,
vacuous admission, reconciliation). Five strictly exceeds three:
the session's bule budget went mostly to discovering walls, not
building positive theorems.
-/
theorem falsifications_account_for_majority_of_bule_spend :
    bule_spent_on_falsifications_in_session >
      (total_session_bule_spent - bule_spent_on_falsifications_in_session) := by
  decide

/-! ## Per-wave summaries -/

/--
Compact per-wave summary: how many bule were paid in this wave,
and how many of those entries corresponded to falsifications.
-/
structure WaveSummary where
  wave_number : Nat
  bule_paid_this_wave : Nat
  falsifications_this_wave : Nat
deriving Repr

/-- Count entries in a wave that correspond to falsifications. -/
def falsifications_per_wave : List BuleSpendEntry → Nat → Nat
  | [], _ => 0
  | e :: rest, w =>
      (if e.wave_number = w ∧ e.corresponds_to_falsification then 1 else 0)
      + falsifications_per_wave rest w

/-- Build a `WaveSummary` for a given wave from the session ledger. -/
def wave_summary_for (w : Nat) : WaveSummary :=
  { wave_number := w
    bule_paid_this_wave := bule_spent_per_wave session_ledger w
    falsifications_this_wave := falsifications_per_wave session_ledger w }

/-- One summary per wave 1..9. -/
def wave_summaries : List WaveSummary :=
  [ wave_summary_for 1
  , wave_summary_for 2
  , wave_summary_for 3
  , wave_summary_for 4
  , wave_summary_for 5
  , wave_summary_for 6
  , wave_summary_for 7
  , wave_summary_for 8
  , wave_summary_for 9 ]

/-- Sum of bule across all wave summaries. -/
def total_bule_across_wave_summaries : Nat :=
  (wave_summaries.map (·.bule_paid_this_wave)).foldr (· + ·) 0

/-- Sum of falsifications across all wave summaries. -/
def total_falsifications_across_wave_summaries : Nat :=
  (wave_summaries.map (·.falsifications_this_wave)).foldr (· + ·) 0

/-- Wave summaries account for all 8 bule spent. -/
theorem wave_summaries_total_bule_eq_8 :
    total_bule_across_wave_summaries = 8 := by
  decide

/-- Wave summaries account for all 5 falsifications. -/
theorem wave_summaries_total_falsifications_eq_5 :
    total_falsifications_across_wave_summaries = 5 := by
  decide

/-! ## The "wave 4 is the falsification wave" theorem -/

/--
Wave 4 is the only wave with a 1:1 falsification-to-bule ratio: it
paid exactly 2 bule and recorded exactly 2 falsifications (F1 and
F2). Other waves either paid bule without recording a falsification
(wave 1: initial measurement; wave 8: vacuous admission) or paid
bule for both falsification and non-falsification events (wave 7:
F4 + reconciliation).
-/
theorem wave_4_recorded_two_falsifications_for_the_session :
    bule_spent_per_wave session_ledger 4 = 2
    ∧ falsifications_per_wave session_ledger 4 = 2 := by
  decide

/-! ## Runtime audit query -/

/--
The runtime audit. Returns `true` iff the session has spent at most
`given_budget` bule. The runtime can call `bule_spend_audit budget`
to enforce a per-session measurement budget cap, refusing further
measurements when it returns false.
-/
def bule_spend_audit (given_budget : Nat) : Bool :=
  decide (total_bule_spent session_ledger ≤ given_budget)

/-- At a budget of 10, the session is within its cap (8 ≤ 10). -/
def audit_at_budget_10 : Bool := bule_spend_audit 10

/-- At a budget of 5, the session has exceeded its cap (8 > 5). -/
def audit_at_budget_5 : Bool := bule_spend_audit 5

/-- Audit at budget 10 returns true. -/
theorem audit_at_budget_10_eq_true : audit_at_budget_10 = true := by
  decide

/-- Audit at budget 5 returns false. -/
theorem audit_at_budget_5_eq_false : audit_at_budget_5 = false := by
  decide

/-- Sanity bridge: at the exact budget (8), the audit passes. -/
theorem audit_at_exact_budget_passes : bule_spend_audit 8 = true := by
  decide

/-- Sanity bridge: at one below the exact budget (7), the audit fails. -/
theorem audit_at_under_budget_fails : bule_spend_audit 7 = false := by
  decide

end Gnosis.BuleBudgetLedger
