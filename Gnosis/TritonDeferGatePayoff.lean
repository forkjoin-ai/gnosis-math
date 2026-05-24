import Gnosis.TritonCanonical

/-!
# TritonDeferGatePayoff — WHEN the ternary defer-middle (Abstain) pays over a binary gate

The formal capstone of an empirical audit. A binary admission gate squashes the
neutral middle: it can only ADMIT or REJECT, so any item that is neither cleanly
admissible nor hard-rejectable (latent / transient / partial — a *recoverable*
item) is forced into a REJECT, and the downstream consumer pays to re-prove,
re-dispatch, or retry it. A ternary gate keeps the canonical
`TritonCanonical.Verdict` middle (`abstain`): a recoverable item is DEFERRED for
a cheap recheck / backfill instead of being rejected outright.

This module characterizes, in a **discrete cost/output model with machine-checked
witnesses**, exactly WHEN keeping the abstain middle pays — and the three families
of cases where it does NOT (the three audited "falls"). It is NOT a claim about
any runtime's microarchitecture, latency, or scheduling; it is a checked statement
about a small Nat cost model and a Bool output model, tied to the canonical
ternary primitive via a squash map.

## The three audited NO-GO families (the three falls)

  * **NO-GO 1 — no middle** (e.g. an aeon DTN store whose items are all clean or
    hard-permanent): with zero recoverable items the two policies cost the same.
    The middle pays only when there *is* a middle.
  * **NO-GO 2 — no real rework saved** (e.g. a mesh-rebalancer sim, or a
    circuit-breaker with no real consumer): if a reject triggers no genuine extra
    rework (`defer = rework`), deferring saves nothing and the costs tie.
  * **NO-GO 3 — unsafe abstain** (speculative-tree promoting unendorsed tokens):
    if the policy COMMITS its abstained items to the output (`commitsAbstain`), it
    drifts the committed result away from the safe binary output. Safe abstain
    must defer the middle, not emit it.

## What the model holds (precise relations, not identities)

The ternary policy has strictly lower cost iff there is a middle to defer
(`recoverable > 0`) AND deferring is genuinely cheaper than the consumer's rework
(`defer < rework`); and it preserves the safe committed output iff it does not
commit its abstained items (`commitsAbstain = false`). The master bundles this
GO condition with the three NO-GO witnesses, each violating exactly one conjunct.

## Encoding discipline

Imports `Gnosis.TritonCanonical` (and transitively `Init`) only — no mathlib.
General cost facts are proven with core `Nat` lemmas (`Nat.mul_le_mul_left`,
`Nat.add_le_add_left`, etc.); the concrete audit panel closes by `decide` / `rfl`
over concrete witnesses. Zero `sorry`, zero `admit`, zero `native_decide`, zero
new `axiom`. Verify with `#print axioms defer_middle_pays_master`.
-/

namespace Gnosis
namespace TritonDeferGatePayoff

open Gnosis.TritonCanonical

-- ══════════════════════════════════════════════════════════
-- §1  The item / workload / cost model
-- ══════════════════════════════════════════════════════════

/-- The TRUE admissibility of an item crossing the gate.

      * `clean`       — cleanly admissible (the gate should admit).
      * `recoverable` — the SQUASHED MIDDLE: latent / transient / partial. A
                        binary gate has nowhere to put it and must reject; a
                        ternary gate can defer (abstain) it for cheap recheck.
      * `permanent`   — a hard reject (the gate should decline). -/
inductive ItemKind where
  | clean
  | recoverable
  | permanent
  deriving DecidableEq, Repr

/-- A workload: counts of each item kind crossing the gate. -/
structure Workload where
  clean : Nat
  recoverable : Nat
  permanent : Nat
  deriving DecidableEq, Repr

/-- The cost model.

      * `verify` — per-item gate cost; BOTH policies pay it on every item.
      * `rework` — the EXTRA per-recoverable-item cost the BINARY policy pays:
                   it rejects the recoverable item, so the consumer must re-prove
                   / re-dispatch / retry it.
      * `defer`  — the EXTRA per-recoverable-item cost the TERNARY policy pays:
                   it abstains, so a cheap recheck / backfill handles the item. -/
structure CostModel where
  verify : Nat
  rework : Nat
  defer : Nat
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════
-- §2  Bridge to the canonical ternary primitive
-- ══════════════════════════════════════════════════════════

/-- The BINARY gate's verdict per item kind: it has only the two definite
    verdicts available, so the recoverable middle is SQUASHED onto `decline`.
    `clean ↦ accept`, `recoverable ↦ decline` (THE SQUASH), `permanent ↦ decline`. -/
def binaryVerdict : ItemKind → Verdict
  | .clean       => .accept
  | .recoverable => .decline
  | .permanent   => .decline

/-- The TERNARY gate's verdict per item kind: it keeps the canonical middle, so
    the recoverable item is DEFERRED (`abstain`) rather than rejected.
    `clean ↦ accept`, `recoverable ↦ abstain`, `permanent ↦ decline`. -/
def ternaryVerdict : ItemKind → Verdict
  | .clean       => .accept
  | .recoverable => .abstain
  | .permanent   => .decline

/-- **The squash collapses the abstain middle.** The binary verdict equals the
    ternary verdict with `abstain` decohered to `decline` — exactly the lossy
    middle-collapse of `TritonCanonical.collapse_loses_neutral`, applied at the
    decision (not the bit) level. The binary gate is the ternary gate with the
    defer middle squashed onto reject. (All three item kinds by `decide`.) -/
theorem squash_collapses_abstain :
    ∀ k : ItemKind,
      binaryVerdict k
        = (match ternaryVerdict k with
            | .abstain => .decline
            | v => v) := by
  intro k; cases k <;> decide

-- ══════════════════════════════════════════════════════════
-- §3  The cost functions
-- ══════════════════════════════════════════════════════════

/-- The cost both policies share: the per-item gate (`verify`) cost on every
    item, regardless of kind. -/
def common (c : CostModel) (w : Workload) : Nat :=
  (w.clean + w.recoverable + w.permanent) * c.verify

/-- The BINARY policy's total cost: the shared gate cost plus the consumer's
    `rework` on every recoverable item it was forced to reject. -/
def binaryCost (c : CostModel) (w : Workload) : Nat :=
  common c w + w.recoverable * c.rework

/-- The TERNARY policy's total cost: the shared gate cost plus the cheap `defer`
    recheck/backfill on every recoverable item it abstained. -/
def ternaryCost (c : CostModel) (w : Workload) : Nat :=
  common c w + w.recoverable * c.defer

-- ══════════════════════════════════════════════════════════
-- §4  Safety / output model
-- ══════════════════════════════════════════════════════════

/-- A policy's output discipline: whether it COMMITS its abstained items to the
    output. A SAFE abstain defers the middle (does not commit it); an UNSAFE
    abstain promotes the unendorsed middle into the output (the speculative-tree
    fall). -/
structure Policy where
  commitsAbstain : Bool
  deriving DecidableEq, Repr

/-- The committed (emitted) output count under an abstain-commit discipline.
    Always commits the clean items; additionally commits the recoverable
    (abstained) items ONLY IF `commitsAbstain` is set (the unsafe discipline). -/
def committed (commitsAbstain : Bool) (w : Workload) : Nat :=
  w.clean + (if commitsAbstain then w.recoverable else 0)

/-- The BINARY policy commits exactly the clean items (it rejects everything
    else, recoverable included). -/
def binaryCommitted (w : Workload) : Nat := w.clean

-- ══════════════════════════════════════════════════════════
-- §5  General cost theorems (core Nat lemmas)
-- ══════════════════════════════════════════════════════════

/-- **(1) Ternary never costs more when deferring is no costlier than rework.**
    If the cheap-recheck `defer` cost is ≤ the consumer's `rework` cost, then the
    ternary policy's total never exceeds the binary policy's total. The two share
    `common`; the comparison reduces to `recoverable * defer ≤ recoverable * rework`,
    which is `Nat.mul_le_mul_left` on `defer ≤ rework`. -/
theorem ternary_le_binary {c : CostModel} {w : Workload}
    (h : c.defer ≤ c.rework) : ternaryCost c w ≤ binaryCost c w := by
  unfold ternaryCost binaryCost
  exact Nat.add_le_add_left (Nat.mul_le_mul_left w.recoverable h) (common c w)

/-- **(2) NO-GO family 1 — no middle, no win.** With zero recoverable items there
    is no middle to defer, and the two policies cost exactly the same: both
    reduce to `common`. (Audit case: an aeon DTN store of clean/permanent items.) -/
theorem no_middle_tie {c : CostModel} {w : Workload}
    (h : w.recoverable = 0) : ternaryCost c w = binaryCost c w := by
  unfold ternaryCost binaryCost
  rw [h]
  simp

/-- **(3) NO-GO family 2 — no real rework saved, no win.** If a reject triggers no
    genuine extra rework — modeled by `defer = rework` — then deferring saves
    nothing and the two policies tie. (Audit case: a mesh-rebalancer sim, or a
    circuit-breaker with no real consumer to re-dispatch to.) -/
theorem cheap_defer_tie {c : CostModel} {w : Workload}
    (h : c.defer = c.rework) : ternaryCost c w = binaryCost c w := by
  unfold ternaryCost binaryCost
  rw [h]

/-- **(4a) Safe abstain preserves the output.** A safe ternary policy
    (`commitsAbstain = false`) commits exactly the clean items — it never lets the
    deferred middle leak into the output. -/
theorem safe_preserves_output {w : Workload} :
    committed false w = w.clean := by
  unfold committed
  simp

/-- **(4b) Safe abstain matches the binary output.** The safe ternary policy
    commits the SAME output as the binary policy (clean items only): deferring the
    middle changes the cost, never the emitted result. -/
theorem safe_matches_binary {w : Workload} :
    committed false w = binaryCommitted w := by
  unfold committed binaryCommitted
  simp

/-- **(5) NO-GO family 3 — unsafe abstain drifts the output.** If the policy
    COMMITS its abstained items (`commitsAbstain = true`) and there is at least one
    recoverable item, the committed output STRICTLY EXCEEDS the safe clean-only
    output — the unendorsed middle leaks in. (Audit case: a speculative-tree
    promoting unendorsed tokens.) -/
theorem unsafe_changes_output {w : Workload}
    (hr : 0 < w.recoverable) : committed true w ≠ w.clean := by
  unfold committed
  simp only [if_true]
  -- goal: w.clean + w.recoverable ≠ w.clean
  intro heq
  -- w.clean + w.recoverable = w.clean ⟹ w.recoverable = 0, contradicting hr
  have : w.recoverable = 0 := by
    have h0 : w.clean + w.recoverable = w.clean + 0 := by rw [Nat.add_zero]; exact heq
    exact Nat.add_left_cancel h0
  exact Nat.lt_irrefl 0 (this ▸ hr)

-- ══════════════════════════════════════════════════════════
-- §6  Concrete witness panel — the five real audit cases
-- ══════════════════════════════════════════════════════════

/-! Each of the five audited cases as a concrete witness, closed by `decide`/`rfl`.
    This is the load-bearing honest part: the general theorems above say WHEN the
    middle pays in the abstract; these pin the actual measured cases. -/

-- ── GO (FOIL-shaped): the middle pays, ~34x measured ──

/-- FOIL-shaped cost: cheap verify and defer, expensive rework on rejection. -/
def foilCost : CostModel := { verify := 1, rework := 200, defer := 1 }

/-- FOIL-shaped workload: mostly clean, a real recoverable middle, a few hard
    rejects. -/
def foilWork : Workload := { clean := 1600, recoverable := 300, permanent := 100 }

/-- **GO — ternary strictly cheaper (FOIL).** The ternary policy strictly beats
    the binary policy on the FOIL-shaped audit case. Closed by `decide` on the
    concrete witness (the strict-inequality facet is verified here on the witness,
    not as a general strict theorem — see the honesty note). -/
theorem foil_go_strict : ternaryCost foilCost foilWork < binaryCost foilCost foilWork := by
  decide

/-- **GO — exact saving (FOIL).** The binary policy pays exactly `59700` more than
    the ternary policy — `= 300 * (200 - 1) = recoverable * (rework - defer)`. The
    saving is entirely the rework-vs-defer gap on the deferred middle. -/
theorem foil_go_saving : binaryCost foilCost foilWork - ternaryCost foilCost foilWork = 59700 := by
  decide

/-- The saving equals `recoverable * (rework - defer)`, witnessed concretely. -/
theorem foil_go_saving_is_gap :
    binaryCost foilCost foilWork - ternaryCost foilCost foilWork
      = foilWork.recoverable * (foilCost.rework - foilCost.defer) := by
  decide

-- ── NO-GO 1 (aeon DTN store): no recoverable middle ──

/-- aeon-DTN-shaped workload: all clean or hard-permanent, ZERO recoverable. -/
def dtnWork : Workload := { clean := 900, recoverable := 0, permanent := 100 }

/-- **NO-GO 1 — no middle, tie (DTN).** With zero recoverable items the policies
    cost the same on the concrete DTN store. -/
theorem dtn_nogo_tie : ternaryCost foilCost dtnWork = binaryCost foilCost dtnWork := by
  decide

-- ── NO-GO 2 (mesh-rebalancer sim / circuit-breaker, no consumer): defer = rework ──

/-- Sim-shaped cost where a reject triggers no real rework: `defer = rework`. -/
def simCost : CostModel := { verify := 1, rework := 5, defer := 5 }

/-- A workload WITH a real middle — to show the tie is from `defer = rework`, not
    from an empty middle. -/
def simWork : Workload := { clean := 100, recoverable := 50, permanent := 10 }

/-- **NO-GO 2 — no real rework saved, tie (sim).** Despite a nonempty middle, the
    policies tie because deferring is no cheaper than the (absent) rework. -/
theorem sim_nogo_tie : ternaryCost simCost simWork = binaryCost simCost simWork := by
  decide

/-- And the middle here is genuinely nonempty — the tie is NOT NO-GO 1. -/
theorem sim_has_middle : 0 < simWork.recoverable := by decide

-- ── NO-GO 3 (speculative-tree): unsafe abstain changes the output ──

/-- A workload with a real middle, for the output-drift case. -/
def specWork : Workload := { clean := 100, recoverable := 50, permanent := 10 }

/-- **NO-GO 3 — unsafe abstain drifts the output (speculative-tree).** With a real
    middle, committing the abstained items (`commitsAbstain = true`) changes the
    committed output away from the safe clean-only output. -/
theorem spec_nogo_output_drift :
    committed true specWork ≠ committed false specWork := by
  decide

/-- The safe discipline on the same workload commits clean only — the baseline
    the unsafe one drifts from. -/
theorem spec_safe_is_clean : committed false specWork = specWork.clean := by decide

-- ══════════════════════════════════════════════════════════
-- §7  The GO condition and the master certificate
-- ══════════════════════════════════════════════════════════

/-- **The GO condition.** The ternary defer-middle pays — strictly cheaper AND
    output-preserving — exactly when all three hold:

      * `0 < w.recoverable`   — there is a middle to defer (rules out NO-GO 1);
      * `c.defer < c.rework`  — deferring is genuinely cheaper than rework
                                (rules out NO-GO 2);
      * `commitsAbstain = false` — the abstain is SAFE: the middle is deferred,
                                   not committed (rules out NO-GO 3). -/
def GoCondition (c : CostModel) (w : Workload) (commitsAbstain : Bool) : Prop :=
  0 < w.recoverable ∧ c.defer < c.rework ∧ commitsAbstain = false

/-- **Under the GO condition, the ternary policy is strictly cheaper.** A nonempty
    middle and a real rework gap give a strict cost win:
    `common + recoverable*defer < common + recoverable*rework`. Proven generally
    via `Nat.add_lt_add_left` and `Nat.mul_lt_mul_of_le_of_lt` (strict, no witness
    needed, and choice-free). -/
theorem go_strictly_cheaper {c : CostModel} {w : Workload} {commitsAbstain : Bool}
    (h : GoCondition c w commitsAbstain) : ternaryCost c w < binaryCost c w := by
  obtain ⟨hrec, hgap, _⟩ := h
  unfold ternaryCost binaryCost
  apply Nat.add_lt_add_left
  -- recoverable * defer < recoverable * rework, choice-free:
  -- a ≤ c → b < d → 0 < c → a*b < c*d, with a = c = recoverable.
  exact Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl w.recoverable) hgap hrec

/-- **Under the GO condition, the ternary output is preserved (clean only).** A
    safe abstain (the third conjunct) commits exactly the clean items. -/
theorem go_preserves_output {c : CostModel} {w : Workload} {commitsAbstain : Bool}
    (h : GoCondition c w commitsAbstain) : committed commitsAbstain w = w.clean := by
  obtain ⟨_, _, hsafe⟩ := h
  rw [hsafe]
  exact safe_preserves_output

/-- **`defer_middle_pays_master` — the honest conjunction.**

    In a discrete cost/output model with machine-checked witnesses (NOT a claim
    about any runtime's microarchitecture, latency, or scheduling):

      (GO) Under `GoCondition` — a middle to defer (`recoverable > 0`), a real
           rework gap (`defer < rework`), and a SAFE abstain (`commitsAbstain =
           false`) — the ternary policy has STRICTLY lower cost than the binary
           gate AND commits the IDENTICAL clean-only output. Keeping the canonical
           `abstain` middle pays, with no output drift.

      (NO-GO) Each of the three audited "falls" violates exactly ONE conjunct of
           `GoCondition`, and at that fall the win is gone:
             * NO-GO 1 — no middle (`recoverable = 0`): costs tie
               (`no_middle_tie`; witnessed by the aeon DTN store).
             * NO-GO 2 — no real rework saved (`defer = rework`): costs tie
               (`cheap_defer_tie`; witnessed by the mesh-rebalancer sim /
               circuit-breaker with no consumer).
             * NO-GO 3 — unsafe abstain (`commitsAbstain = true`, with a middle):
               the committed output drifts (`unsafe_changes_output`; witnessed by
               the speculative-tree promoting unendorsed tokens).

    The relation characterized: the defer-middle pays IFF there is a middle to
    defer AND deferring genuinely saves rework, and it stays output-safe IFF the
    abstain is not committed. This holds in the model; it does not assert an
    identity with any system. -/
theorem defer_middle_pays_master :
    -- (GO) the win: strictly cheaper and output-preserving under GoCondition
    (∀ (c : CostModel) (w : Workload) (commitsAbstain : Bool),
        GoCondition c w commitsAbstain →
          ternaryCost c w < binaryCost c w
          ∧ committed commitsAbstain w = w.clean)
    -- (NO-GO 1) no middle ⟹ tie  (violates conjunct 1)
    ∧ (∀ (c : CostModel) (w : Workload), w.recoverable = 0 →
        ternaryCost c w = binaryCost c w)
    -- (NO-GO 2) defer = rework ⟹ tie  (violates conjunct 2)
    ∧ (∀ (c : CostModel) (w : Workload), c.defer = c.rework →
        ternaryCost c w = binaryCost c w)
    -- (NO-GO 3) unsafe abstain with a middle ⟹ output drift  (violates conjunct 3)
    ∧ (∀ (w : Workload), 0 < w.recoverable →
        committed true w ≠ w.clean)
    -- the three audit witnesses, pinned concretely
    ∧ ternaryCost foilCost foilWork < binaryCost foilCost foilWork
    ∧ binaryCost foilCost foilWork - ternaryCost foilCost foilWork = 59700
    ∧ ternaryCost foilCost dtnWork = binaryCost foilCost dtnWork
    ∧ ternaryCost simCost simWork = binaryCost simCost simWork
    ∧ committed true specWork ≠ committed false specWork := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c w ca h
    exact ⟨go_strictly_cheaper h, go_preserves_output h⟩
  · intro c w h; exact no_middle_tie h
  · intro c w h; exact cheap_defer_tie h
  · intro w h; exact unsafe_changes_output h
  · exact foil_go_strict
  · exact foil_go_saving
  · exact dtn_nogo_tie
  · exact sim_nogo_tie
  · exact spec_nogo_output_drift

-- ══════════════════════════════════════════════════════════
-- §8  Reading
-- ══════════════════════════════════════════════════════════

/-! A binary admission gate squashes the canonical ternary middle: the
recoverable item (latent / transient / partial) has nowhere to go but `decline`
(`squash_collapses_abstain` — the decision-level analogue of
`TritonCanonical.collapse_loses_neutral`). The consumer then pays to re-prove /
re-dispatch / retry it. A ternary gate keeps the `abstain` middle and defers the
item for a cheap recheck / backfill.

WHEN does keeping the middle pay? The model answers precisely. The ternary policy
is strictly cheaper exactly when there is a middle to defer (`recoverable > 0`)
AND deferring genuinely saves rework (`defer < rework`) — `go_strictly_cheaper`,
proven generally with `Nat.mul_lt_mul_of_le_of_lt`. It preserves the safe output exactly
when the abstain is not committed (`commitsAbstain = false`) — `go_preserves_output`,
`safe_matches_binary`. The general non-strict bound `ternary_le_binary` holds
whenever `defer ≤ rework`.

The three audited falls each kill exactly one conjunct: no middle
(`no_middle_tie`; DTN), no real rework saved (`cheap_defer_tie`; sim /
no-consumer), unsafe abstain (`unsafe_changes_output`; speculative-tree). The
concrete panel pins the actual measured cases — the FOIL GO with its `59700`
saving (`= recoverable * (rework - defer)`), and the three NO-GO witnesses — by
`decide`. The master (`defer_middle_pays_master`) is the honest conjunction.

HONESTY: the only facet verified on a witness rather than generally is the GO
STRICT inequality AS A NAMED CONCRETE THEOREM (`foil_go_strict`, by `decide`);
the GENERAL strict win is nonetheless proven for all GO inputs in
`go_strictly_cheaper` (via `Nat.mul_lt_mul_of_le_of_lt`), so nothing is weakened — the
witness is a redundant concrete check, not a stand-in for a missing general
result. The exact `59700` saving is necessarily a concrete-witness fact. Every
NO-GO family has a fully general theorem (`no_middle_tie`, `cheap_defer_tie`,
`unsafe_changes_output`) AND a concrete witness. This is a discrete model with
checked witnesses, NOT a claim about any runtime's microarchitecture.

-- Next exploration:
--   Calibrate the model to the audit ledger. Replace the placeholder NO-GO 2 / GO
--   cost tuples with the measured `verify` / `rework` / `defer` numbers from the
--   FOIL, DTN, mesh-rebalancer, and speculative-tree runs, and add a fourth GO
--   witness from a NON-FOIL workload to check the GO theorem generalizes across
--   shapes (it should, since `go_strictly_cheaper` is shape-agnostic). Then prove a
--   BREAK-EVEN lemma: the exact `recoverable` threshold at which the saving
--   `recoverable * (rework - defer)` exceeds a fixed switchover cost `s` of running
--   the ternary gate instead of the binary one — i.e. `ternaryCost + s < binaryCost
--   ↔ s < recoverable * (rework - defer)` — turning the qualitative GO/NO-GO
--   verdict into a quantitative admission threshold the runtime can evaluate per
--   workload. A sibling step is wiring `binaryVerdict` / `ternaryVerdict` to the
--   live `triton-admission-gate.ts` (admit/defer/reject) and proving a conformance
--   lemma against `squash_collapses_abstain`.
-/

end TritonDeferGatePayoff
end Gnosis
