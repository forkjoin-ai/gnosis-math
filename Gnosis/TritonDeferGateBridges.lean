import Gnosis.TritonDeferGatePayoff
import Gnosis.TritonCanonical
import Gnosis.BuleyeanProbability

/-!
# TritonDeferGateBridges — two corpus resemblances turned into checked theorems

`TritonDeferGatePayoff` characterizes WHEN the ternary defer-middle (`abstain`)
pays over a binary admission gate. The module's prose gestures at two older
corpus results it RESEMBLES. This module turns those two resemblances into
machine-checked correspondences, so the resemblance stops being rhetoric and
becomes a theorem with an honest scope:

  * **Bridge 1 — Buleyean positivity ↔ the abstain middle.**
    `BuleyeanProbability.buleyean_positivity` is the "+1 sliver" law: every choice
    in a `BuleyeanSpace` keeps strictly positive weight (`0 < bs.weight i`); no
    choice is ever pruned to zero. The defer-gate's `abstain` is the runtime face
    of that law: the ternary gate keeps the recoverable middle LIVE (above a
    positive floor), whereas the binary squash drops it to the pruned/zero state
    — exactly the no-zero floor that positivity forbids. We give the middle a
    `gateWeight` (accept/abstain = `1`, the live floor; decline = `0`, pruned) and
    prove a real theorem that INVOKES `buleyean_positivity`: the Buleyean floor is
    positive, the ternary recoverable sits at-or-above it, and the binary squash
    drops below it.

  * **Bridge 2 — safe abstain ↔ quorum fault-tolerance.**
    `TritonCanonical.quorum_fault_tolerance` / `quorum_one_abstainer_defers` say a
    single abstaining witness DEFERS the quorum (it neither vetoes like a decline
    nor commits like a unanimous accept). The defer-gate's safe abstain
    (`committed false w = w.clean`, `go_preserves_output`) is the per-item instance
    of that: the gate's abstained item, placed in a quorum ballot beside accepts
    with no decline, makes the quorum DEFER (`abstain`) — by direct APPLICATION of
    the existing quorum theorem, not a re-proof.

## Honesty about tightness (the load-bearing distinction)

These are NOT identity claims. The repo rule: rhetorical force is not evidence.

  * Bridge 2 is a **TIGHT instance**: the gate's abstain ballot
    `mkBallot accept accept abstain` is literally one of the ballots
    `quorum_one_abstainer_defers` already settles, so the bridge `apply`s the
    existing theorem. Nothing new is assumed.

  * Bridge 1 is a **weaker-but-true shared-predicate correspondence**, and we say
    so. `gateWeight` and `BuleyeanSpace.weight` are DIFFERENT functions over
    DIFFERENT domains; we do NOT claim they are the same map. What is genuinely
    shared and proven is the structural property `Retained` / a POSITIVE FLOOR:
    Buleyean positivity guarantees `1 ≤ bs.weight i` for every choice, the ternary
    recoverable verdict is `Retained` with `gateWeight = 1` (at-or-above that
    floor), and the binary squash is `¬ Retained` with `gateWeight = 0` (below it).
    The theorem `defer_keeps_positive_weight` invokes `buleyean_positivity`
    directly to witness the floor, so the correspondence is anchored to the real
    law, not a restatement.

## Encoding discipline

Imports `Gnosis.TritonDeferGatePayoff`, `Gnosis.TritonCanonical`,
`Gnosis.BuleyeanProbability` (and transitively `Init`) only — no mathlib. Each
bridge ships a concrete witness closed by `decide` AND a general statement. Zero
`sorry`, zero `admit`, zero `native_decide`, zero new `axiom`. The general
strict-floor facts use core choice-free `Nat` lemmas (`Nat.succ_le_of_lt`,
`Nat.lt_irrefl`) — no `Classical.choice`. Verify with
`#print axioms defer_gate_bridges_master`.
-/

namespace Gnosis
namespace TritonDeferGateBridges

open Gnosis.TritonCanonical
open Gnosis.TritonDeferGatePayoff

-- ══════════════════════════════════════════════════════════
-- §1  The shared "live / pruned" predicate over verdicts
-- ══════════════════════════════════════════════════════════

/-- The gate-level liveness weight of a verdict, on the SAME discrete scale the
    Buleyean floor lives on (a `Nat` with `0` = pruned, `≥1` = live):

      * `accept`  ↦ `1`  — live (committed)
      * `abstain` ↦ `1`  — live (DEFERRED, not pruned: the +1 sliver stays)
      * `decline` ↦ `0`  — pruned (rejected; below the no-zero floor)

    This is NOT the Buleyean weight function — it is a coarse `{0,1}` shadow of it
    on the verdict alphabet, chosen so that the Buleyean positivity floor (`≥1`)
    and the "is this verdict retained?" question line up on one scale. -/
def gateWeight : Verdict → Nat
  | .accept  => 1
  | .abstain => 1
  | .decline => 0

/-- A verdict is `Retained` (live, at-or-above the floor) iff its `gateWeight` is
    strictly positive — i.e. it is NOT pruned to zero. `accept` and `abstain` are
    retained; `decline` is pruned. -/
def Retained (v : Verdict) : Prop := 0 < gateWeight v

instance : DecidablePred Retained := fun v => by
  unfold Retained gateWeight; cases v <;> exact inferInstance

theorem retained_accept  : Retained .accept  := by decide
theorem retained_abstain : Retained .abstain := by decide
/-- `decline` is NOT retained: the binary squash's destination is pruned. -/
theorem not_retained_decline : ¬ Retained .decline := by decide

-- ══════════════════════════════════════════════════════════
-- §2  BRIDGE 1 — Buleyean positivity ↔ the abstain middle
-- ══════════════════════════════════════════════════════════

/-! The genuine shared content (a WEAKER-BUT-TRUE shared-predicate
    correspondence, NOT an identity): Buleyean positivity is the "+1 sliver" law
    — no choice ever reaches zero weight (`1 ≤ bs.weight i`). The ternary gate's
    recoverable verdict (`abstain`) stays `Retained` at `gateWeight = 1`, at-or-
    above that floor; the binary squash sends the SAME item to `decline`, pruned
    to `gateWeight = 0`, BELOW the floor positivity guarantees. The binary squash
    is therefore incompatible with the Buleyean no-zero law; the ternary abstain
    is that law's runtime face. -/

/-- The ternary gate keeps the recoverable middle as `abstain`. -/
theorem ternary_recoverable_abstain : ternaryVerdict .recoverable = .abstain := rfl

/-- The binary squash sends the recoverable middle to `decline`. -/
theorem binary_recoverable_decline : binaryVerdict .recoverable = .decline := rfl

/-- The ternary recoverable verdict is `Retained` (live) — concrete witness. -/
theorem ternary_recoverable_retained : Retained (ternaryVerdict .recoverable) := by decide

/-- The binary recoverable verdict is pruned (NOT retained) — concrete witness. -/
theorem binary_recoverable_pruned : ¬ Retained (binaryVerdict .recoverable) := by decide

/-- The gate weights split exactly at the floor: the ternary keeps the middle at
    the live floor (`1`), the binary squash drops it to the pruned floor (`0`). -/
theorem recoverable_weight_split :
    gateWeight (ternaryVerdict .recoverable) = 1
    ∧ gateWeight (binaryVerdict .recoverable) = 0 := by decide

/-- **BRIDGE 1 — `defer_keeps_positive_weight`.**

    Anchored to the real law: for ANY `BuleyeanSpace bs` and choice `i`, Buleyean
    positivity gives a strictly positive floor `0 < bs.weight i` (the "+1 sliver"
    — no choice ever pruned to zero), hence `1 ≤ bs.weight i`. On the gate's
    `{0,1}` shadow of that same scale, the ternary recoverable verdict
    (`abstain`) is `Retained` and sits AT-OR-ABOVE that floor
    (`gateWeight (ternaryVerdict .recoverable) ≤ bs.weight i`), while the binary
    squash drops the SAME item to `decline`, pruned to `0` — STRICTLY BELOW the
    floor positivity guarantees (`gateWeight (binaryVerdict .recoverable) <
    bs.weight i`).

    The binary squash is thus incompatible with the Buleyean no-zero law; the
    ternary abstain is the law's runtime face. (WEAKER-BUT-TRUE correspondence:
    `gateWeight` is a coarse shadow of `BuleyeanSpace.weight`, not the same map —
    what is shared and proven is the positive-floor / `Retained` property, with
    `buleyean_positivity` invoked directly to supply the floor.) -/
theorem defer_keeps_positive_weight (bs : BuleyeanSpace) (i : Fin bs.numChoices) :
    -- (the +1 sliver: the Buleyean floor is strictly positive)
    0 < bs.weight i
    -- (ternary keeps the middle at-or-above the floor — Retained, ≥ the +1 sliver)
    ∧ Retained (ternaryVerdict .recoverable)
    ∧ gateWeight (ternaryVerdict .recoverable) ≤ bs.weight i
    -- (binary squash drops the SAME item strictly below the floor — pruned to 0)
    ∧ ¬ Retained (binaryVerdict .recoverable)
    ∧ gateWeight (binaryVerdict .recoverable) < bs.weight i := by
  -- the floor, straight from the no-zero law:
  have hfloor : 0 < bs.weight i := buleyean_positivity bs i
  -- 1 ≤ bs.weight i  (the +1 sliver as a concrete lower bound)
  have hone : 1 ≤ bs.weight i := Nat.succ_le_of_lt hfloor
  refine ⟨hfloor, ternary_recoverable_retained, ?_, binary_recoverable_pruned, ?_⟩
  · -- gateWeight (ternaryVerdict .recoverable) = 1 ≤ bs.weight i
    show gateWeight (ternaryVerdict .recoverable) ≤ bs.weight i
    rw [ternary_recoverable_abstain]; exact hone
  · -- gateWeight (binaryVerdict .recoverable) = 0 < bs.weight i
    show gateWeight (binaryVerdict .recoverable) < bs.weight i
    rw [binary_recoverable_decline]; exact hfloor

-- ══════════════════════════════════════════════════════════
-- §3  BRIDGE 2 — safe abstain ↔ quorum fault-tolerance
-- ══════════════════════════════════════════════════════════

/-! The genuine content (a TIGHT instance — direct application): the defer-gate's
    safe abstain (`committed false w = w.clean`, `go_preserves_output` — the
    recoverable/abstained item is DEFERRED, not committed) behaves at the quorum
    level EXACTLY like `TritonCanonical`'s deferring witness. Place the gate's
    per-item ternary verdicts into a three-witness ballot: two clean items
    (`accept`) and one recoverable item (`abstain`), with no permanent item
    (`decline`). That ballot is literally one of the ballots
    `quorum_one_abstainer_defers` already settles, so the quorum DEFERS
    (`abstain`) — the abstaining witness neither vetoes nor commits. -/

/-- The defer-gate ballot built from per-item TERNARY verdicts: two clean
    (`accept`), one recoverable (`abstain`), no permanent (so no `decline`). This
    is the gate's middle placed alongside two definite accepts, as a quorum. -/
def gateAbstainBallot : Ballot :=
  mkBallot (ternaryVerdict .clean) (ternaryVerdict .clean) (ternaryVerdict .recoverable)

/-- The gate ballot reduces to `mkBallot accept accept abstain` — exactly one of
    the deferring ballots in `quorum_one_abstainer_defers`. -/
theorem gateAbstainBallot_eq :
    gateAbstainBallot = mkBallot .accept .accept .abstain := rfl

/-- **BRIDGE 2 — `safety_is_quorum_fault_tolerance`.**

    The defer-gate's safe abstain corresponds to a deferring quorum witness, BY
    DIRECT APPLICATION of the existing `TritonCanonical` fault-tolerance result
    (a TIGHT instance, not a re-proof):

      (1) the gate's recoverable middle IS the abstain verdict
          (`ternaryVerdict .recoverable = .abstain`);
      (2) placed in a quorum with two clean accepts and no decline, the quorum
          DEFERS — `quorum gateAbstainBallot = .abstain` — proven by `apply`ing
          `quorum_one_abstainer_defers` (the abstaining witness neither vetoes
          like `decline` nor commits like a unanimous `accept`);
      (3) and the gate's output discipline matches: a safe abstain commits exactly
          the clean items (`committed false w = w.clean`, the defer-gate's
          `safe_preserves_output`) — the per-item analogue of "abstainer defers,
          accepts commit, no decline ⟹ no veto". -/
theorem safety_is_quorum_fault_tolerance (w : Workload) :
    -- (1) the gate middle is the abstain witness
    ternaryVerdict .recoverable = Verdict.abstain
    -- (2) in quorum, the abstaining witness DEFERS — applied from the corpus theorem
    ∧ quorum gateAbstainBallot = .abstain
    -- (3) and the safe gate commits exactly the clean items (defers the abstain)
    ∧ committed false w = w.clean := by
  refine ⟨rfl, ?_, ?_⟩
  · -- TIGHT: gateAbstainBallot = mkBallot accept accept abstain, the first
    -- conjunct of quorum_one_abstainer_defers.
    rw [gateAbstainBallot_eq]
    exact quorum_one_abstainer_defers.1
  · -- the gate's safe output discipline (reuse the prior module's lemma)
    exact safe_preserves_output

/-- A purely concrete restatement of the deferring behavior, checked by `decide`:
    the gate's abstain ballot defers, while replacing the abstain by a decline
    would veto and replacing it by an accept would commit — the abstain is
    genuinely the deferring middle, neither veto nor commit. -/
theorem gate_abstain_defers_witness :
    quorum gateAbstainBallot = .abstain
    ∧ quorum (mkBallot .accept .accept .decline) = .decline
    ∧ quorum (mkBallot .accept .accept .accept)  = .accept := by decide

-- ══════════════════════════════════════════════════════════
-- §4  The master certificate
-- ══════════════════════════════════════════════════════════

/-- **`defer_gate_bridges_master` — the two corpus resemblances, made rigorous.**

    These make rigorous two of the corpus resemblances around the defer-gate:

      (Bridge 1) **Buleyean positivity** — the abstain is the "+1 sliver" / no-zero
        weight law's runtime face. For any `BuleyeanSpace`, positivity gives a
        strictly positive floor (`0 < bs.weight i`); the ternary recoverable
        middle is `Retained` at-or-above that floor while the binary squash drops
        the same item below it. (A WEAKER-BUT-TRUE shared-predicate correspondence:
        `gateWeight` is a coarse `{0,1}` shadow of `BuleyeanSpace.weight`, NOT the
        same map; the shared, proven property is the positive floor / `Retained`,
        with `buleyean_positivity` invoked directly.)

      (Bridge 2) **Quorum fault-tolerance** — the safe abstain is a deferring
        witness. The gate's recoverable middle, placed in a quorum with accepts
        and no decline, makes the quorum DEFER, by DIRECT APPLICATION of
        `quorum_one_abstainer_defers` (a TIGHT instance). Output-wise the safe
        gate commits exactly the clean items.

    This is a discrete model with checked correspondences, NOT an identity claim.
    Bridge 2 applies the existing theorem directly; Bridge 1 is the honest weaker
    shared-predicate statement. Each bridge also ships a concrete `decide`-checked
    witness. -/
theorem defer_gate_bridges_master :
    -- Bridge 1: anchored to buleyean_positivity, the floor + retained split
    (∀ (bs : BuleyeanSpace) (i : Fin bs.numChoices),
        0 < bs.weight i
        ∧ Retained (ternaryVerdict .recoverable)
        ∧ gateWeight (ternaryVerdict .recoverable) ≤ bs.weight i
        ∧ ¬ Retained (binaryVerdict .recoverable)
        ∧ gateWeight (binaryVerdict .recoverable) < bs.weight i)
    -- Bridge 2: the safe abstain defers in quorum (applied) + output preserved
    ∧ (∀ (w : Workload),
        ternaryVerdict .recoverable = Verdict.abstain
        ∧ quorum gateAbstainBallot = .abstain
        ∧ committed false w = w.clean)
    -- concrete witnesses (decide)
    ∧ gateWeight (ternaryVerdict .recoverable) = 1
    ∧ gateWeight (binaryVerdict .recoverable) = 0
    ∧ quorum gateAbstainBallot = .abstain := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro bs i; exact defer_keeps_positive_weight bs i
  · intro w; exact safety_is_quorum_fault_tolerance w
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- §5  Reading
-- ══════════════════════════════════════════════════════════

/-! Two resemblances the `TritonDeferGatePayoff` prose gestured at are now checked
theorems with honest scope.

Bridge 1 (`defer_keeps_positive_weight`) ties the gate's abstain middle to
`BuleyeanProbability.buleyean_positivity` — the "+1 sliver" / no-zero-weight law.
Positivity supplies a strictly positive floor (`0 < bs.weight i`); on the gate's
coarse `{0,1}` shadow of that scale the ternary recoverable verdict is `Retained`
at-or-above the floor (`gateWeight = 1`) while the binary squash drops the same
item below it (`gateWeight = 0`). This is the HONEST weaker correspondence: a
shared positive-floor / `Retained` predicate, NOT a claim that `gateWeight` and
`BuleyeanSpace.weight` are the same function — but the floor is the real one,
`buleyean_positivity` is invoked directly, and the binary squash provably violates
it.

Bridge 2 (`safety_is_quorum_fault_tolerance`) ties the gate's safe abstain to
`TritonCanonical.quorum_one_abstainer_defers`. The gate's recoverable middle,
placed in a three-witness quorum beside two clean accepts and no decline, makes
the quorum DEFER (`abstain`) — by DIRECT APPLICATION of the existing theorem (a
TIGHT instance). The abstaining witness neither vetoes (like `decline`) nor
commits (like a unanimous `accept`), mirroring the gate's per-item discipline
that defers the abstain and commits the clean (`safe_preserves_output`).

`defer_gate_bridges_master` conjoins both. It is a discrete model with checked
correspondences, NOT an identity claim: Bridge 2 is tight (applies the corpus
theorem); Bridge 1 is the weaker-but-true shared-predicate statement, stated as
such.

-- Next exploration:
--   Promote Bridge 1 from the `{0,1}` shadow to a graded correspondence. Define a
--   `BuleyeanSpace`-indexed verdict weighting `verdictWeight bs : Verdict → Nat`
--   that maps `decline ↦ 0` but `abstain`/`accept ↦ bs.weight i` for the choice
--   `i` the item occupies, then prove the ternary recoverable middle inherits the
--   FULL Buleyean weight (`= bs.weight i`, not merely `≥ 1`) while the binary
--   squash still drops to `0` — turning the floor inequality into an exact-value
--   correspondence anchored on `buleyean_positivity` AND
--   `buleyean_monotone_nonrejected` (the recoverable middle's weight never
--   decreases under a rejection elsewhere). A sibling step: lift Bridge 2 from the
--   single `mkBallot accept accept abstain` witness to a workload-parameterized
--   ballot family and prove the gate's per-kind ternary verdict vector quorum-
--   folds to `abstain` whenever the workload has a middle and no permanent item,
--   via `quorum_fault_tolerance` over the enumerated ballots — a general (not
--   single-witness) tight instance.
-/

end TritonDeferGateBridges
end Gnosis
