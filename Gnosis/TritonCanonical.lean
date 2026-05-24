import Init

/-!
# TritonCanonical — the one signed-decision-with-neutral / 3-witness base

The distributed-inference grid keeps re-deriving the same shape: a decision that
is not binary but TERNARY — accept, abstain, decline — and a quorum of three
witnesses (Probe / Return / Verify) that collapse to one stabilized verdict.
That shape is scattered across the codebase as ad-hoc booleans and bespoke
three-state enums:

  * `triton-admission-gate.ts` already runs a 3-state gate (admit/defer/reject).
  * `distributed-inference-host/src/frf.ts` tracks a bare `sawRejection : bool`.
  * `pleromatic-reasoning-validator.ts` returns a bare `valid : bool`.
  * `arena-merge-gate.ts` returns a bare `ok : bool`.
  * speculative-decode draft acceptance is a bare accept/reject bool.

Each of those booleans silently DROPS the neutral middle — the "I don't know /
defer / quarantine" verdict that a fault-tolerant grid needs. This module lands
the CANONICAL primitive once, as machine-checked decidable theorems over
concrete witnesses, so the runtime can adopt a single shared `TritonVerdict`
type instead of re-inventing it per call-site.

## What this unifies (the scattered triton faces)

  * `Gnosis.TritonQuantizationInversion.Trit` (`neg|zero|pos`) — the ternary
    ALPHABET and its `binaryCollisionWitness` / `collapse_loses_sign`: a bit
    cannot tell two signed states apart. We mirror that lossiness here for the
    DECISION alphabet.
  * `Gnosis.PleromaticGroundingTriton.GroundingNode` (`math|physics|moonshine`
    = Probe/Return/Verify) — three witnesses agreeing on a single point
    stabilize a closure. We make that agreement an executable quorum fold.
  * `Gnosis.GnosisNumbersAreStructural.triton.value = 3` — three is the smallest
    non-trivial braid; here it is the minimal fault-tolerant quorum (`3 = 2f+1`,
    `f = 1`).
  * `Gnosis.GrandReductionTriton.computeTriton` (→ {-1,0,+1}, contraction /
    equilibrium / expansion) — the same sign trichotomy, here as a verdict sign.

## Encoding discipline

`import Init` only — no mathlib. The verdict alphabet is a 3-element inductive
with `DecidableEq`; signs live in `Int`; the quorum is proven by `decide` over
all `3^3 = 27` ballots, enumerated as an explicit `List`. Every theorem closes
by `decide` or explicit small case analysis. Zero `sorry`, zero `admit`, zero
`native_decide`, zero new `axiom`. Proven, not asserted.
-/

namespace Gnosis
namespace TritonCanonical

-- ══════════════════════════════════════════════════════════
-- §1  The canonical verdict alphabet
-- ══════════════════════════════════════════════════════════

/-- The canonical ternary verdict: the signed-decision-with-neutral primitive.

    Grid aliases (the names the runtime call-sites already use):
      * `accept`  ≅ admit   (`triton-admission-gate.ts`)
      * `abstain` ≅ defer / quarantine
      * `decline` ≅ reject

    This is the single type meant to replace ad-hoc booleans at
    `frf.ts` (`sawRejection`), `pleromatic-reasoning-validator.ts` (`valid`),
    `arena-merge-gate.ts` (`ok`), and speculative-decode draft acceptance. -/
inductive Verdict where
  | decline  -- -1 : reject
  | abstain  --  0 : defer / quarantine / neutral middle
  | accept   -- +1 : admit
  deriving DecidableEq, Repr

/-- The verdict's sign in `{-1, 0, +1}` — the same trichotomy as
    `GrandReductionTriton.computeTriton` and `TritonQuantizationInversion.Trit`. -/
def sign : Verdict → Int
  | .decline => -1
  | .abstain => 0
  | .accept  => 1

theorem sign_decline : sign .decline = -1 := by decide
theorem sign_abstain : sign .abstain = 0 := by decide
theorem sign_accept  : sign .accept  = 1 := by decide

/-- **Sign is injective.** Distinct verdicts carry distinct signs, so the sign
    map loses NO information: the three decisions are genuinely three points on
    the number line, not a degenerate collapse. (Checked over all 9 ordered
    pairs by case analysis; each surviving equality goal closes by `decide`.) -/
theorem sign_injective : ∀ a b : Verdict, sign a = sign b → a = b := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

-- ══════════════════════════════════════════════════════════
-- §2  Bool subsumption — why ternary beats binary
-- ══════════════════════════════════════════════════════════

/-- The LOSSY sign-collapse of a verdict into a bool. We collapse the way a
    naive accept/reject boolean would: a positive verdict (`accept`) is `true`;
    anything not-accept (`decline` AND the neutral `abstain`) is `false`.

    This is exactly the boolean the runtime call-sites use today, and it is
    where information goes to die: `abstain` (defer/quarantine) is forced to
    masquerade as `decline`. Mirrors `binaryCollapse` /
    `TritonQuantizationInversion.binaryCollisionWitness`. -/
def collapse : Verdict → Bool
  | .accept  => true
  | .abstain => false
  | .decline => false

/-- **Binary collision witness.** The collapse maps the genuinely-distinct
    `abstain` and `decline` to the SAME bool (`false`), so a single bit cannot
    recover which one occurred. Direct mirror of
    `TritonQuantizationInversion.binaryCollisionWitness`. -/
theorem collapse_collision_witness :
    collapse .abstain = collapse .decline := by decide

/-- …yet `abstain` and `decline` are genuinely distinct verdicts with distinct
    signs (0 vs -1), so the bool drops information. The neutral middle and the
    rejection are merged. The bit drops the abstention; the verdict keeps it. -/
theorem collapse_loses_neutral :
    collapse .abstain = collapse .decline
    ∧ sign .abstain ≠ sign .decline
    ∧ Verdict.abstain ≠ Verdict.decline := by
  refine ⟨by decide, ?_, ?_⟩ <;> decide

/-- `collapse` is NOT injective: two distinct verdicts share an image. -/
theorem collapse_not_injective :
    ¬ (∀ a b : Verdict, collapse a = collapse b → a = b) := by
  intro h
  exact absurd (h .abstain .decline (by decide)) (by decide)

/-- The complete enumeration of `Verdict` — exactly three inhabitants. Used to
    bound the cardinality decidably. -/
def allVerdicts : List Verdict := [.decline, .abstain, .accept]

/-- The enumeration is complete: every verdict appears in `allVerdicts`. -/
theorem allVerdicts_complete : ∀ v : Verdict, v ∈ allVerdicts := by
  intro v
  cases v <;> decide

/-- The enumeration has no duplicates and length 3. -/
theorem allVerdicts_nodup_len :
    allVerdicts.length = 3 ∧ allVerdicts.Nodup := by
  refine ⟨by decide, ?_⟩
  decide

/-- The complete enumeration of `Bool` — exactly two inhabitants. -/
def allBools : List Bool := [false, true]

theorem allBools_complete : ∀ b : Bool, b ∈ allBools := by
  intro b; cases b <;> decide

/-- **Cardinality: `Verdict` has 3 inhabitants > 2 = `Bool`.** Three distinct
    verdicts, two distinct bools. Three strictly exceeds two. -/
theorem verdict_card_exceeds_bool :
    allVerdicts.length = 3
    ∧ allBools.length = 2
    ∧ allVerdicts.length > allBools.length := by
  refine ⟨by decide, by decide, by decide⟩

/-- **No `Bool → Verdict` is a section of `collapse`.** Because `collapse` is
    not injective, no right-inverse `g : Bool → Verdict` can satisfy
    `g (collapse v) = v` for all `v`: such a `g` would force the colliding pair
    `abstain`/`decline` (which share a bool) to the same verdict, contradiction.
    Concretely, any `g` makes `g false` a single fixed verdict, but BOTH
    `abstain` and `decline` collapse to `false`, so at most one of them can be
    recovered — `abstain` is unrepresentable in a bool. The neutral middle is
    the irreducible extra a bool cannot hold. -/
theorem no_bool_section :
    ¬ ∃ g : Bool → Verdict, ∀ v : Verdict, g (collapse v) = v := by
  rintro ⟨g, hg⟩
  -- g (collapse abstain) = abstain and g (collapse decline) = decline,
  -- but collapse abstain = collapse decline = false, so abstain = decline.
  have ha : g false = .abstain := by have := hg .abstain; simpa using this
  have hd : g false = .decline := by have := hg .decline; simpa using this
  have : (Verdict.abstain) = (Verdict.decline) := by rw [← ha, hd]
  exact absurd this (by decide)

-- ══════════════════════════════════════════════════════════
-- §3  Three-witness quorum (Probe / Return / Verify)
-- ══════════════════════════════════════════════════════════

/-- A witness role index. The three positions are the
    `PleromaticGroundingTriton` Probe / Return / Verify triple. -/
abbrev Witness := Fin 3

/-- Role names for the three witnesses (documentation; mirrors
    `GroundingNode.math|physics|moonshine` = Probe/Return/Verify). -/
def witnessRole : Witness → String
  | 0 => "probe"
  | 1 => "return"
  | _ => "verify"

/-- A ballot: each of the three witnesses casts a verdict. -/
abbrev Ballot := Witness → Verdict

/-- **The safety-first quorum fold.** Three witnesses collapse to one stabilized
    verdict (the GroundingTriton triple-agreement, made executable):

      * if ANY witness declines  ⟹ `decline`   (one veto rejects: safety first)
      * else if ALL accept       ⟹ `accept`     (unanimous admit)
      * else                     ⟹ `abstain`    (mixed accept/abstain ⟹ defer)

    Safety dominates liveness: a single decline vetoes; absent any decline, only
    unanimity admits, otherwise the grid defers. -/
def quorum (b : Ballot) : Verdict :=
  if b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline then
    .decline
  else if b 0 = .accept ∧ b 1 = .accept ∧ b 2 = .accept then
    .accept
  else
    .abstain

/-! ### Enumerating all 27 ballots

A `Ballot` is `Fin 3 → Verdict`; there are `3^3 = 27` of them. We materialize
the function-space as a `List Ballot` (one entry per assignment of the three
witnesses) and quantify quorum properties by `decide` over the list. -/

/-- Build a ballot from three explicit verdicts. -/
def mkBallot (w0 w1 w2 : Verdict) : Ballot
  | 0 => w0
  | 1 => w1
  | _ => w2

/-- All `3^3 = 27` ballots, materialized. -/
def allBallots : List Ballot :=
  let vs := allVerdicts
  vs.flatMap (fun a => vs.flatMap (fun b => vs.map (fun c => mkBallot a b c)))

/-- There are exactly 27 ballots. -/
theorem allBallots_count : allBallots.length = 27 := by decide

-- ── (a) SAFETY ──

/-- Unanimous accept yields accept. -/
theorem quorum_unanimous_accept :
    quorum (mkBallot .accept .accept .accept) = .accept := by decide

/-- **SAFETY.** Across all 27 ballots: if every witness accepts, the quorum
    accepts; and if ANY witness declines, the quorum result is NOT accept (a
    single veto blocks admission). -/
theorem quorum_safety :
    allBallots.all (fun b =>
      -- unanimous accept ⟹ accept
      (decide (b 0 = .accept ∧ b 1 = .accept ∧ b 2 = .accept)
        == decide (quorum b = .accept))
      -- any decline ⟹ result ≠ accept
      && (!(decide (b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline))
           || decide (quorum b ≠ .accept)))
    = true := by decide

/-- Any single decline forces decline (safety-first veto), witnessed across the
    three positions a decline can occupy alongside arbitrary other votes. -/
theorem quorum_decline_vetoes :
    allBallots.all (fun b =>
      !(decide (b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline))
      || decide (quorum b = .decline))
    = true := by decide

-- ── (b) FAULT-TOLERANCE (3 = 2f+1, f = 1) ──

/-- **FAULT-TOLERANCE.** Any ballot with at least one `accept`, zero `decline`,
    and the remaining witnesses `abstain` yields a result in `{accept, abstain}`
    — never `decline`. One abstaining (faulty/absent) witness cannot force a
    rejection: with `3 = 2f+1` and `f = 1`, a single non-participating witness
    is tolerated. Checked across all 27 ballots. -/
theorem quorum_fault_tolerance :
    allBallots.all (fun b =>
      -- precondition: ≥1 accept, 0 decline, rest abstain
      !(decide ((b 0 = .accept ∨ b 1 = .accept ∨ b 2 = .accept)
                ∧ ¬(b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline)
                ∧ (∀ i : Fin 3, b i = .accept ∨ b i = .abstain)))
      -- conclusion: result ∈ {accept, abstain}, never decline
      || decide (quorum b = .accept ∨ quorum b = .abstain))
    = true := by decide

/-- A concrete fault-tolerance witness: two accepts and one abstain ⟹ abstain
    (the grid defers rather than rejecting on a single missing witness). -/
theorem quorum_one_abstainer_defers :
    quorum (mkBallot .accept .accept .abstain) = .abstain
    ∧ quorum (mkBallot .accept .abstain .accept) = .abstain
    ∧ quorum (mkBallot .abstain .accept .accept) = .abstain := by decide

/-- And a single decline DOES override even two accepts (safety beats the lone
    rejecter only by vetoing — decline is the safe direction). -/
theorem quorum_one_decliner_vetoes :
    quorum (mkBallot .accept .accept .decline) = .decline
    ∧ quorum (mkBallot .accept .decline .accept) = .decline
    ∧ quorum (mkBallot .decline .accept .accept) = .decline := by decide

-- ── (c) CLOSURE ──

/-- **CLOSURE.** The quorum of three verdicts is itself a verdict — its result
    always lies in the canonical enumeration `{decline, abstain, accept}`. The
    three witnesses collapse to one stabilized verdict (the GroundingTriton
    triple-agreement: 3 → 1). Checked across all 27 ballots. -/
theorem quorum_closure :
    allBallots.all (fun b => decide (quorum b ∈ allVerdicts)) = true := by
  decide

/-- Closure stated for any ballot (not just the enumerated ones): the result is
    always one of the three verdicts, by definitional case split on `quorum`. -/
theorem quorum_total (b : Ballot) :
    quorum b = .decline ∨ quorum b = .abstain ∨ quorum b = .accept := by
  unfold quorum
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)

-- ══════════════════════════════════════════════════════════
-- §4  Structural tie — witness count = triton = 3
-- ══════════════════════════════════════════════════════════

/-- The number of witnesses in the quorum. -/
def witnessCount : Nat := 3

/-- **Structural tie.** The witness count equals
    `GnosisNumbersAreStructural.triton.value = 3` — the smallest non-trivial
    braid and the minimal fault-tolerant quorum (`3 = 2·1 + 1`, tolerating
    `f = 1` faulty witness). Three is where fault-tolerant agreement begins.

    (We restate the value `3` directly here rather than importing the catalog,
    keeping this module `Init`-only; the identity `triton.value = 3` is proven
    in `GnosisNumbersAreStructural.triton_is_smallest_non_abelian_degree`.) -/
theorem witness_count_is_triton :
    witnessCount = 3
    ∧ allBallots.length = witnessCount ^ witnessCount  -- 3^3 = 27
    ∧ witnessCount = 2 * 1 + 1                          -- 2f+1, f = 1
    ∧ witnessCount > 2 := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  decide

-- ══════════════════════════════════════════════════════════
-- §5  Master certificate
-- ══════════════════════════════════════════════════════════

/-- **TRITON-CANONICAL.**

    The single signed-decision-with-neutral / 3-witness-agreement base for the
    distributed-inference grid:

      (1) The verdict alphabet `{decline, abstain, accept}` carries an injective
          sign in `{-1, 0, +1}` — three genuine points, no collapse.
      (2) Subsumption: `|Verdict| = 3 > 2 = |Bool|`; the bool-collapse is lossy
          (`abstain`/`decline` collide) and admits no section — the neutral
          middle is unrepresentable in a bool.
      (3) The Probe/Return/Verify quorum is SAFE (any decline vetoes; only
          unanimity admits), FAULT-TOLERANT (one abstainer cannot force a
          reject; `3 = 2f+1`), and CLOSED (three verdicts fold to one verdict).
      (4) The witness count is the structural triton, `3`. -/
theorem triton_canonical_master :
    -- (1) sign injective
    (∀ a b : Verdict, sign a = sign b → a = b)
    -- (2) cardinality 3 > 2 and collapse lossy + no section
    ∧ allVerdicts.length = 3
    ∧ allBools.length = 2
    ∧ allVerdicts.length > allBools.length
    ∧ collapse .abstain = collapse .decline
    ∧ Verdict.abstain ≠ Verdict.decline
    ∧ (¬ ∃ g : Bool → Verdict, ∀ v : Verdict, g (collapse v) = v)
    -- (3) quorum safety + fault-tolerance + closure (over all 27 ballots)
    ∧ quorum (mkBallot .accept .accept .accept) = .accept
    ∧ allBallots.all (fun b =>
        !(decide (b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline))
        || decide (quorum b ≠ .accept)) = true
    ∧ allBallots.all (fun b =>
        !(decide ((b 0 = .accept ∨ b 1 = .accept ∨ b 2 = .accept)
                  ∧ ¬(b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline)
                  ∧ (∀ i : Fin 3, b i = .accept ∨ b i = .abstain)))
        || decide (quorum b = .accept ∨ quorum b = .abstain)) = true
    ∧ allBallots.all (fun b => decide (quorum b ∈ allVerdicts)) = true
    -- (4) structural tie
    ∧ witnessCount = 3
    ∧ allBallots.length = 27 := by
  refine ⟨sign_injective, ?_, ?_, ?_, ?_, ?_, no_bool_section,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

-- ══════════════════════════════════════════════════════════
-- §6  Reading
-- ══════════════════════════════════════════════════════════

/-! The grid's decisions are not binary. They are ternary: accept (admit),
abstain (defer / quarantine), decline (reject). The sign map
`{-1, 0, +1}` (`sign_injective`) shows the three are genuinely distinct, and the
bool-collapse (`collapse_loses_neutral`, `collapse_not_injective`,
`no_bool_section`) shows the neutral middle is exactly what a boolean cannot
hold — `abstain` is unrepresentable, forced to masquerade as `decline`. That is
the whole case for the type: the missing third state is the fault-tolerant
"defer".

Three witnesses (Probe / Return / Verify) fold to one stabilized verdict by the
safety-first `quorum` (`quorum_safety`, `quorum_decline_vetoes`): any decline
vetoes, and only unanimity admits. The fold is fault-tolerant
(`quorum_fault_tolerance`, `quorum_one_abstainer_defers`): a single abstaining
witness defers rather than rejecting — the `3 = 2f+1`, `f = 1` quorum. And it is
closed (`quorum_closure`, `quorum_total`): three verdicts collapse to a verdict,
the GroundingTriton triple-agreement made executable. The witness count is the
structural triton, `3` (`witness_count_is_triton`) — the smallest non-trivial
braid and the minimal fault-tolerant quorum.

-- Next exploration:
--   Runtime adoption. Materialize a shared `TritonVerdict` type in TS and Rust
--   (decline | abstain | accept, with a `sign` and a `quorum` matching this
--   module's fold) and replace the ad-hoc booleans at:
--     * `distributed-inference-host/src/frf.ts`        `sawRejection : bool`
--     * `pleromatic-reasoning-validator.ts`            `valid : bool`
--     * `arena-merge-gate.ts`                          `ok : bool`
--     * speculative-decode draft acceptance            accept/reject bool
--   In each, the bool currently merges "reject" and "defer" — exactly the
--   `abstain`/`decline` collision proven lossy here (`collapse_loses_neutral`).
--   The defer/abstain middle is the needed third state. Wire `triton-admission-
--   gate.ts`'s existing admit/defer/reject to the canonical aliases, then prove
--   a conformance lemma: the runtime `quorum` agrees with `quorum` here on all
--   27 ballots (a golden test mirroring `allBallots`).
-/

end TritonCanonical
end Gnosis
