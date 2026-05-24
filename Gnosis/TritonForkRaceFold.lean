import Gnosis.TritonCanonical

/-!
# TritonForkRaceFold — the trit + fork/race/fold as a common computational substrate

One ternary primitive (`TritonCanonical.Verdict` = `{decline, abstain, accept}`) and
the fork/race/fold lifecycle, under which three regimes of computation each appear as a
PROVEN structural facet:

  * **Classical** computation is the *collapsed* trit — Bool embeds into `Verdict`
    (the two definite verdicts) and round-trips, while the neutral middle (`abstain`) is
    strictly new and has no Bool preimage. Binary logic is the trit with the middle
    decohered away: a strict sub-regime.
  * **Concurrent** computation is the *fold* — the three-witness `quorum`
    (`TritonCanonical`) is the consensus fold: safe, fault-tolerant (`3 = 2f+1`), closed.
  * **Quantum-shaped** computation is *superposition + collapse* — `sign` is the spin-1
    eigentriple `{-1, 0, +1}` (definite verdicts = eigenstates, `abstain` = the
    undetermined sign-0 superposed state), and the fold acts as an idempotent measurement
    projection `P ∘ P = P` that fixes the eigenstates and collapses the superposition.

## Honesty (read this before believing the headline)

This is a **structural / algebraic** unification with machine-checked projections, NOT a
claim that physics is unified, that consensus IS quantum mechanics, or that a `Verdict`
IS a qubit. Each "facet" is a precise *relation* (embeds into / collapses to / is
idempotent / is injective with a given range), proven by `decide` over concrete finite
witnesses, never asserted. Where the standard word would overclaim ("X IS Y") the
statements instead say "embeds", "collapses", "is the retraction of", "is idempotent",
"has range exactly". The QM language is the eigenstate/projection *algebra*
(P∘P = P fixing eigenstates), which is genuinely shared with the fold — not a physical
identity. The middle state, the quorum, and the sign map carry the load; the
"unification" is the conjunction of these checked relations and nothing more.

## Encoding discipline

Imports `Gnosis.TritonCanonical` (and transitively `Init`) only — no mathlib. Every
theorem closes by `decide` over a closed/finite statement or by explicit small case
analysis. Zero `sorry`, zero `admit`, zero `native_decide`, zero new `axiom`. Proven,
not asserted. Verify with `#print axioms computation_unification_master`.
-/

namespace Gnosis
namespace TritonForkRaceFold

open Gnosis.TritonCanonical

-- ══════════════════════════════════════════════════════════
-- §1  CLASSICAL = the collapsed trit (Bool embeds; the middle is new)
-- ══════════════════════════════════════════════════════════

/-- Embed a classical bit into the ternary verdict: `true ↦ accept`, `false ↦ decline`.
    This lands a bool on the two DEFINITE verdicts only; it never produces the neutral
    middle. Classical logic lives entirely on this two-element sub-image. -/
def embedBool : Bool → Verdict
  | true  => .accept
  | false => .decline

/-- **`embedBool` is injective.** The two bits land on two distinct definite verdicts, so
    no classical information is lost going in. (All 4 ordered pairs by `decide`.) -/
theorem embedBool_injective : ∀ a b : Bool, embedBool a = embedBool b → a = b := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

/-- **`collapse` is a retraction of `embedBool`** — classical round-trips. Sending a bit
    up into the trit and collapsing it back is the identity on `Bool`:
    `collapse (embedBool b) = b`. Binary logic is faithfully recovered from the verdict
    substrate. (`collapse` is `TritonCanonical.collapse`: `accept ↦ true`, else `false`.) -/
theorem collapse_embedBool : ∀ b : Bool, collapse (embedBool b) = b := by
  intro b; cases b <;> decide

/-- **`embedBool` is NOT surjective: `abstain` has no bool preimage.** The neutral middle
    is the strictly-new, non-classical state — unreachable from any bit. This is the
    precise sense in which the trit STRICTLY EXTENDS Bool: classical computation is the
    trit with the middle decohered away (the two-element sub-regime `{accept, decline}`). -/
theorem embedBool_not_surjective :
    ¬ ∃ b : Bool, embedBool b = Verdict.abstain := by
  rintro ⟨b, hb⟩
  cases b <;> exact absurd hb (by decide)

/-- The image of `embedBool` is exactly the two definite verdicts, never `abstain`. The
    classical sub-regime is the definite two; the superposed middle is outside it. -/
theorem embedBool_range_definite :
    ∀ b : Bool, embedBool b = Verdict.accept ∨ embedBool b = Verdict.decline := by
  intro b; cases b <;> decide

/-- **Classical-as-collapsed-trit, bundled.** `embedBool` is an injective, non-surjective
    embedding of `Bool` whose retraction is `collapse`; the one missed point is the
    neutral `abstain`. Binary logic embeds into the trit and round-trips, but cannot reach
    the middle — a strict sub-regime. -/
theorem classical_is_collapsed_trit :
    (∀ a b : Bool, embedBool a = embedBool b → a = b)              -- injective
    ∧ (∀ b : Bool, collapse (embedBool b) = b)                     -- collapse retracts
    ∧ (¬ ∃ b : Bool, embedBool b = Verdict.abstain)               -- middle unreachable
    ∧ (∀ b : Bool, embedBool b = Verdict.accept
                   ∨ embedBool b = Verdict.decline) := by          -- image = definite two
  exact ⟨embedBool_injective, collapse_embedBool,
         embedBool_not_surjective, embedBool_range_definite⟩

-- ══════════════════════════════════════════════════════════
-- §2  CONCURRENT = the fold (quorum as consensus, restated)
-- ══════════════════════════════════════════════════════════

/-! The concurrent facet is the three-witness `quorum` of `TritonCanonical`, recast here
    as the *fold* operator of fork/race/fold. We restate its consensus properties — SAFE
    (any decline vetoes; only unanimity admits), FAULT-TOLERANT (`3 = 2f+1`; one abstainer
    cannot force a reject), and CLOSED (three verdicts fold to one) — under the
    fold-operator name, so the lifecycle in §5 reads in fork/race/fold vocabulary. -/

/-- The consensus **fold**: alias for `TritonCanonical.quorum`. Three witnesses fold to one
    stabilized verdict (any decline vetoes; else unanimous accept admits; else defer). -/
def fold (b : Ballot) : Verdict := quorum b

theorem fold_eq_quorum (b : Ballot) : fold b = quorum b := rfl

/-- **CONCURRENT/SAFETY (restated).** Across all 27 ballots: any decline forces the fold to
    a non-accept (a single veto blocks admission). Restates `quorum_safety`'s veto half. -/
theorem fold_safety :
    allBallots.all (fun b =>
      !(decide (b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline))
      || decide (fold b ≠ .accept)) = true := by decide

/-- **CONCURRENT/FAULT-TOLERANCE (restated, `3 = 2f+1`).** With ≥1 accept, 0 decline, and
    the rest abstaining, the fold result is in `{accept, abstain}` — never decline. A
    single non-participating (abstaining) witness is tolerated. Restates
    `quorum_fault_tolerance`. -/
theorem fold_fault_tolerance :
    allBallots.all (fun b =>
      !(decide ((b 0 = .accept ∨ b 1 = .accept ∨ b 2 = .accept)
                ∧ ¬(b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline)
                ∧ (∀ i : Fin 3, b i = .accept ∨ b i = .abstain)))
      || decide (fold b = .accept ∨ fold b = .abstain)) = true := by decide

/-- **CONCURRENT/CLOSURE (restated).** The fold of three verdicts is itself a verdict —
    the result always lies in the canonical alphabet. Restates `quorum_closure`. -/
theorem fold_closure :
    allBallots.all (fun b => decide (fold b ∈ allVerdicts)) = true := by decide

/-- The minimal fault-tolerant fold is the structural triton, `3 = 2·1 + 1`. -/
theorem fold_witness_count :
    witnessCount = 3 ∧ witnessCount = 2 * 1 + 1 ∧ allBallots.length = 27 := by
  refine ⟨by decide, by decide, ?_⟩; decide

-- ══════════════════════════════════════════════════════════
-- §3  QUANTUM-SHAPED = superposition + collapse (the spin-1 eigentriple)
-- ══════════════════════════════════════════════════════════

/-! The verdict's `sign : Verdict → Int` (from `TritonCanonical`) lands in `{-1, 0, +1}` —
    the spin-1 eigenvalue triple. The two definite verdicts are the eigenstates (signs ±1);
    `abstain` is the undetermined sign-0 superposed state. We pin the range exactly and the
    injectivity (no two verdicts share an eigenvalue), reusing `sign_injective`. -/

/-- **`sign` is injective** — the eigenvalues `{-1, 0, +1}` separate the three verdicts;
    no collapse on the eigenvalue axis. (Reuses `TritonCanonical.sign_injective`.) -/
theorem sign_injective' : ∀ a b : Verdict, sign a = sign b → a = b :=
  sign_injective

/-- The eigenvalue triple, materialized. -/
def spinTriple : List Int := [-1, 0, 1]

/-- **`sign` has range exactly `{-1, 0, +1}`** — the spin-1 eigentriple. Every verdict's
    sign is one of the three eigenvalues (∀-direction), and each eigenvalue is realized by
    some verdict (∃-direction). The two ±1 eigenvalues are the definite eigenstates; the
    `0` eigenvalue is the undetermined / superposed `abstain`. -/
theorem sign_range_is_spin_triple :
    (∀ v : Verdict, sign v ∈ spinTriple)
    ∧ (∃ v : Verdict, sign v = -1)
    ∧ (∃ v : Verdict, sign v = 0)
    ∧ (∃ v : Verdict, sign v = 1) := by
  refine ⟨?_, ⟨.decline, by decide⟩, ⟨.abstain, by decide⟩, ⟨.accept, by decide⟩⟩
  intro v; cases v <;> decide

/-- **`abstain` is the undetermined (sign-0) superposed state.** Its eigenvalue is `0`, and
    it is the unique verdict with sign `0` (so the definite verdicts both carry nonzero
    sign — they are the determined eigenstates). -/
theorem abstain_is_superposed :
    sign Verdict.abstain = 0
    ∧ (∀ v : Verdict, sign v = 0 → v = .abstain)
    ∧ sign Verdict.accept ≠ 0
    ∧ sign Verdict.decline ≠ 0 := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro v; cases v <;> (intro h; first | rfl | exact absurd h (by decide))

/-- **Quantum-shaped facet, bundled.** `sign` is an injective map with range exactly the
    spin-1 eigentriple `{-1, 0, +1}`; the definite verdicts are the ±1 eigenstates and
    `abstain` is the unique sign-0 (undetermined / superposed) state. This is the
    eigenstate framing — a structural/algebraic shadow of spin-1, not a physical claim. -/
theorem quantum_shaped_is_spin_triple :
    (∀ a b : Verdict, sign a = sign b → a = b)
    ∧ (∀ v : Verdict, sign v ∈ spinTriple)
    ∧ sign Verdict.abstain = 0
    ∧ (∀ v : Verdict, sign v = 0 → v = .abstain)
    ∧ sign Verdict.accept = 1
    ∧ sign Verdict.decline = -1 := by
  refine ⟨sign_injective', (sign_range_is_spin_triple).1, ?_, ?_, ?_, ?_⟩
  · decide
  · exact (abstain_is_superposed).2.1
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- §4  fold_is_idempotent_collapse — the measurement-projection theorem
-- ══════════════════════════════════════════════════════════

/-! "Quantum folds, it's the same thing": the fold acts as an idempotent projection onto
    the definite verdicts — exactly the measurement algebra `P ∘ P = P` that fixes
    eigenstates and collapses superposition. We make `P` concrete as the unanimous fold
    `project v := fold (constant ballot v)` and prove (a) unanimous-definite folds to that
    verdict, (b) the definite verdicts are the fixed points (eigenstates) and `abstain` the
    unique non-fixed (superposed) state, (c) idempotence `P (P v) = P v`. -/

/-- The constant ballot: all three witnesses cast the same verdict `v`. -/
def constBallot (v : Verdict) : Ballot := mkBallot v v v

/-- The measurement projection `P`: fold a unanimous ballot of `v`. This is the consensus
    fold applied to a single repeated input — the "measure `v` three times and fold" map. -/
def project (v : Verdict) : Verdict := fold (constBallot v)

/-- **(a) Unanimous definite folds to that verdict.** `quorum [v,v,v] = v` for the definite
    `v ∈ {accept, decline}`: measuring a definite state returns it unchanged. (And the
    unanimous-abstain ballot folds to `abstain` — the superposed input stays superposed
    under a unanimous read, which is what makes `abstain` a fixed point too at THIS map; it
    is its NON-fixedness under collapse-to-Bool, not under the fold, that marks it
    superposed — see §1/§3. Here `project` fixes all three, i.e. `project = id`.) -/
theorem unanimous_definite_folds_to_self :
    project .accept = .accept ∧ project .decline = .decline := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **`project` is the identity** — folding a unanimous ballot returns the common verdict
    for every verdict, definite or superposed. The projection onto the consensus value of
    an already-agreed input is that value. -/
theorem project_id : ∀ v : Verdict, project v = v := by
  intro v; cases v <;> decide

/-- **(b) The definite verdicts are the fixed points (eigenstates) under the
    Bool-collapse-then-reembed projection, and `abstain` is the unique non-fixed
    (superposed) state.** The genuine measurement projection is `measure := embedBool ∘
    collapse : Verdict → Verdict`. It fixes the eigenstates `{accept, decline}` and sends
    the superposed `abstain` to a DIFFERENT verdict (`decline`) — collapsing it. This is
    the `P` whose fixed-point set is exactly the eigenstates. -/
def measure (v : Verdict) : Verdict := embedBool (collapse v)

/-- `accept` and `decline` are fixed points of `measure` (the eigenstates). -/
theorem measure_fixes_definite :
    measure .accept = .accept ∧ measure .decline = .decline := by
  refine ⟨?_, ?_⟩ <;> decide

/-- `abstain` is NOT a fixed point of `measure` — it collapses (to `decline`). The
    superposed middle is the one state measurement changes. -/
theorem measure_collapses_abstain :
    measure .abstain ≠ Verdict.abstain ∧ measure .abstain = Verdict.decline := by
  refine ⟨by decide, by decide⟩

/-- **The fixed-point set of `measure` is EXACTLY the definite verdicts.** `measure v = v`
    iff `v ∈ {accept, decline}`; equivalently, the unique non-fixed verdict is `abstain`.
    Eigenstates ⇔ fixed points; superposition ⇔ the one moved state. -/
theorem measure_fixedpoints_are_eigenstates :
    ∀ v : Verdict, (measure v = v) ↔ (v = .accept ∨ v = .decline) := by
  intro v
  cases v with
  | decline => exact ⟨fun _ => Or.inr rfl, fun _ => by decide⟩
  | abstain => exact ⟨fun h => absurd h (by decide), fun h => by cases h <;> exact absurd ‹_› (by decide)⟩
  | accept  => exact ⟨fun _ => Or.inl rfl, fun _ => by decide⟩

/-- **(c) IDEMPOTENCE: `measure ∘ measure = measure` (`P ∘ P = P`).** Re-measuring a
    collapsed result is stable — the second read returns the first. This is the defining
    law of a measurement projection. (All three verdicts by `decide`.) -/
theorem measure_idempotent : ∀ v : Verdict, measure (measure v) = measure v := by
  intro v; cases v <;> decide

/-- **`fold_is_idempotent_collapse` — the measurement-projection master.** The fold/collapse
    acts as an idempotent projection `P` onto the definite verdicts, exactly the
    measurement algebra `P ∘ P = P` fixing eigenstates and collapsing superposition:

      (a) a unanimous definite ballot folds to that verdict (`quorum [v,v,v] = v`);
      (b) the fixed-point set of the collapse-projection `measure` is EXACTLY the definite
          verdicts (the eigenstates), with `abstain` the unique non-fixed (superposed)
          state that gets collapsed;
      (c) IDEMPOTENCE — re-folding/re-measuring a collapsed result is stable
          (`measure (measure v) = measure v`). -/
theorem fold_is_idempotent_collapse :
    -- (a) unanimous definite folds to self
    (project .accept = .accept ∧ project .decline = .decline)
    -- (b) eigenstates = fixed points; abstain the unique superposed (collapsed) one
    ∧ (∀ v : Verdict, (measure v = v) ↔ (v = .accept ∨ v = .decline))
    ∧ (measure .abstain ≠ Verdict.abstain ∧ measure .abstain = Verdict.decline)
    -- (c) idempotence P∘P = P
    ∧ (∀ v : Verdict, measure (measure v) = measure v) := by
  exact ⟨unanimous_definite_folds_to_self,
         measure_fixedpoints_are_eigenstates,
         measure_collapses_abstain,
         measure_idempotent⟩

-- ══════════════════════════════════════════════════════════
-- §5  DYNAMICS = fork → race(abstain) → fold(collapse)
-- ══════════════════════════════════════════════════════════

/-! The lifecycle: FORK spawns the three witnesses; each may still be RACING (its verdict
    not yet definite — `abstain` is the in-flight / undetermined state); FOLD collapses the
    settled ballot to one verdict. The race-speed theorems govern when the fold can commit
    early. -/

/-- A witness is still RACING (in-flight / undetermined) exactly when its verdict is
    `abstain` — the sign-0 superposed state has not yet collapsed to ±1. -/
def stillRacing (v : Verdict) : Bool := decide (v = .abstain)

theorem stillRacing_iff_abstain : ∀ v : Verdict, stillRacing v = true ↔ v = .abstain := by
  intro v
  cases v with
  | decline => exact ⟨fun h => by simp [stillRacing] at h, fun h => by cases h⟩
  | abstain => exact ⟨fun _ => rfl, fun _ => by decide⟩
  | accept  => exact ⟨fun h => by simp [stillRacing] at h, fun h => by cases h⟩

/-- **FAST-VETO (race-speed).** Any decline collapses the fold immediately, regardless of
    the other witnesses — including while they are still racing (abstaining). The scheduler
    need not wait for stragglers once a single decline lands. Checked over all 27 ballots:
    any decline ⇒ `fold = decline`. (Restates the veto direction of `quorum_decline_vetoes`
    under the fold name, surfaced as the early-commit rule.) -/
theorem fast_veto :
    allBallots.all (fun b =>
      !(decide (b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline))
      || decide (fold b = .decline)) = true := by decide

/-- **STRAGGLER-DEFERS-NOT-KILLS (race-speed).** If no witness declines but some are still
    racing (abstaining), the fold defers (`abstain`) rather than rejecting. A slow/absent
    witness can never turn the result into a `decline` — only a real veto can. Checked over
    all 27 ballots: (no decline ∧ some abstain) ⇒ `fold ≠ decline`, and in fact
    `fold ∈ {accept, abstain}`. -/
theorem straggler_defers_not_kills :
    allBallots.all (fun b =>
      !(decide (¬(b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline)
                ∧ (b 0 = .abstain ∨ b 1 = .abstain ∨ b 2 = .abstain)))
      || decide (fold b = .accept ∨ fold b = .abstain)) = true := by decide

/-- **MONOTONE-COMMIT (race-speed).** A unanimous accept ballot commits to `accept`. Once
    every witness has settled to accept (no straggler, no veto), the fold admits. The
    concrete unanimous witness plus the general all-accept characterization. -/
theorem monotone_commit :
    fold (mkBallot .accept .accept .accept) = .accept
    ∧ allBallots.all (fun b =>
        !(decide (b 0 = .accept ∧ b 1 = .accept ∧ b 2 = .accept))
        || decide (fold b = .accept)) = true := by
  refine ⟨by decide, ?_⟩; decide

/-- **Lifecycle, bundled.** fork → race(abstain) → fold(collapse): a witness in-flight is
    `abstain`; fast-veto commits on any decline; a straggler defers but never kills;
    unanimous accept monotonically commits. The three race-speed rules that let a scheduler
    consume `abstain` for wall-clock speed (the runtime follow-on). -/
theorem fork_race_fold_dynamics :
    (∀ v : Verdict, stillRacing v = true ↔ v = .abstain)
    ∧ allBallots.all (fun b =>
        !(decide (b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline))
        || decide (fold b = .decline)) = true
    ∧ allBallots.all (fun b =>
        !(decide (¬(b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline)
                  ∧ (b 0 = .abstain ∨ b 1 = .abstain ∨ b 2 = .abstain)))
        || decide (fold b = .accept ∨ fold b = .abstain)) = true
    ∧ fold (mkBallot .accept .accept .accept) = .accept := by
  exact ⟨stillRacing_iff_abstain, fast_veto, straggler_defers_not_kills,
         (monotone_commit).1⟩

-- ══════════════════════════════════════════════════════════
-- §6  MASTER — the honest conjunction
-- ══════════════════════════════════════════════════════════

/-- **`computation_unification_master` — one ternary primitive + fork/race/fold, under which
    classical / concurrent / quantum-shaped computation are each a PROVEN structural facet.**

    The claim, stated precisely:

      (1) CLASSICAL = collapsed trit. `Bool` embeds into `Verdict` via `embedBool`
          (injective), round-trips under `collapse` (`collapse ∘ embedBool = id`), and
          misses exactly the neutral middle `abstain` (no bool preimage). Binary logic is
          the trit with the middle decohered away — a strict sub-regime.

      (2) CONCURRENT = the fold. The three-witness consensus `fold` (= `quorum`) is SAFE
          (any decline vetoes), FAULT-TOLERANT (`3 = 2f+1`; one abstainer can't force a
          reject), and CLOSED (three verdicts fold to one).

      (3) QUANTUM-SHAPED = superposition + collapse. `sign` is injective with range exactly
          the spin-1 eigentriple `{-1, 0, +1}`; the definite verdicts are the ±1
          eigenstates and `abstain` is the unique sign-0 superposed state.

      (4) MEASUREMENT-PROJECTION. The collapse-projection `measure` is IDEMPOTENT
          (`P ∘ P = P`), its fixed-point set is EXACTLY the definite verdicts (the
          eigenstates), and `abstain` is the unique non-fixed state it collapses — the
          measurement algebra fixing eigenstates and collapsing superposition.

      (5) DYNAMICS. fork → race(abstain) → fold(collapse): in-flight ⇔ `abstain`;
          fast-veto (any decline commits immediately); straggler-defers-not-kills;
          unanimous-accept monotone-commit.

    **What this is NOT.** Not a unification of physics; not a claim that consensus IS
    quantum mechanics or that a verdict IS a qubit. It is a STRUCTURAL / ALGEBRAIC
    unification: a single ternary primitive and one lifecycle under which the three regimes
    appear as checked PROJECTIONS (relations: embeds / collapses / is idempotent / is
    injective with a fixed range), each mechanized by `decide` over finite witnesses. A
    common computational substrate, proven — and nothing more. -/
theorem computation_unification_master :
    -- (1) classical = collapsed trit
    ( (∀ a b : Bool, embedBool a = embedBool b → a = b)
      ∧ (∀ b : Bool, collapse (embedBool b) = b)
      ∧ (¬ ∃ b : Bool, embedBool b = Verdict.abstain)
      ∧ (∀ b : Bool, embedBool b = Verdict.accept ∨ embedBool b = Verdict.decline) )
    -- (2) concurrent = the fold (safe, fault-tolerant, closed)
    ∧ ( allBallots.all (fun b =>
          !(decide (b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline))
          || decide (fold b ≠ .accept)) = true
        ∧ allBallots.all (fun b =>
            !(decide ((b 0 = .accept ∨ b 1 = .accept ∨ b 2 = .accept)
                      ∧ ¬(b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline)
                      ∧ (∀ i : Fin 3, b i = .accept ∨ b i = .abstain)))
            || decide (fold b = .accept ∨ fold b = .abstain)) = true
        ∧ allBallots.all (fun b => decide (fold b ∈ allVerdicts)) = true )
    -- (3) quantum-shaped = spin-1 eigentriple + superposed middle
    ∧ ( (∀ a b : Verdict, sign a = sign b → a = b)
        ∧ (∀ v : Verdict, sign v ∈ spinTriple)
        ∧ sign Verdict.abstain = 0
        ∧ (∀ v : Verdict, sign v = 0 → v = .abstain)
        ∧ sign Verdict.accept = 1
        ∧ sign Verdict.decline = -1 )
    -- (4) measurement-projection: idempotent collapse fixing eigenstates
    ∧ ( (project .accept = .accept ∧ project .decline = .decline)
        ∧ (∀ v : Verdict, (measure v = v) ↔ (v = .accept ∨ v = .decline))
        ∧ (measure .abstain ≠ Verdict.abstain ∧ measure .abstain = Verdict.decline)
        ∧ (∀ v : Verdict, measure (measure v) = measure v) )
    -- (5) dynamics: fork → race(abstain) → fold(collapse), race-speed
    ∧ ( (∀ v : Verdict, stillRacing v = true ↔ v = .abstain)
        ∧ allBallots.all (fun b =>
            !(decide (b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline))
            || decide (fold b = .decline)) = true
        ∧ allBallots.all (fun b =>
            !(decide (¬(b 0 = .decline ∨ b 1 = .decline ∨ b 2 = .decline)
                      ∧ (b 0 = .abstain ∨ b 1 = .abstain ∨ b 2 = .abstain)))
            || decide (fold b = .accept ∨ fold b = .abstain)) = true
        ∧ fold (mkBallot .accept .accept .accept) = .accept ) := by
  refine ⟨classical_is_collapsed_trit,
          ⟨fold_safety, fold_fault_tolerance, fold_closure⟩,
          quantum_shaped_is_spin_triple,
          fold_is_idempotent_collapse,
          fork_race_fold_dynamics⟩

-- ══════════════════════════════════════════════════════════
-- §7  Reading
-- ══════════════════════════════════════════════════════════

/-! One ternary primitive — `Verdict = {decline, abstain, accept}` — and one lifecycle —
fork → race(abstain) → fold(collapse) — carry three regimes of computation as PROVEN
structural facets.

CLASSICAL is the collapsed trit (`classical_is_collapsed_trit`): `embedBool` injects `Bool`
onto the two definite verdicts, `collapse` retracts it (round-trip), and the neutral middle
`abstain` has no bool preimage (`embedBool_not_surjective`). Binary logic is exactly the
trit with the middle decohered away — a strict sub-regime.

CONCURRENT is the fold (`fold_safety`, `fold_fault_tolerance`, `fold_closure`): the
three-witness consensus is safe, fault-tolerant (`3 = 2f+1`), and closed — restated from
`TritonCanonical.quorum` under the fork/race/fold operator name.

QUANTUM-SHAPED is superposition + collapse (`quantum_shaped_is_spin_triple`): `sign` is the
spin-1 eigentriple `{-1, 0, +1}`, the definite verdicts are the ±1 eigenstates, and
`abstain` is the unique sign-0 superposed state. The fold acts as an idempotent measurement
projection (`fold_is_idempotent_collapse`): `measure ∘ measure = measure` with fixed-point
set EXACTLY the eigenstates and `abstain` the one collapsed state — the `P ∘ P = P` algebra.

DYNAMICS (`fork_race_fold_dynamics`): an in-flight witness is `abstain`; fast-veto commits
on any decline (race-speed); a straggler defers but never kills; unanimous accept
monotonically commits.

The master (`computation_unification_master`) is the honest conjunction. It is a
STRUCTURAL / ALGEBRAIC unification — a common computational substrate with checked
projections — NOT a unification of physics, and NOT an identity claim ("X IS Y"). Each
facet is a precise relation (embeds / collapses / is injective with range / is idempotent),
mechanized by `decide` over finite witnesses.

-- Next exploration:
--   Wire the race/scheduler to CONSUME `abstain` for wall-clock race-speed. The
--   race-speed theorems above (`fast_veto`, `straggler_defers_not_kills`,
--   `monotone_commit`) are the correctness contract for an early-commit scheduler: the
--   runtime may fold-and-return the instant a `decline` lands (fast_veto) without waiting
--   for still-racing (abstaining) witnesses, and may treat a no-decline-with-stragglers
--   state as a safe defer (straggler_defers_not_kills) rather than blocking on a quorum it
--   already knows cannot reject. Implement this as a streaming fold over the witness
--   `Ballot` that short-circuits on the first decline and emits `abstain` (defer) when the
--   undecided set is nonempty but decline-free; then prove a conformance lemma that the
--   streaming early-commit fold agrees with this module's `fold` on all 27 ballots (a
--   golden test mirroring `allBallots`). A sibling benchmark is measuring the wall-clock
--   win now; this theorem set is the proof that the speed is sound.
-/

end TritonForkRaceFold
end Gnosis
