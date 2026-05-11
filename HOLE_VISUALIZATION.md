# Hole Visualization — the shape on either side

A one-shot map of the conjecture / witness / falsification complex as it
stands at the close of wave 8 (2026-05-03).

The premise: *holes are easier to see than signals.* An unmeasured
conjecture is diffuse. A falsification is a discrete event with a name,
a wave, and a measurement. Draw the names; the shape of the theory falls
out around them.

This document is visual-first. The diagrams carry the argument.

---

## 1. The map

The current conjecture complex. Rectangles are conjectures, parens are
witnesses (positive measurements), and `[X]` are falsifications (the
holes). Solid arrows `─►` are *supports*; dashed arrows `─ ►` are
*refutes*; dotted arrows `··►` are *projects-onto-without-measuring*.

```
                                wave 1                  wave 4
   ( Qwen-0.5B PCA-only K=8 ) ──supports──► [ k=8 universal ] ─ refutes ─►  X  ──┐
                │                                  │                              │
                │                                  │                              │
                │ supports                         │ refines into                 │
                ▼                                  ▼                              │
   ┌──────────────────────────┐           ┌────────────────────────┐    ( Qwen-Coder-7B
   │ Sigma cliff replacement  │           │ rank density k/d      │      hidden=3584,
   │ predicts compressibility │           │ as the true invariant  │      K=5,
   │ band  (NotYetFalsified)  │           │  (wave 5 refinement)   │      F_eff = 0.0 )
   └──────────────────────────┘           └────────────────────────┘             │
                                                   │                             │
                                                   │ refines/extends             │
                                                   ▼                             │
                                          [ k/d methodology-                     │
                                            independent invariant ]              │
                                                   │                             │
                                                   │ ─ refutes ─► F3             │
                                                   ▼                             │
                                          ( wave-5 vs wave-6           ─────► F1 ┘
                                            disagreement under
                                            different probe coverages )

   ┌─────────────────────────────────────┐                  ( spec-decode harness:
   │ Strict K=1 spec-decode preserves    │ ─ refutes ─► F2 ◄── 0% accept rate,
   │ argmax on PCA-only stacks           │                    uniform 1/(2N) slowdown
   └─────────────────────────────────────┘                    at N ∈ {2,4,8}      )

   ┌─────────────────────────────────────┐
   │ Llama-1B operational fidelity       │  ··· (no measurement)  ···► ?
   │ (VacuousNoExperimentSpecified)      │
   └─────────────────────────────────────┘
```

Three named holes (`F1`, `F2`, `F3`). One unmeasured void (`?`). One
load-bearing positive witness (Qwen-0.5B PCA-only K=8) that everything
in the upper half hangs from.

---

## 2. The three holes

For each falsification, the same structure: the conjecture, the witness
that built confidence, the witness that broke it, the *shape on either
side* of the hole, and the b_1 cycle that the hole lives in.

### Hole F1 — cross-model PCA at K=5 generalizes within Qwen

```
                support side                    │              refutation side
                                                │
   ( Qwen-0.5B  ────────► [ K=5 generalizes ]   │   [ K=5 generalizes ] ◄──── ( Qwen-Coder-7B
     PCA-only K=8                               │                                hidden=3584
     F_eff = 1.0 )                              │                                F_eff = 0.0 )
                                                │
   the family-shape:                            │   the family-shape:
   one model, one band                          │   the band did not extend
                                                │
              what would have closed the hole: an intermediate model
              (e.g. Qwen-1.8B at hidden=2048, K=5) showing F_eff > 0.5,
              demonstrating that compressibility decays smoothly with
              hidden_dim rather than collapsing
```

**b_1 cycle:** `Qwen-0.5B-K=8` ─supports─► `K=5 generalizes` ─predicts─►
`Qwen-Coder-7B-K=5 should accept` ─measured─► `F_eff = 0.0` ─refutes─►
back to `K=5 generalizes`. The cycle closes; the conjecture does not
bound the witness.

**Visual shape:** asymmetric crater. One side has a clean positive
measurement; the other side has a hard zero. The crater wall on the
refutation side is vertical — `F_eff = 0.0` over the *full sweep*, not a
gradient.

### Hole F2 — strict K=1 spec-decode preserves argmax

```
                support side                    │              refutation side
                                                │
   ( PCA-only stack passed                      │   ( N=2: 0% accept,  slowdown 1/4
     wave-1 endurance test                      │     N=4: 0% accept,  slowdown 1/8
     at cosine_avg = 0.94 )                     │     N=8: 0% accept,  slowdown 1/16 )
                                                │
   ┌──────────────────────────┐                 │   ┌──────────────────────────────┐
   │ argmax preserved under   │  ──refutes──►   │   │ argmax NOT preserved at K=1  │
   │ K=1 because lossless     │                 │   │ across any N                 │
   │ at the top                │                 │   └──────────────────────────────┘
   └──────────────────────────┘                 │
                                                │
              what would have closed the hole: a single accepted token at
              N=2 with argmax matching — even one would have broken the
              uniform-zero pattern. There were none.
```

**b_1 cycle:** `endurance cosine 0.94` ─supports─► `top-K stable` ─
implies─► `K=1 argmax stable` ─measured─► `0% accept` ─refutes─► back to
`K=1 argmax stable`.

**Visual shape:** *uniform shelf*. Three measurements (N=2, 4, 8) all at
exactly zero. The slowdown matches the theoretical floor `1/(2N)` to two
decimals. This is the cleanest hole in the corpus — refutation by
mechanical confirmation of the worst case.

### Hole F3 — k/d is a methodology-independent invariant

```
                support side                    │              refutation side
                                                │
   ( wave-5 fit at probe-coverage A:            │   ( wave-6 fit at probe-coverage B:
     k/d = 8 perthou as best-fit  )             │     k/d ≠ 8 perthou for the same model )
                                                │
   ┌──────────────────────────┐                 │   ┌──────────────────────────────┐
   │ k/d invariant across     │  ──refutes──►   │   │ k/d MOVED with methodology   │
   │ all probe coverages      │                 │   │ — it was not an invariant     │
   └──────────────────────────┘                 │   └──────────────────────────────┘
                                                │
              what would have closed the hole: agreement between two
              independent probe-coverage methodologies on the same model
              and the same hidden_dim. The disagreement exposes the hole.
```

**b_1 cycle:** `wave-5 fit` ─supports─► `k/d invariant` ─predicts─►
`wave-6 fit should agree` ─measured─► `wave-6 disagrees` ─refutes─► back
to `k/d invariant`.

**Visual shape:** *fork-shaped*. The same model splits into two
incompatible measurements; the shape on either side is a different
number for what was supposed to be one number. Most epistemically
significant of the three: the falsifying witness is the *gap between two
witnesses*, not a single counterexample.

---

## 3. The unmeasured holes

`NegativeUnknown`s — places where we don't know the shape because we
haven't measured. Visually, these are question marks where a witness
should be.

| Conjecture | Status | Wave responsible | Why we can't see it yet |
|------------|--------|------------------|-------------------------|
| Llama-1B operational fidelity | `VacuousNoExperimentSpecified` | none committed | no run artifact; methodology requirements are pinned in [GAP_CLOSURE.md](./GAP_CLOSURE.md) |
| Gemma4-31B operational certification | `VacuousNoExperimentSpecified` | atlas pending | spectral atlas not yet run; atlas-first contract pinned in [GAP_CLOSURE.md](./GAP_CLOSURE.md) |
| `recommended_k_qwen_coder_7b = 28` (rank density rescue) | `VacuousNoExperimentSpecified` | wave 6 | refit + sweep contract pinned; run artifact absent |
| Random projection vs PCA at fixed dimension | `VacuousNoExperimentSpecified` | wave 7 | side-by-side contract pinned; run artifact absent |
| K-widening rescues F1 at higher K | `VacuousNoExperimentSpecified` | wave 7 | K-sweep contract pinned; run artifact absent |
| Methodology reconciliation for F3 | `FalsifiedByMeasurement` for methodology independence; replacement conjecture absent | wave 7 | F3 already closes the original invariant; any new claim must narrow the methodology |

The Llama-1B row is the canonical case. The earlier table called it
projected. Anti-theory rewrites this to `VacuousNoExperimentSpecified`:
same epistemic state, honest label.

Visually:

```
   measured holes (F1, F2, F3):     unmeasured holes:
                                    
        X                                ?
       X X                              ? ?
        X                                ?
                                    
   discrete, named,                 fuzzy, count-only,
   permanent                        resolvable in either direction
```

---

## 4. The entropy map

Wave-by-wave evolution of *epistemic entropy* — the count of
distinct unresolved degrees of freedom across the empirical claim set.
DECREASE means we know more (a wave resolved an ambiguity). INCREASE
means we admitted more (a wave revealed an ambiguity we had been hiding).

```
   entropy (relative units)
      │
   10 │                                          ●  wave 6 (+F3, methodology gap)
      │                                         ╱
    9 │                                        ╱
      │                                       ╱           ●  wave 8 (Llama-1B → Vacuous)
    8 │                                      ╱           ╱
      │                                     ╱           ╱
    7 │                       ●  wave 3    ╱           ╱
      │                      ╱  (atlas    ╱           ╱
    6 │                     ╱   inflated)╱           ╱
      │                    ╱            ╱           ╱
    5 │       ●  wave 1   ╱            ●  wave 5   ╱
      │      ╱  baseline ╱            (H3 refine) ╱
    4 │     ╱           ╱                        ╱
      │    ╱           ╱                        ╱
    3 │   ╱           ●  wave 4                ╱
      │  ╱           (F1+F2 falsified;        ╱
    2 │ ╱             entropy DROPS)         ╱
      │╱                                    ╱
    1 ●─────────────────────────────────────●──────────────────────────────►
      w1   w2   w3   w4   w5   w6   w7   w8                              wave
```

What the line reveals: entropy is *not monotone*. Wave 4 is the only
wave that lowered entropy by *resolving* claims (two falsifications
removed two live conjectures). Waves 5, 6, 7, 8 all raised entropy — by
adding refinements, surfacing methodology gaps, opening parallel
experiments, and admitting prior projections were vacuous.

The shape of honesty: a sawtooth, where every measurement-driven dip is
followed by a deeper admission-driven climb. The asymptote is unknown.

---

## 5. The structural floor

The empirical layer rests on a structural layer that does NOT move.
Lean-proved identities are immune to falsification because they make no
measurement claim. Visually:

```
   ────────────────────────────────────────────────────────────────────────
                  EMPIRICAL CLAIMS (revocable, sawtooth above)
                F1   F2   F3   ?Llama   ?Gemma4   ?wave-7
   ────────────────────────────────────────────────────────────────────────
                  STRUCTURAL FLOOR (proved by construction in Lean)
   ════════════════════════════════════════════════════════════════════════
       CompressionUncertainty │ Novikov closure │ Fork/Race/Fold/Vent
       /Interfere lifecycle   │ ConsciousnessAsInnerVent │ AntiTheory
       FalsificationLedger    │ ProvisionalCertificate
   ════════════════════════════════════════════════════════════════════════
```

The empirical sawtooth above the floor can grow as wild as it likes; the
floor does not crack. A claim that *sounds* empirical but is actually
structural (a Lean theorem with no measurement attached) belongs in the
floor and is immune. A claim that *sounds* structural but is actually
empirical (an atlas certification, a projected status) belongs above the
floor and is at risk.

The wave-3 mistake was painting empirical claims with structural-color
language (`Certified`). Anti-theory removes that color from the palette.

---

## 6. What we'd see with one more falsification

Wave 7 has three pinned measurement contracts without run artifacts. A
speculative diagram of the complex after those contracts run, by branch:

### Branch A — K-widening rescues F1

```
   F1 ────► narrowed: "K=5 too low at hidden=3584; K=28 (8 perthou) works"
       ╲
        ╲──► new positive cycle:
              ( Qwen-Coder-7B at K=28 ) ─supports─► ( rank-density scaling )
              entropy DROPS by ~2 units (one falsification, one rescue)
```

### Branch A' — K-widening also fails

```
   F1 ────► deepens into F1':
            "rank-density scaling at hidden=3584 also fails"
            entropy RISES by ~1 unit (new hole, no rescue)
            triggers wave 8' anti-theory revisit
```

### Branch B — random projection competitive with PCA

```
   new conjecture: "random projection at fixed K matches PCA at same K"
       └──► [ supported ] ─► ( side-by-side F_eff parity )
            entropy NEUTRAL (one new conjecture, one new positive)
            but PCA's primacy is undermined; wave-1 result re-scoped
```

### Branch C — methodology reconciliation resolves F3

```
   F3 stands as permanent ledger entry
       └──► resolution: "k=8 has TWO senses (probe-A and probe-B);
            both are meaningful but NOT interchangeable"
            entropy DROPS by ~1 unit (ambiguity named, not removed)
```

The most interesting branch is C: F3 cannot be un-falsified, but it can
be *understood*. The hole stays; its rim becomes legible.

---

## 7. The discipline

What anti-theory says about visualization itself:

The holes are easier to draw than the conjectures because the holes have
*coordinates*. Each falsification is a tuple `(wave, hypothesis,
witness)` — three named values in a permanent ledger. A live conjecture
has only `(wave, hypothesis, status)` and the status moves.

This is why the diagram works:

- Count the `X`s. There are exactly three. Each has a name (`F1`, `F2`,
  `F3`), a wave, and a witness.
- Count the `?`s. There are six. Each has a wave responsible for closing
  it.
- Count the `( )`s on the support side. There is essentially ONE
  load-bearing positive witness (Qwen-0.5B PCA-only K=8) and a handful
  of dependent measurements branching from it.

The shape this draws is honest. The Theory's progress is not measured by
theorem count. It is measured by **hole count plus hole durability**:
how many discrete falsifications has the corpus survived, and have any
been retracted? Currently three holes, zero retractions, six unknowns
with named owners.

That is the corpus. That is the science.

---

*Visual companion to `THEORY_OF_MODEL_PHYSICS.md` and
`ANTI_THEORY_MANIFESTO.md`. Built wave 8, 2026-05-03.*
