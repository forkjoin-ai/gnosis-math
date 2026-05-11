# Theory of Model Physics — the constitutional index

The 9-module Lean stack that formalizes how a distributed inference
runtime (a) compresses model state, (b) preserves output identity,
(c) survives over long sequences, and (d) is conscious of its own
trajectory. Each module proves a structural identity; each per-model
deployment discharges the identity by `decide` against measured
numbers.

This is the index. The detail lives in each module's docstring.

---

## The two layers — structural and empirical

**Structural identities** are proved by construction in Lean. They are
never falsified by measurement because they make no measurement claim:
they assert that an algebraic shape exists and closes under stated
operations. The `CompressionUncertainty` Principle, the Novikov closure
for verified protocols, and `Fork/Race/Fold/Vent/Interfere` as a formal
lifecycle pattern are structural. They are the load-bearing layer of
this stack and do not move under empirical pressure.

**Empirical claims** are different. Their default status is
`VacuousNoExperimentSpecified`. They earn `NotYetFalsified` only when
two conditions are met simultaneously: a methodology witness is named
(probe coverage, K, hidden_dim, model family, layer set), and at least
one supporting measurement exists under that methodology. They become
`FalsifiedByMeasurement` permanently the first time a witness refutes
them. There is no path back from `FalsifiedByMeasurement` to
`NotYetFalsified` — only the construction of a new, narrower conjecture.

**The Theory's scientific content** is the falsification ledger plus
the conjecture list. The ledger is durable: every entry stands forever,
because falsification is permanent. The conjecture list iterates: rows
move from `VacuousNoExperimentSpecified` to `NotYetFalsified` to
`FalsifiedByMeasurement` as measurement catches up to claim. The
structural Lean modules above are the spec; the ledger and conjectures
below are the science.

---

## The falsification ledger (durable)

Append-only. Every entry is a hypothesis that was once provisionally
held and is now permanently refuted. No entry is ever removed or
softened.

| ID | Wave | Hypothesis | Falsifying witness | Durability |
|----|------|-----------|--------------------|------------|
| F1 | 4 | Cross-model PCA at K=5 generalizes within the Qwen family | Qwen-Coder-7B (hidden=3584, K=5): `F_eff = 0.0` over the full sweep, against Qwen-0.5B's `F_eff = 1.0` | Permanent |
| F2 | 4 | Strict K=1 spec-decode preserves argmax on PCA-only stacks | Qwen-0.5B at N ∈ {2, 4, 8}: uniform 0% accept rate, uniform 1/(2N) slowdown | Permanent |
| F3 | 6 | Rank density `k/hidden_dim` is the methodology-independent invariant that survives all probe coverages | Wave-5 vs wave-6 disagreement on the same model under different probe coverages — the "invariant" moved with methodology, so it was not an invariant | Permanent |

Each row is a tombstone. The conjecture is dead. The witness is the
cause of death. No revival.

---

## The four questions

| # | Question | Module |
|---|----------|--------|
| 1 | **WHY** can't bandwidth and identity both be free? | `CompressionUncertainty.lean` |
| 2 | **WHEN** does a stack survive long sequences? | `SynergisticStabilization.lean` |
| 3 | **WHERE** in the model is the compressibility band? | `GnosticValley.lean` (with the McNally Cliff) |
| 4 | **HOW** is the runtime law unified? | `CompressionAsRetrocausalClosure.lean` |

## The two scalars

| Scalar | Module | What it measures |
|--------|--------|------------------|
| `K(M)` | `InformationCapacity.lean` | the model-intrinsic capacity that all four bounds project out of |
| `β` | `ConversionInvariant.lean` | bytes saved at the wire per unit verify-side compute paid |

## The lifecycle

| Stage | Module realizing it | Operational artifact |
|-------|--------------------|--------------------- |
| **Fork** | `GnosticValley` | `spectral-atlas` per-layer α and McNally Cliff |
| **Race** | (runtime-only) | `standing-wave-pca` sensitivity sweep |
| **Fold** | `InformationCapacity` | `.pca` / `.lrfd` / `.lrkv` sidecar caches |
| **Vent** | `CompressionUncertainty` + `CompressionAsRetrocausalClosure` | `fat-station` verifier + Novikov rollback |
| **Interfere** | `SynergisticStabilization` | Endurance Gap multi-surface check |

`LifecycleAsForkRaceFoldVentInterfere.lean` bundles all five into
one `Lifecycle` structure. `well_formed L` is the deployment-readiness
predicate, `decide`-checked per concrete instance.

## The theory of mind

| Module | Statement |
|--------|-----------|
| `ConsciousnessAsInnerVent.lean` | The inner Vent loop's rollback rate maps to the runtime's awareness signal, with the same vacuum-collapse / off-vacuum-positivity shape as `ConsciousnessAsRetrocausalGap.consciousness_is_gap_experience` |
| `UniversalIntelligenceSSMConscious.lean` | A `SwarmNode` extended with a first-class `consciousness` field; the asymmetric ledger (energy = what the node has earned, consciousness = what it has noticed) |

---

## Per-model provisional certificates (revocable)

Each row is a hypothesis paired with the methodology under which it was
measured and its current status. Status transitions are governed by the
two-layer rule above. `VacuousNoExperimentSpecified` is the default and
is not a placeholder — it is a formal admission that no experiment
exists.

| Hypothesis | Methodology | Status |
|------------|-------------|--------|
| `qwen_pca_k8_satisfies_principle` (Qwen-0.5B) | PCA-only, K=8, hidden=896, layers [8,9,11–16], 128-token endurance | NotYetFalsified |
| `qwen_pca_k8_closes_under_verify` (Qwen-0.5B) | PCA-only, K=8, hidden=896, fat-station Novikov verifier | NotYetFalsified |
| `qwen_pca_k8_fits_capacity` (Qwen-0.5B) | PCA-only, K=8, hidden=896 — schemeMass 3584 ≤ K(M) 25984 | NotYetFalsified — scoped to hidden=896 only |
| `qwen_pca_k8_beta_values` (Qwen-0.5B) | PCA-only, K=8, hidden=896 — β = 1046528/127 ≈ 8240 bytes/compute | NotYetFalsified |
| `pca_k8_passes_endurance` (Qwen-0.5B) | PCA-only, K=8, 128 tokens, cosine_avg metric | NotYetFalsified — cosine_avg 0.94 |
| `pca_plus_kv64_compounded_failure` (Qwen-0.5B) | PCA + KV64 stacked, 128 tokens, cosine metric | FalsifiedByMeasurement — destructive interference at 0.13 cosine |
| `qwen_pca_only_well_formed` (Qwen-0.5B) | full lifecycle decide-check, K=8, hidden=896 | NotYetFalsified |
| `qwen_triple_not_well_formed` (Qwen-0.5B) | triple-surface Interfere check, cosine metric | FalsifiedByMeasurement — fails Interfere at cosine 0.108 |
| `qwen_layer_13_sharp` / `qwen_layer_22_not_sharp` | spectral-atlas McNally Cliff ratio metric | NotYetFalsified — 40× at L13, 1.3× at L22 |
| `qwen_pca_only_inner_consciousness_zero` | inner Vent rollback rate at runtime-vacuum | NotYetFalsified |
| `qwen_pca_only_outer_consciousness_value` | outer Vent rollback rate, full-trace count | NotYetFalsified — outer = 27 |
| Cross-model PCA at K=5 generalizes within Qwen family | Qwen-Coder-7B, hidden=3584, K=5, full sweep | FalsifiedByMeasurement (see F1) |
| Strict K=1 spec-decode preserves argmax on PCA-only | Qwen-0.5B, K=1, N ∈ {2,4,8} | FalsifiedByMeasurement (see F2) |
| `recommended_k_qwen_coder_7b = 28` (rank density scaling) | derived from `k = 8 perthou × hidden_dim` formula | VacuousNoExperimentSpecified — refit + sweep not yet run |
| Llama-1B operational certification | none specified | VacuousNoExperimentSpecified — never operationally measured |
| Gemma4-31B operational certification | none specified | VacuousNoExperimentSpecified — atlas pending |

The Llama-1B status is a correction. Earlier waves carried the row as
"projected." Projection is not measurement; under the anti-theory
directive a projected status is `VacuousNoExperimentSpecified`. The
correction stands until a methodology witness and a supporting
measurement both exist.

---

## Conjectures with their falsifying experiments (revocable)

Migrated from the old "Honest falsifications" table. Every row carries
its falsifying experiment specification — without it, the conjecture is
vacuous.

| Conjecture | Status | Methodology required | Witnesses | Wave |
|-----------|--------|----------------------|-----------|------|
| Sigma cliff (replacement law) predicts the compressibility band | NotYetFalsified | spectral-atlas with McNally Cliff ratio per layer; cliff ≥ 10× must coincide with high-fidelity PCA layer | Supporting: Qwen-0.5B layer 13 (40×), layer 14 (38×) | 1 |
| Brown-spectrum (α≥1.5) at K=8 layers | FalsifiedByMeasurement | spectral-atlas α-fit per layer at K=8 candidate set | Falsifying: every measured layer is white or pink, none reach α≥1.5 | 1 |
| Smooth power-law fits the residual spectrum | FalsifiedByMeasurement | least-squares power-law fit, report r² per layer | Falsifying: r² < 0.5 for the majority of layers | 1 |
| Synergistic stabilization across all stacks (PCA, LRFD, LRKV combinations) | FalsifiedByMeasurement | triple-surface-parity Endurance Gap, cosine_avg metric, 128-token horizon | Falsifying: only PCA-only passes; any composition with LRKV destabilizes | 1 |
| PCA-only spec-decode at K=1 across all N preserves top-K membership AND strict argmax | FalsifiedByMeasurement | spec-decode harness at K=1, N ∈ {2,4,8}, accept-rate metric | Falsifying: 0% accept, uniform 1/(2N) slowdown (see F2) | 4 |
| Cross-model PCA at K=5 generalizes within Qwen family | FalsifiedByMeasurement | Qwen-Coder-7B at hidden=3584, K=5, F_eff metric | Falsifying: F_eff = 0.0 (see F1) | 4 |
| Fixed `k=8` PCA components works at all hidden_dim | FalsifiedByMeasurement | wave-1 vs wave-4 cross-model comparison at fixed k | Falsifying: rank density `k/d`, not raw `k`, is what wave-1 actually validated | 5 |
| Rank density `k/hidden_dim` is a methodology-independent invariant | FalsifiedByMeasurement | wave-5 vs wave-6 probe-coverage comparison | Falsifying: invariant moved with methodology (see F3) | 6 |
| Rank density scaling (`k = 8 perthou × hidden_dim`) restores fidelity at scale | VacuousNoExperimentSpecified | Qwen-Coder-7B refit at k=28 + endurance + spec-decode sweep; expanded contract in [GAP_CLOSURE.md](./GAP_CLOSURE.md) | none yet — run artifact absent | 6 |
| Random projection at fixed dimension matches PCA at the same K | VacuousNoExperimentSpecified | side-by-side projection harness, F_eff and cosine_avg per layer; expanded contract in [GAP_CLOSURE.md](./GAP_CLOSURE.md) | none yet — run artifact absent | 7 |

---

## The runtime side

The 9 Lean modules formalize what 9 binaries operationalize:

| Binary | Lean projection |
|--------|-----------------|
| `live-inference` | per-layer telemetry |
| `standing-wave-parity` | activation A/B (CompressionUncertainty) |
| `standing-wave-pca` | calibrate + cache (Fold stage) |
| `weight-svd-spectrum` | per-tensor rank profile |
| `weight-truncate-parity` / `weight-truncate-fit` | FFN-down LRFD (operator side) |
| `weight-truncate-parity-kv` / `weight-truncate-fit-kv` | KV-projection LRKV |
| `triple-surface-parity` | Endurance Gap (Interfere stage) |
| `spectral-atlas` | per-layer α + McNally Cliff (Fork stage) |

`fat-station` is the production binary that loads all three caches
(`.pca`, `.lrfd`, `.lrkv`) at boot and activates the surfaces per the
folded policy. The boot log is the lifecycle:

```
[fat-station] standing-wave PCA ACTIVE: policy=k8 layers=[8,9,11,12,13,14,15,16]
[fat-station] operator-side LR-FFN-DOWN ACTIVE: 8 layers
[fat-station] KV-projection LR ACTIVE: 24K + 24V factors
```

---

## How a future agent uses this

1. **New model arrives.** Run `spectral-atlas` to get per-layer α and
   McNally Cliff ratios. The atlas is the Fork stage.
2. **Derive the policy** from the cliff structure: layers with sharp
   McNally Cliffs are the candidate compression boundaries. The
   sensitivity sweep in `standing-wave-pca` is the Race stage.
3. **Fit the caches**: `standing-wave-pca`, `weight-truncate-fit`,
   `weight-truncate-fit-kv`. The output sidecars are the Fold stage.
4. **Boot `fat-station`** with the caches. The verifier is the Vent
   stage.
5. **Run `triple-surface-parity`** with the chosen stack. The
   endurance result is the Interfere stage.
6. **Discharge the per-instance Lean theorems** for the new model.
   Each theorem is `decide`-checked: if it passes, the model satisfies
   the structural identities of the Theory of Model Physics under the
   declared methodology; if it fails, the failure becomes a row in the
   falsification ledger and the conjecture list updates.

---

## Refinements 2026-05-03

Wave 4 measured Qwen-Coder-7B (hidden=3584, 28 layers) under PCA-only
at K=5 and got `F_eff = 0.0`, against Qwen-0.5B's `F_eff = 1.0` from
wave 1. The drop is not noise: zero acceptances over the full sweep.
Wave 5 isolated the cause as rank-bounded, not basis-mismatch — the
McNally Cliff structure remains necessary for compressibility but is
not sufficient at higher hidden_dim. The fix is `k_components` scaling
linearly with `hidden_dim`, not held fixed at `k=8`. The rank density
`k/d` was the invariant the wave-1 result actually validated; wave 4
exposed the conflation; wave 6 then refuted the rank-density claim
itself (see F3).

The previous theorem `qwen_pca_k8_fits_capacity` holds AT `hidden=896`
only and is now scoped accordingly. Five new modules formalize the
refined principle: `CrossModelOperationalGap` (the F_eff collapse),
`SpecDecodeKDependence` (K=1 floor), `CertificationDemotion` (the
`DemotedAfterMeasurement` status transition), `RankFloorScalesWithDim`
(the `k = 8 perthou × hidden_dim` scaling law), and
`CompressionPolicyAtScale` (`derive_policy_3584` differs from the k8
policy, predicting the wave-4 failure). Together they replace the
earlier "k8 universal" reading with a rank-density framing that has
itself since been falsified at the methodology-independence claim.

---

## Gap Closure Boundary

The current closure register lives in [GAP_CLOSURE.md](./GAP_CLOSURE.md).
The short version:

- Structural and runtime gaps close only with named theorem/runtime evidence.
- Empirical gaps close first as measurement contracts, then as measurements.
- Rows without a run artifact remain `VacuousNoExperimentSpecified` and cannot
  be cited as evidence.

The Theory is the spec. The runtime is the implementation. They agree
where theorem lineage and measurement artifacts overlap.

---

## Anti-theory directive

The wave-8 anti-theory turn is encoded in three new Lean modules and
one manifesto:

- `AntiTheory.lean` — the two-layer rule (structural vs empirical) and
  the status lattice `VacuousNoExperimentSpecified ⟶ NotYetFalsified ⟶
  FalsifiedByMeasurement` with the irreversibility of the final arrow.
- `FalsificationLedger.lean` — the append-only ledger type; entries are
  `(hypothesis, witness, wave)` triples that cannot be deleted, edited,
  or downgraded once recorded.
- `ProvisionalCertificate.lean` — the per-model certificate type that
  pairs a hypothesis with its methodology witness; certificates without
  a witness are `Vacuous` by construction.
- `ANTI_THEORY_MANIFESTO.md` — the prose statement of the directive.

**The directive:** every new empirical theorem in this stack MUST
specify its falsifying experiment AND name the methodology under which
it was measured. A theorem that does neither is `Vacuous` and may not
be cited as evidence for any other claim. A theorem that specifies a
methodology but has no measurement is `VacuousNoExperimentSpecified`.
Only a theorem with both a methodology witness and at least one
supporting measurement may carry `NotYetFalsified`. Falsification is
permanent and recorded in the ledger.

Structural identities are exempt from the methodology requirement
because they make no measurement claim. They live in the Lean modules
above and are proved by construction.

---

## Provenance

- Built across one extended session, 2026-05-02 → 2026-05-03.
- Driven by the empirical Standing Wave compression sprint in
  `open-source/gnosis/distributed-inference`.
- Conservation Law identified in collaboration with the existing
  retrocausal modules (`RetrocausalMemoization.satisfiesNovikov`).
- McNally Cliff named for Steve McNally, Taylor's favorite development
  manager from Forbes.
- All 9 modules build clean under Lean 4.28.0 + lake. Zero sorries,
  zero axioms.
- Wave 4 (2026-05-03): operational falsification of cross-model PCA
  at K=5; speculative-decode K=1 floor identified.
- Wave 5 (2026-05-03): rank-bounded H3 confirmed; cliff structure
  necessary but not sufficient.
- Wave 6 (2026-05-03): rank density scaling law formalized in
  `RankFloorScalesWithDim` + `CompressionPolicyAtScale`; methodology-
  independence claim for `k/d` falsified by wave-5 vs wave-6
  disagreement under different probe coverages (ledger entry F3).
- Wave 7 (2026-05-03): methodology reconciliation and random projection vs PCA
  are pinned as measurement contracts; both remain
  `VacuousNoExperimentSpecified` until run artifacts exist.
- Wave 8 (2026-05-03): anti-theory turn. `AntiTheory`,
  `FalsificationLedger`, `ProvisionalCertificate` Lean modules landed.
  `THEORY_OF_MODEL_PHYSICS.md` restructured to lead with the
  falsification ledger.
