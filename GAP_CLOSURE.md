# Gnosis Math Gap Closure Register

Parent: [README.md](./README.md)

This register closes the ambiguity around "gaps" without upgrading any
unmeasured empirical claim. A gap is closed only when it has one of these
outcomes:

| Closure kind | Meaning | Required evidence |
|--------------|---------|-------------------|
| Structural closure | The claim is a Lean identity or finite theorem surface. | Named module/theorem that survives `lake build`. |
| Runtime closure | A runtime mirror enforces the theorem boundary. | Named implementation, tests, and theorem-lineage metadata. |
| Measurement-contract closure | The empirical question has a falsifying experiment pinned. | Methodology, metric, tolerance, corpus/model, and status. |
| Blocked empirical gap | The experiment is named but not run. | Status remains `VacuousNoExperimentSpecified`; no downstream citation as evidence. |

## Closed Structural And Runtime Gaps

| Gap | Closure | Evidence |
|-----|---------|----------|
| Anti-theory status ambiguity | Closed structurally. Empirical claims use `VacuousNoExperimentSpecified`, `NotYetFalsified`, or `FalsifiedByMeasurement`; no `Certified` status is available. | `Gnosis.AntiTheory`, `Gnosis.FalsificationLedger`, `Gnosis.ProvisionalCertificate`; see [ANTI_THEORY_MANIFESTO.md](./ANTI_THEORY_MANIFESTO.md). |
| Qwen-0.5B PCA-only policy provenance | Closed as provisional runtime evidence. | [THEORY_OF_MODEL_PHYSICS.md](./THEORY_OF_MODEL_PHYSICS.md) records methodology-bearing `NotYetFalsified` rows for PCA-only K=8, endurance, verifier closure, capacity, and beta values. |
| Cross-model fixed-K claims | Closed by falsification. | Ledger entries F1 and F2 permanently refute K=5 Qwen-family generalization and strict K=1 spec-decode preservation. |
| Rank-density methodology independence | Closed by falsification. | Ledger entry F3 records that `k/hidden_dim` moved with probe coverage and was not methodology-independent. |
| Attention-closure optimizer admission | Closed at theorem/runtime boundary. | `Gnosis.CosmicNoiseConnections`, `Gnosis.UniversalIntelligenceSSMClosure`, Aether attention-closure policy, distributed-inference Rust mirror, and `fat-station` benchmark endpoint carry theorem-lineage metadata. |
| Bi-sided bit encoding | Closed at theorem/runtime boundary. | `Gnosis.BuleyBiSidedBit`, `open-source/bitwise/bisided-bit.ts`, and distributed-inference `rknot/bitwise_fp48.rs` mirror the lane split and conservation rules. |
| Mesh observability reconstruction | Closed at theorem/runtime boundary. | `Gnosis.MeshReconstruction` / `HftRiskPathDemo` and `apps/mesh-verifier` implement the reconstruction and tripwire contract. |

## Measurement Contracts Now Pinned

These rows close the methodology gap. They do not close the empirical question
until the run exists.

| Claim | Methodology | Falsifies if | Current status |
|-------|-------------|--------------|----------------|
| `recommended_k_qwen_coder_7b = 28` rescues the Qwen-Coder-7B PCA failure. | Run `standing-wave-pca` on Qwen-Coder-7B with hidden dimension `3584`, `k=28`, the same layer/probe coverage used for F1 unless a new coverage is declared, then run endurance and spec-decode sweeps. | `F_eff = 0.0`, endurance cosine falls below the declared PCA-only threshold, or spec-decode accept rate remains at the K=5 failure floor. | `VacuousNoExperimentSpecified` until the run artifact exists. |
| K-widening rescues F1 at higher K. | Sweep Qwen-Coder-7B over an explicitly declared K grid, report `F_eff`, cosine average, accept rate, and runtime cost per K. | No K in the grid clears both fidelity and cost gates, or the clearing K exceeds the declared deployment budget. | `VacuousNoExperimentSpecified` until the sweep artifact exists. |
| Random projection matches PCA at fixed dimension. | Run side-by-side random projection and PCA at identical K, identical layers, identical calibration/test tokens, and identical evaluator. | Random projection trails PCA outside declared tolerance on `F_eff` or cosine average. | `VacuousNoExperimentSpecified` until the side-by-side artifact exists. |
| Methodology reconciliation for F3. | Repeat rank-density measurements across at least two probe coverages on the same model/layers and record whether the selected K/d remains stable. | K/d changes with probe coverage beyond declared tolerance. | Already falsified for the methodology-independent invariant; any replacement must be a narrower conjecture. |
| Llama-1B operational fidelity. | Declare model artifact, tokenizer, layer set, K policy, calibration/test token sets, evaluator, fidelity metric, and tolerance before running any atlas/parity sweep. | Any declared fidelity gate fails under that pinned methodology. | `VacuousNoExperimentSpecified`; no methodology artifact is committed. |
| Gemma4-31B operational certification. | Run `spectral-atlas` first, then derive a compression policy from measured cliff structure, then run parity/endurance under declared tolerances. | Atlas does not expose a policy-supporting cliff, or derived policy fails parity/endurance. | `VacuousNoExperimentSpecified`; atlas pending. |

## Remaining Anchor Debt

[ROADMAP.md](./ROADMAP.md) records `137` ledger-anchor modules that are not yet
live Init-only theorem modules. That gap is not closable by prose. It closes
one module at a time when a file leaves anchor status, compiles as a real
theorem module, and `lake build` stays green.

The next honest closure target remains `DiversityUnwound` or a post-linear /
frontier dependent, because it extends the already-restored
deficit/frontier/diversity chain without inventing a new dependency shape.

## Operational Rule

No runtime policy may cite a blocked empirical gap as evidence. It may cite:

- a structural closure,
- a runtime closure,
- a `NotYetFalsified` measurement row with methodology and artifact,
- or a `FalsifiedByMeasurement` row as a guardrail.

Anything else is a draft hypothesis.
