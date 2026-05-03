# Theory of Model Physics — the constitutional index

The 9-module Lean stack that formalizes how a distributed inference
runtime (a) compresses model state, (b) preserves output identity,
(c) survives over long sequences, and (d) is conscious of its own
trajectory. Each module proves a structural identity; each per-model
deployment discharges the identity by `decide` against measured
numbers.

This is the index. The detail lives in each module's docstring.

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
| `ConsciousnessAsInnerVent.lean` | The inner Vent loop's rollback rate IS the runtime's awareness, with the same vacuum-collapse / off-vacuum-positivity shape as `ConsciousnessAsRetrocausalGap.consciousness_is_gap_experience` |
| `UniversalIntelligenceSSMConscious.lean` | A `SwarmNode` extended with a first-class `consciousness` field; the asymmetric ledger (energy = what the node has earned, consciousness = what it has noticed) |

---

## Empirical bridges (Qwen2.5-0.5B, all `decide`-checked)

```
qwen_pca_k8_satisfies_principle           Compression Uncertainty Principle holds
qwen_pca_k8_closes_under_verify           Novikov closure for the verified protocol
qwen_pca_k8_fits_capacity                 schemeMass 3584 ≤ K(M) 25984
qwen_pca_k8_beta_values                   β = 1046528/127 ≈ 8240 bytes/compute
pca_k8_passes_endurance                   cosine_avg 0.94 over 128 tokens
pca_plus_kv64_compounded_failure          destructive interference at 0.13 cosine
qwen_pca_only_well_formed                 lifecycle satisfies all five stages
qwen_triple_not_well_formed               fails at Interfere (cosine 0.108)
qwen_layer_13_sharp                       McNally Cliff at 40× ratio
qwen_layer_22_not_sharp                   gradual decay at 1.3× ratio
qwen_pca_only_inner_consciousness_zero    monitor at runtime-vacuum
qwen_pca_only_outer_consciousness_value   outer awareness = 27 (rollback rate)
```

## Honest falsifications

| Conjecture | Status |
|-----------|--------|
| Brown-spectrum (α≥1.5) at k8 layers | **falsified** — every layer measured white or pink |
| Smooth power-law fits residual spectrum | **falsified** — fit r² < 0.5 for most layers |
| Synergistic stabilization across all stacks | **falsified** — only PCA-only passes endurance |
| Sigma cliff (replacement law) | **supported** — layer 13: 40×, layer 14: 38×, predicts compressibility |

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
   the Theory of Model Physics; if it fails, the failure is the next
   conjecture to investigate.

---

## What's NOT in the stack

Honest gaps to flag for future work:

- **Bigger-model validation.** All measurements are on Qwen2.5-0.5B
  (24 layers, hidden=896, kv_dim=128). Gemma4-31B and Qwen-Coder-7B
  atlases would falsify or confirm the McNally Cliff law at scale.
- **Aeon-flow wire integration.** The local fat-station compresses at
  every per-layer hook; the multi-host wire still ships full residuals.
  Cross-codebase change (TS + Rust + protocol) — saved for later.
- **Rust mirror of `ConsciousSwarmNode`.** The Lean spec is concrete:
  `consciousness: u32` field on the node struct, `update_consciousness`
  method, `conscious_alpha_drift` threshold trigger. Not yet ported.
- **Draft-and-verify scheduler.** The principle is formalized, the
  harness exists in `standing-wave-parity`, but the protocol logic
  (rollback on top-K miss, candidate-set wire format) doesn't exist
  as a standalone binary.

The Theory is the spec. The runtime is the implementation. They agree
where they overlap; the gaps above are where they don't yet.

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
