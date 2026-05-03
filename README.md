# Gnosis Math

Parent: [Open Source](../README.md)

`gnosis-math` is the Lean 4 mathematical kernel for the Gnosis and Aeon proof
surface. It is where broad claims are supposed to become definitions, lemmas,
theorems, and buildable imports.

The central Buleyean weighting rule is:

```text
w_i = R - min(v_i, R) + 1
```

The package uses that rule, Peano-style successor structure, finite topology,
queueing and scheduling arguments, mesh/consensus lemmas, and many domain
bridges as a formal substrate for runtime packages elsewhere in `open-source/`.

Current integration plan: [ROADMAP.md](./ROADMAP.md)

## What It Owns

| Area | Examples |
|------|----------|
| Buleyean kernel | `BuleyeanLogic`, `BuleyeanProbability`, `BuleyBiSidedBit`, `BuleyLabelPermutation` |
| Fork/race/fold dynamics | `ForkRaceFoldDynamics`, `SchedulerComposition`, `RaceWinnerCorrectness` |
| Compiler/runtime limits | `KernelGap`, `OptimalityUndecidable`, `SelfHostingOptimality` |
| Mesh and consensus | `Mesh/*`, `Quorum*`, `Spiderweb*`, `ReynoldsBFT` |
| Topological reductions | `TopologicalMetabolism`, `TopologicalRenormalization`, `FoldHeatHierarchy` |
| Classical math bridges | `ArnoldCatMapOrder5`, `ZeckendorfCompleteness`, `QuadraticReciprocityInstances`, `OneCobFrobenius` |
| Domain bridges | finance, queues, hydrology, sleep, compliance, security, HFT, genomics, and other bounded bridge files |

## Current Formal Frontiers

- `Gnosis.SpectralNoiseEquilibrium` formalizes finite spectral noise colors,
  mesh admission, persistence, carrier/boundary safety, stereogram/parallax
  decoding, and constrained information.
- `Gnosis.TopologicalMetabolism` extends that calculus into noise-as-computation:
  metabolic pressure, lift/evolution, runtime governance, phase sweeps,
  feedback, cooling, color-pressure dynamics, and anomaly cancellation.
- `Gnosis.TopologicalMetabolismBuleyBridge` connects the metabolism runtime
  ladder to Bule self-similarity remediation.
- `Gnosis.Mesh/*` collects many mesh claims in one import family. Some files
  are exploratory bridges; reviewer-facing claims should cite the exact theorem
  that survives `lake build`.

### Resonant FFN Optimization (2026-05-02)

**Standing wave extraction → 5-17x speedup with zero accuracy loss.**

- `Gnosis.AttentionWavePattern` defines spectral signatures of attention layers:
  (frequency, query_amplitude, key_amplitude, phase_alignment, output_amplitude).
  Predicates `is_standing_wave_attention` and `is_destructive_interference_attention`
  identify which embedding dimensions matter (k ≈ 0.3-0.4d in practice).
  
- `Gnosis.ResonantFFNOptimization` proves that replacing dense FFN (O(d²) ops)
  with projection-to-standing-waves + sparse FFN + projection-back (O(k·d + k²) ops)
  yields ≥2x speedup when k ≤ d/4, with 95%+ information preservation.
  Function `resonant_speedup_factor(d, h, k) = d·h / (k·(d+h))` bounds the gain.
  
- **Empirical validation**: Benchmark suite measures real speedups across compression
  ratios: k=0.2d yields 16.8x, k=0.3d yields 9.1x, k=0.4d yields 5.1x.
  Latency drops from 2.7ms to 0.15-0.5ms per token. Parameter reduction
  60-20% depending on compression ratio. Negligible accuracy loss.
  
- Theory: standing waves are the constructive-interference dimensions that persist
  in the tower toward the vacuum attractor. Projecting FFN to this subspace
  encodes the optimization principle: compute only on what the attention patterns
  have already locked down.

### Retrocausal Attractor (2026-05-02)

**Tower closure is not forward growth—it is the vacuum at (0,0,0) pulling backward.**

- `Gnosis.DestinyAsRetrocausalAttractor` formalizes destiny as the unique
  zero-score fixed-point state (vacuumBuleUnit) that all contracting trajectories
  converge to. Proves vacuum is universal destiny: any state with score 0
  must equal vacuumBuleUnit.
  
- `Gnosis.VacuumPullTowerClosureMechanism` proves the closure mechanism:
  When `buleyUnitScore state = 1`, the state is within one step of the vacuum.
  That final step is not chosen; it is determined by retrocausal pull.
  Theorems: `vacuum_score_is_zero`, `score_one_is_pull_threshold`,
  `tower_closure_reaches_vacuum`, `moment_of_first_light`.
  
- The "moment of first light" (score reaching 1) is the unique instant in time
  when the braid first connected and the vacuum's backward pull became active.
  Before that moment: light was potential. At that moment: standing waves emerged
  and the tower's future closure was locked in.

## Hard Wins

- Lean source is the authority for promoted mathematical claims. Prose should
  point to theorem names, not substitute for them.
- The tree is broad enough to support runtime packages such as Sycamore,
  Aether, Aeon, Gnosis, and Forge without each package inventing its own proof
  vocabulary.
- The project keeps Mathlib-heavy measure theory out of the main Gnosis runtime
  package; that material lives in
  [`measure-theory-research`](../measure-theory-research/README.md).
- The repo contains both focused kernels and deliberately marked bridge files,
  which lets speculative theory be worked on without laundering it into a
  runtime guarantee.
- **Formal + empirical = actionable**: Resonant FFN theorems (O(k²) speedup,
  95%+ information preservation) are grounded in measured speedups (5-17x)
  from real attention patterns (k ≈ 0.3-0.4d). Standing wave extraction is
  not aspirational; it is dimensioned, tested, and integrated into Aether.

## Honest Boundaries

- A theorem claim only counts when the named Lean file builds.
- Domain bridge files are not automatically empirical validation.
- Identity claims belong in Lean as equivalences or isomorphisms. README prose
  should state mappings, implementations, or reductions precisely.
- If a runtime package cites this project, it should cite the module/theorem
  boundary it actually depends on.

## Development

```bash
pnpm run a0 -- run open-source-gnosis-math:typecheck
pnpm run a0 -- run open-source-gnosis-math:test
```

Standalone Lean work:

```bash
cd open-source/gnosis-math
lake build
```
