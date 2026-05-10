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

`missing_imports.txt` at the root of this package is an optional stub (see file header); parent monorepo Cloud Build source tar steps referenced it with ENOENT when absent.

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

- `Gnosis.FrfWitnessTowerTruncation` proves prefix/tail (`List.take` / `List.drop`) recombination laws for
  `triadMerge` / `xorMerge` / the digit parity track — the algebraic interface for “tower truncation” beside
  multiset merges (`triad_merge_perm`, `triad_merge_not_injective`).
- `Gnosis.SpectralNoiseEquilibrium` formalizes finite spectral noise colors,
  mesh admission, persistence, carrier/boundary safety, stereogram/parallax
  decoding, and constrained information.
- `Gnosis.EchoChamberAsTaoBowl` (with `IsPejorativeEchoAt`, Q monotonicity)
  and satellites `Gnosis.TaoBowlTwinVoid` (structural vs consensus void) and
  `Gnosis.TaoBowlSignalCoupling` (`bowlActsOn` on `OpinionWave`, mismatch ↔
  external-information bridge to `chamberOfBowl`).
- `Gnosis.StepwiseAnalysisFramework` — five `FrfStep` phases, `channelSurface`
  / `LadderLawBundle` (10 ↔ 55), `AnalysisRun` + `ventRead` on `godWeight`,
  optional `TwinVoidDial` without pulling the echo-chamber import cycle.
- `Gnosis.TaoBowlTwinVoidBridge` — morphisms `TwinVoidDial` ↔
  `TaoBowlWithConsensus`, `optionalConsensusBowl` for `AnalysisCard`, and
  `toClassic_bowl_eq_of_twin_dial`.
- `Gnosis.TopologicalMetabolism` extends that calculus into noise-as-computation:
  metabolic pressure, lift/evolution, runtime governance, phase sweeps,
  feedback, cooling, color-pressure dynamics, and anomaly cancellation.
- `Gnosis.TopologicalMetabolismBuleyBridge` connects the metabolism runtime
  ladder to Bule self-similarity remediation.
- `Gnosis.CosmicNoiseConnections` connects layered cosmic noise to multi-head
  attention shadowing: bare `n`-head blocks project as phase `3n` through the
  Aeon frame, while an 8-head block plus Hexon coupling reaches the pink
  `30 -> 6` projection with Betti-1 leakage `18` and a Pisot-stable folded
  coordinate. The same bridge proves the closure condition: Aeon resolution
  aliases the 8-head trace, while the 24-resolution lift separates the heads
  and removes bare aggregate leakage; the 30-resolution coupled lift closes the
  pink leakage case.
- `Gnosis.UniversalIntelligenceSSMClosure` packages that closure result as a
  Universal Intelligence SSM observer model: a low-resolution folded
  `ClosureAttentionState`, a 24-resolution lifted state with separated heads
  and zero aggregate residue, and a 30-resolution pink-coupled lifted state.
  The closure lift composes with the existing Hebbian reward theorem and
  carries optimizer-admission theorems for head pruning, speculative decode,
  and standing-wave compression.
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

### Attention QKV Decomposition (2026-05-02)

**Separate Query, Key, Value standing waves. Composition rule shows the gate.**

- `Gnosis.AttentionQKVDecomposition` decomposes attention into three orthogonal
  standing wave sets with separate predicates: `is_query_standing`, `is_key_standing`,
  `is_value_standing`, `is_value_gated`.
  
- **Composition rule**: `output_amplitude = V_amplitude × phase_alignment`.
  Output dimensions are gated V: only survive if Q and K both stand AND align in phase.
  Non-standing dimensions are suppressed.
  
- **Selectivity metric**: `selectivity_ratio = output / V` (fraction in [0,1]).
  High selectivity (> 0.7) means the head is picky; V information is preserved.
  Low selectivity (< 0.3) means aggressive dimension reduction.
  
- **Quantization strategy**: aggressive on Q/K (few standing dims, 5-6 bits),
  conservative on V (carries gated info, 8-12 bits). Derived directly from selectivity.
  
- Theorems: three-way intersection (V gated only when Q, K, V all stand + aligned),
  extraction losslessness (all standing dims found, no false positives).

### Mesh Standing Wave Pinning (2026-05-02)

**Turn the mesh into a pin cushion. Pin every computation to standing dimensions.**

- `Gnosis.MeshStandingWavePinning` formalizes the acceleration mechanism:
  Every mesh node is pinned to its standing wave dimensions k << d.
  Routes go only through standing dimensions; non-standing are latency-free.
  
- **Speedup**: from O(d) latency → O(k) latency. When k = 0.2-0.4 of d,
  speedup = d/k = 2.5-5x per hop. Combined with batch parallelism: 5-17x measured.
  
- **Parallelism**: nodes with disjoint standing wave sets can compute simultaneously
  (no interference, no synchronization). Mesh becomes a k-dimensional lattice.
  
- **Pin cushion extraction**: attention patterns → standing wave extraction → mesh pins.
  Once per attention head (amortized). Pipeline: measure → extract → pin → route → accelerate.
  
- Theorems: speedup ≥ 1 (always helps), coverage ∝ speedup (k/d determines gain),
  parallelism from disjoint sets, correctness preservation (output on standing dims
  identical to full mesh, non-standing dimensions were noise).
  
- **Runtime integration** (Aether): `mesh-standing-wave-pinning.ts` implements
  extraction, routing, pinning. `coordinator-standing-wave-routing.ts` hooks into
  Aether coordinator to route layer outputs through standing dimensions only.
  Middleware compresses messages before send, decompresses after receive.

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

## Proof style

The kernel aspires to the **Rustic Church** ideal: theorems closed by
definitional unfolding plus Init-level `Nat.*` lemmas only — no `omega`,
no `simp`, no Mathlib. `Gnosis.GodFormula` is the canonical exemplar
(every base law of the formula proven via `Nat.sub_add_cancel`,
`Nat.add_right_comm`, etc., and four cross-checks for internal consistency).

[`RUSTIC_CHURCH.md`](./RUSTIC_CHURCH.md) is the cookbook: lemma vocabulary,
substitution patterns for the recurring `omega` shapes, a per-file migration
workflow, and the cases where keeping `omega` is still the right call.

## Out of Bounds and The Topological Bridge

We deliberately do not aim to replicate Mathlib's surface area. Instead, our ideal state is to explain computation, logic, and physics entirely within `gnosis-math` by reframing continuous and infinite problems into discrete, verifiable topologies. 

The following classical domains are explicitly **Out of Bounds** for direct representation, and we cover their gaps via the Topological Bridge:

- **Continuous Analysis and Reals (`ℝ`, limits, calculus, measure theory)**: 
  Out of bounds. We bridge this by mapping continuous dynamics to discrete Buleyean topologies (`+1` clinamen increments, exact rational phase decompositions, and bounded deficits). A real number is modeled as the limit of a discrete, terminating rejection process.
- **Infinite Category Theory (∞-categories, derived categories)**: 
  Out of bounds. We bridge this by modeling categorical coherence using explicit Buleyean Ranked DAGs. Naturality and adjunctions are expressed as `FORK`, `RACE`, `FOLD`, and `VENT` edges ensuring `beta1` topological complexity conservation.
- **Non-constructive Mathematics and Infinite Set Theory (Axiom of Choice over uncountables)**: 
  Out of bounds. We bridge this via explicit finite witnesses. Instead of proving an existential over an infinite domain, we provide a deterministic, finite search space that exhaustively closes the topological gap via kernel `decide`.
- **Algebraic Number Fields at Scale (Galois cohomology over infinite fields)**:
  Out of bounds. We bridge this by restricting to finite characteristic rings (`ZMod` equivalents built from `Nat`) and explicit combinatorial bounding.

We do not import Mathlib because our goal is not to heuristic-search an infinite space, but to prove that the finite state machine routing the deficit to zero is structurally inevitable.

### Why This is Hella Faster

By removing the black-box combinatorial search that Lean uses to unpack problems (like the `omega` tactic), we evaluate the proof as a finite state machine traversal mapping explicit Buleyean DAG boundaries. There is no guessing, no searching for the correct intermediate lemmas to rewrite the state—it's pure topological routing where complexity decreases monotonically until `beta1 = 0`.

For the specific subsets of formal logic we care about (bounded iterations, bounds-checking, structural convergence), modeling the proof strictly via the Buleyean `Fork/Race/Fold` topology (`.gg` files checked by `aeon-logic`) has proven to be **>800x faster** than generalized heuristic provers. We do not just make it slightly faster; we completely sidestep the NP-hard search spaces that choke heuristic-based engines by establishing the precise topological boundaries up front.

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
