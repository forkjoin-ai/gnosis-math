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
