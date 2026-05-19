# Contrarian

Parent: [Gnosis](../README.md)

`Gnosis/Contrarian/` contains small Lean anti-theorem modules. Each file states
an apparently inverted claim with explicit structure fields, then proves the
bounded consequence that follows from those fields.

## Current Focus

- [ContrarianAdversariesImprove.lean](./ContrarianAdversariesImprove.lean) -
  formalizes adversarial pressure as a strict improvement witness and proves
  that such pressure maps to instrumental friendship.
- [ContrarianDominantAttentionIsInnocent.lean](./ContrarianDominantAttentionIsInnocent.lean) -
  proves that high attention mass is not the taxable offense under
  `SkyrmsEnergyTax`; a zero-externality dominant head pays only the clinamen
  floor, while a lower-attention harmful head pays more.
- [ContrarianOracleSpeedupIllusion.lean](./ContrarianOracleSpeedupIllusion.lean) -
  formalizes a finite Fork/Race/Fold entropy certificate and proves that a
  zero classical deficit gives modeled oracle speedup multiplier `1`; under the
  same unit-depth normalization, physical quantum hardware has no strict
  computational value over the certified FOIL profile. It also provides the
  `industry_apotheosis` certificate: a zero-deficit non-associative phyle
  strictly dominates a positive-deficit associative legacy monolith while
  preserving the monolith's inverse-Bule entropy-overrun witness. Its
  static-prover/edge-verifier section models Lean proof generation as a heavy
  artifact, compresses that artifact to a succinct admission proof, and proves
  that the edge gate preserves zero deficit and multiplier `1`. The
  `FoilEdgeRuntime` gatekeeper contract proves WebGPU dispatch remains
  inaccessible until the WASM-style admission gate accepts the succinct
  certificate.

## Verification

Run the focused module check from `open-source/gnosis-math`:

```sh
lake build Gnosis.Contrarian.ContrarianOracleSpeedupIllusion
```

Run the aggregate check:

```sh
lake build Gnosis
```
