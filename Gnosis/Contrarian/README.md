# Contrarian

Parent: [Gnosis](../README.md)

`Gnosis/Contrarian/` contains small Lean anti-theorem modules. Each file states
an apparently inverted claim with explicit structure fields, then proves the
bounded consequence that follows from those fields.

## Current Focus

- [ContrarianAdversariesImprove.lean](./ContrarianAdversariesImprove.lean) -
  formalizes adversarial pressure as a strict improvement witness and proves
  that such pressure maps to instrumental friendship.

## Verification

Run the focused module check from `open-source/gnosis-math`:

```sh
lake build Gnosis.Contrarian.ContrarianAdversariesImprove
```

Run the aggregate check:

```sh
lake build Gnosis
```
