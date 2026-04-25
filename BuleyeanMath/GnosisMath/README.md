# GnosisMath (Init-only)

Parent: [BuleyeanMath README](../README.md)

- [`GnosisMathPrelude.lean`](./GnosisMathPrelude.lean) — `powNat` and core `Nat` lemmas.
- [`ListNat.lean`](./ListNat.lean) — extra `Nat`/`List` lemmas (Mathlib-shaped, `Init` proofs).
- [`Fibonacci.lean`](./Fibonacci.lean) — `fibZ` weights aligned with [`ZeckendorfFST.F`](../ZeckendorfFST.lean) (Init-only shadow).
- [`Basic.lean`](./Basic.lean) — barrel: prelude + `ListNat` + `Fibonacci`.

Consumers: [`MathSandbox`](../../MathSandbox.lean), [`Hyperoperations`](../Hyperoperations.lean).
