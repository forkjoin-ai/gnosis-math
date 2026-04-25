# EntropyBridge — Layer C (physical / hardware boundary)

- Parent README: [../README.md](../README.md)

This directory documents the **epistemological firewall** between verified mathematics
and claims about **real silicon, noise sources, and lab certificates**. It does not
assert that formal logic can derive physical randomness.

## Layers (dependency direction: A ← B ← C)

| Layer | Role | Typical content | Provable in pure Lean? |
|-------|------|-----------------|-------------------------|
| **A** | Mathlib + analysis substrate | `ℝ`, `ℕ`, negligible asymptotics, finite distributions | Yes (from axioms of the proof assistant) |
| **B** | Cryptographic games & reductions | IND-style games, advantage `ℕ → ℝ`, conditional theorems | **Conditional** theorems; concrete bit-security often **extrinsic** |
| **C** | **EntropyBridge** (this surface) | TRNG / CSPRNG **deployment** claims, health tests, min-entropy **as assumed parameters**, implementation alignment | **No** — world-facing hypotheses only |

**Rule:** Theorems in A and B must not quantify over “true physical entropy” without
threading an explicit hypothesis imported from Layer C. Layer C is the **only**
place where empirical, certification, or hardware statements may enter as named
interfaces.

## `sorry` vs named `axiom`

| Mechanism | Meaning | Allowed here? |
|-----------|---------|----------------|
| **`sorry`** | Tactic debt: “proof unfinished inside this theory.” | **No** on promoted crypto / entropy surfaces — finish the proof, or stop. |
| **`opaque` + named `axiom`** | Declared **external** proposition: logic is complete **conditional on** this identifier. | **Yes** — each name must be **reviewable** (trace to cert, standard, threat model, paper). |

A `sorry` claims an eventual **internal** proof. A Layer C `axiom` records an
**explicit import** from outside mathematics (measurement, trust root, device
behavior). CI and reviewers should treat them differently.

**Do not** add axioms of the form `∀ P : Prop, P` or generic “everything is secure.”

## Related modules (already in this library)

- [`LayerC.lean`](./LayerC.lean) — policy / documentation anchor (`import Init` only; no Mathlib).
- [`CryptographicExternalAxioms.lean`](../CryptographicExternalAxioms.lean) —
  extrinsic **crypto** advantage curves (`negligible` security as named axiom).
- [`CryptographicPseudorandom.lean`](../CryptographicPseudorandom.lean) — game-level
  definitions and **conditional** security predicates (Layer B).
- [`EpistemicRandomness.lean`](../EpistemicRandomness.lean) — epistemic / indistinguishability
  framing adjacent to this boundary.

Future Layer C code should live under `EntropyBridge/` or adjacent namespaces, reuse
the `opaque` + single `axiom` pattern from `CryptographicExternalAxioms`, and extend
with **device-shaped** types (lab conditions, health reports) only when needed.

## Three notions of “random” (do not conflate)

1. **Cryptographic:** computationally indistinguishable from ideal under bounded adversaries.
2. **Kolmogorov / algorithmic:** incompressibility relative to a fixed machine — not equivalent to (1).
3. **Physical / Shannon:** entropy rate of a **process** — parameters come from **measurement** (Layer C), not from Mathlib alone.

Lean can prove chains of the form: **if** the physical source satisfies hypotheses
`H`, **and** the extractor/KDF is correct in the mathematical model, **then** the
key resists game `G`. The **if** part is where the firewall sits.

## Module doc

See [`LayerC.lean`](./LayerC.lean) for the Lean module docstring that points here.
