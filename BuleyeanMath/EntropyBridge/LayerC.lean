import Init

/-!
# EntropyBridge — Layer C policy

**Canonical prose:** [`README.md`](./README.md) in this directory (axiom vs `sorry`,
layer containment, pointers to `CryptographicExternalAxioms` / game layers).

This namespace is the designated home for **hardware- and deployment-facing**
interfaces: named axioms, `opaque` device parameters, and hypotheses that cannot be
discharged from Mathlib alone. Keep **conditional** crypto proofs in
`CryptographicPseudorandom` and related modules; put **world imports** here.

No `sorry` on this surface — use named `axiom`s with reviewable identifiers.
-/

namespace EntropyBridge

/-- Documentation anchor; concrete `opaque` / `axiom` pairs are added per deployment. -/
abbrev PolicyDoc : Unit := ()

end EntropyBridge
