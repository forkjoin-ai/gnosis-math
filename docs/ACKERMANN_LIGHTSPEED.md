# The Ackermann Ceiling Occupies the Role of c

A Lean-verified program formalizing the claim that the **Ackermann function is the
speed of light** — stated precisely (per the repo rule, never "X *is* the Y"): the
Ackermann growth ceiling **occupies the role of c**, the unique invariant frontier
separating the realizable (computable / causal) from the unrealizable
(super-primitive-recursive / acausal).

All modules are **Init-only** (no Mathlib / Batteries), **zero `sorry`**, and depend
only on the standard axioms `propext` + `Quot.sound` (the `native_decide` witnesses
additionally use `ofReduceBool`/`trustCompiler`).

Build gate (the full `Gnosis` ledger is pre-broken — build the chain head):

```
lake build Gnosis.AckermannIsLightSpeed
```

## The argument in one line

`computable` and `causal` are the same predicate, separated by a single **forced**
constant (c), **saturated** by light = information at the limit, with the **Ackermann
diagonal** as the frontier of the primitive-recursive ladder.

## Modules

| Module | Role |
|--------|------|
| `AckermannLightConeBridge` | The map `runtimeEvent T n = {time := A(n), space := T(n)}`; `certified_iff_in_lightcone` (computable ⟺ causal); saturation ⟺ lightlike; super-Ackermann ⟺ spacelike; the NP co-theorem (subluminal never reaches the front). |
| `AckermannUniversality` | The PR ladder: `hyperop 1/2/3 = +, ·, ^`. Records the universal obligation. |
| `AckermannMonotone` | **Discharges** the universal: `eventual_domination` — the diagonal eventually strictly dominates every fixed level (`hyperop k n n < A(n)` for `n ≥ k+3`). The full monotonicity tower, handling the irregular level-2 base `a·0=0`. |
| `InformationLightCone` | The keystone (light = information). Discrete Margolus–Levitin lattice causality: `info_within_cone` (info confined to `|x| ≤ t`), the photon rides the front, max info speed = c. |
| `ForcedLightConeEmbedding` | `slope_forced` — the cone slope (c) is the *unique* certificate-faithful conversion. c is pinned, not chosen. |
| `AckermannIsLightSpeed` | Capstone: `ackermann_ceiling_occupies_role_of_c` (five legs), `co_theorem_subluminal_never_catches_the_front`, `identityLedger`, `recorded_gap_discharged`. |
| `TimeTravelLightCone` | Closed timelike curves = spacelike = super-Ackermann. Chronology protection; `grandfather_paradox` (axiom-free); time travel ⟺ super-primitive-recursive growth. |
| `FrontierComputability` | Fixed PR levels are **eventually subluminal** (general form of the NP co-theorem, backed by `eventual_domination`). |
| `TimeDilation` | The twin paradox on the lattice: proper time = rest-step count; travel strictly reduces aging. |

## The five legs (capstone `ackermann_ceiling_occupies_role_of_c`)

- **(A) Bridge** — computable-certified ⟺ causal (in the future light cone).
- **(B) Saturation** — the Ackermann frontier lies exactly on the cone (lightlike).
- **(C) Forced** — the cone slope c is the unique certificate-faithful conversion.
- **(D) Keystone** — c = max information-propagation speed; the photon attains it.
- **(E) Ladder** — the sub-frontier levels are exactly succ / + / · / ^.

Plus `recorded_gap_discharged`: the universal (E-strengthening) is a theorem, not a
deferred obligation.

## Honest scope

Fully mechanized: all five legs, the universal domination, the time-travel and
time-dilation corollaries. **Cited, not mechanized** (Init-only Lean has no reals):
the continuum Margolus–Levitin step `ν_max · ℓ_P = c`. Leg (D) mechanizes its
discrete, dimensionless skeleton.
