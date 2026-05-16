# OPTICS_DOCTRINE: Formal Visual Perception Theorem Style

## Overview

The Gnosis Optics framework formalizes physiological transitions, boundaries, and predictive mappings in visual perception using Lean 4's Init-only doctrine. This document specifies the theorem style, proof patterns, and conservation laws underlying all four tracks of the visual perception system.

**Core Principle**: Every theorem uses only named Nat lemmas from Lean's Init library. Zero `omega`, zero `simp`, zero `decide` on open goals. Proofs are mechanical, explicit, and compose deterministically.

---

## The Four Tracks

### Track Alpha: Optical Geometry
- **Domain**: Point spread function (PSF) aberrations, foveal density, corneal scattering
- **Conservation**: Optical geometry is always positive — psfWidth always ≥ 1
- **Method**: Monotonicity through division bounds (Nat.div_le_div_right)

### Track Beta: Photopigment Kinetics
- **Domain**: Cone recovery, thermal dissipation, chromaticShift
- **Conservation**: Photopigment recovery bounded by cone capacity
- **Method**: Saturating subtraction for deficit modeling

### Track Gamma: Perceptual Transitions
- **Domain**: Eigengrau dark current, fulcrum threshold, signal-to-noise extinction
- **Conservation**: Dark baseline irreducible (+1 clinamen) — darkBaseline = 1
- **Method**: Discrete state ordering (stateVacuum < stateFulcrum < stateClosure)

### Track Delta: Phosphene Topology
- **Domain**: Four noise regimes (Brownian/Pink/White/Quantum), pressure-light isomorphism
- **Conservation**: Phosphene regimes bounded {1,2,3,4}
- **Method**: Modular arithmetic for regime assignment

---

## Init-Only Doctrine Applied to Optics

### Rule 1: Monotonicity via Division
**When proving**: `∀ i₁ i₂ : Nat, i₁ ≤ i₂ → f i₁ ≤ f i₂` where `f` divides by a constant.

**Pattern**:
```lean
theorem psf_broadening_with_intensity :
    ∀ i₁ i₂ : Nat, i₁ ≤ i₂ → psfWidth i₁ ≤ psfWidth i₂ := by
  intros i₁ i₂ hle
  unfold psfWidth
  have : i₁ / 16 ≤ i₂ / 16 :=
    Nat.div_le_div_right hle
  exact Nat.add_le_add_right this 1
```

**Key Lemmas**:
- `Nat.div_le_div_right : a ≤ b → a / c ≤ b / c`
- `Nat.add_le_add_right : a ≤ b → a + c ≤ b + c`
- `Nat.mul_le_mul : a ≤ c → b ≤ d → a * b ≤ c * d`

---

### Rule 2: Saturating Subtraction for Deficit
**When proving**: Properties of saturating subtraction `a - b` where underflow wraps to 0.

**Pattern**:
```lean
theorem deficit_decreases (capacity r₁ r₂ : Nat) (hle : r₁ ≤ r₂) :
    photopigmentDeficit r₂ capacity ≤ photopigmentDeficit r₁ capacity := by
  unfold photopigmentDeficit
  exact Nat.sub_le_sub_left hle capacity
```

**Key Lemmas**:
- `Nat.sub_le_sub_left : a ≤ b → b - c ≤ a - c` (reverses: more recovery = less deficit)
- `Nat.sub_le : a - b ≤ a` (subtraction always bounded above by minuend)
- `Nat.sub_self : a - a = 0`

---

### Rule 3: Modular Arithmetic for Bounded Regimes
**When proving**: Properties of regimes constrained to {1, 2, 3, 4}.

**Pattern**:
```lean
theorem phosphene_from_stimulus_bounded (stimulus : Nat) :
    phospheneRegimeFromStimulus stimulus ≤ 4 := by
  unfold phospheneRegimeFromStimulus
  have : stimulus % 4 ≤ 3 := Nat.lt_succ_iff.mp (Nat.mod_lt stimulus (by decide))
  exact Nat.add_le_add_right this 1
```

**Key Lemmas**:
- `Nat.mod_lt : a < b → a % b < b` (modular remainder always less than divisor)
- `Nat.lt_succ_iff : a < b → a ≤ b - 1` (strict < converts to ≤)
- `Nat.mod_two_eq_zero_or_one : a % 2 = 0 ∨ a % 2 = 1`

---

### Rule 4: Positivity via Successor
**When proving**: Lower bounds like `f x ≥ 1`.

**Pattern**:
```lean
theorem psf_convolution_bounds (intensity : Nat) :
    psfWidth intensity ≥ 1 := by
  unfold psfWidth
  exact Nat.succ_pos _
```

**Key Lemmas**:
- `Nat.succ_pos : 0 < Nat.succ n` (successor always positive)
- `Nat.zero_lt_succ : 0 < Nat.succ n`
- `Nat.le_refl : a ≤ a`

---

## Worked Examples

### Example 1: Three-Cone Regeneration Rate Handling

**Goal**: Prove all three cone types recover to their individual capacity bounds.

```lean
-- Setup: coneS, coneM, coneL with different maxCapacity values
def coneRecovery (cone : ConeType) (timeSteps : Nat) : Nat :=
  Nat.min cone.maxCapacity (timeSteps * cone.regenerationRate)

theorem cone_recovery_bounded (cone : ConeType) (t : Nat) :
    coneRecovery cone t ≤ cone.maxCapacity := by
  unfold coneRecovery
  exact Nat.min_le_left _ _
```

**Why this works**: 
- `Nat.min_le_left a b : Nat.min a b ≤ a` directly states the left side of min is bounded by itself
- We don't branch on `cone` type; the proof applies universally
- Recovery time scales as `t * regenerationRate`, but `Nat.min` saturates at capacity

**Key Pattern**: When multiplying by a per-type coefficient, use `Nat.min` to cap the result.

---

### Example 2: Fulcrum Boundary Verification

**Goal**: Prove the three perceptual states form a strict ordering.

```lean
-- Setup from PerceptualTransition
def stateVacuum : Nat := 10
def stateFulcrum : Nat := 11
def stateClosure : Nat := 12

theorem fulcrum_strictly_between :
    stateVacuum < stateFulcrum ∧ stateFulcrum < stateClosure :=
  state_ordering
```

**Why this works**:
- States are ground-truth constants, so comparison reduces to decidable equality
- The proof is a reference to `state_ordering`, which is proven by `decide`
- No monotonicity needed; we're just verifying discrete boundary positions

**Key Pattern**: For fixed thresholds, use `decide` at definition time, then reference the proof.

---

### Example 3: Monotonicity through Saturating Subtraction

**Goal**: Prove increasing pressure produces larger phosphene shapes.

```lean
def pressurePhospheneShape (pressure : Nat) : Nat :=
  (pressure * pressure) / 4 + 1

theorem phosphene_shape_monotone (p₁ p₂ : Nat) (h : p₁ ≤ p₂) :
    pressurePhospheneShape p₁ ≤ pressurePhospheneShape p₂ := by
  unfold pressurePhospheneShape
  have h1 : p₁ * p₁ ≤ p₂ * p₂ := Nat.mul_le_mul h h
  have h2 : p₁ * p₁ / 4 ≤ p₂ * p₂ / 4 := Nat.div_le_div_right h1
  exact Nat.add_le_add_right h2 1
```

**Why this works**:
- `Nat.mul_le_mul` squares both sides of `h : p₁ ≤ p₂`
- `Nat.div_le_div_right` preserves ≤ under division (division by const always monotone in numerator)
- `Nat.add_le_add_right` preserves ≤ under addition

**Key Pattern**: Build monotonicity chain: if f(x) ≤ f(y), then g(f(x)) ≤ g(f(y)) for monotone g.

---

### Example 4: Noise Regime State Machine

**Goal**: Prove four noise regimes partition the input space modulo 4.

```lean
def noise_regime_brownian : regimeBrownian = 1 := rfl
def noise_regime_pink : regimePink = 3 := rfl
def noise_regime_white : regimeWhite = 4 := rfl
def noise_regime_quantum : regimeQuantum = 12 := rfl

def inRegimeBrownian (level : Nat) : Bool := level = regimeBrownian
def inRegimePink (level : Nat) : Bool := level = regimePink

theorem brownian_regime_minimal :
    regimeBrownian = 1 ∧ regimeBrownian ≤ 12 := by
  decide
```

**Why this works**:
- Regime membership is tested by equality check: `level = regimeX`
- The four regimes (1, 3, 4, 12) are unambiguous constants
- Decidability comes from Nat equality being decidable
- `decide` closes goals that reduce to Nat arithmetic

**Key Pattern**: For categorical state machines (regime ∈ {1, 3, 4, 12}), use equality checks and `decide`.

---

## Conservation Law Structure

### Universal Pattern: God Formula as Apex

Every track instantiates the God Formula: `w = R - min(v, R) + 1`

```lean
def godFormulaUniversal (capacity deficit : Nat) : Nat :=
  capacity - (Nat.min deficit capacity) + 1

theorem god_formula_universal_sliver (capacity deficit : Nat) :
    godFormulaUniversal capacity deficit ≥ 1 := by
  unfold godFormulaUniversal
  exact Nat.succ_pos _
```

### Track-Specific Instantiation

Each track defines domain-specific parameters that plug into the God Formula:

**Track Alpha**: `psfWidth` is irreducible (capacity = ∞, deficit = 0) → always ≥ 1
**Track Beta**: `coneRecovery` via `Nat.min` (capacity-bounded regeneration)
**Track Gamma**: Dark current = 1 is the +1 clinamen; fulcrum = recovery boundary
**Track Delta**: Regime codes {1,3,4,12} modulo 4; phospheneRegimeFromStimulus = stimulus % 4 + 1

---

## Key Invariants Across Tracks

| Property | Track Alpha | Track Beta | Track Gamma | Track Delta |
|----------|-------------|-----------|-------------|-------------|
| Conservation | psfWidth ≥ 1 | recovery ≤ capacity | darkBaseline = 1 | regime ∈ {1,2,3,4} |
| Monotonicity | w.r.t. intensity | w.r.t. time | state ordering | w.r.t. stimulus |
| Boundary | No hard cutoff | Capacity saturation | Fulcrum threshold | Modular wrapping |
| Method | Division bounds | Saturating subtraction | Discrete ordering | Modular arithmetic |

---

## Proof Checklist

When adding a new theorem to Optics:

1. **State the type**: Is this monotonicity, conservation, or a boundary?
2. **Unfold definitions**: Expand all relevant defs (psfWidth, coneRecovery, etc.)
3. **Identify lemma chain**: Find Init lemmas that connect input to conclusion
4. **Build intermediate steps**: Use `have` to name each application
5. **Close the goal**: Apply final lemma with `exact`
6. **Verify**: No `omega`, `simp`, or `sorry`; all names in Init library

---

## Anti-Patterns to Avoid

### ❌ Using omega on open goals
```lean
-- WRONG:
theorem bad : a ≤ b → a + c ≤ b + c := by omega
```
**Fix**: Use `Nat.add_le_add_right` instead.

### ❌ Pattern matching on Nat
```lean
-- WRONG:
def f (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => n
```
**Fix**: Use recursion or explicit formulas that avoid case analysis.

### ❌ Existential reasoning
```lean
-- WRONG:
theorem exists_bad : ∃ x, x + 1 = y := by
  use y - 1; omega
```
**Fix**: If needed, construct the witness explicitly.

### ❌ Implicitly assuming decidability
```lean
-- WRONG:
theorem unclear (n : Nat) : n = 5 ∨ n ≠ 5 := by decide
```
**Fix**: Use `Nat.eq_or_ne` instead, or only call `decide` on concrete values.

---

## Testing and Validation

Each Track file compiles independently:
```bash
lake build Gnosis.Optics.RetinalTopography
lake build Gnosis.Optics.PhotopigmentKinetics
lake build Gnosis.Optics.PerceptualTransition
lake build Gnosis.Optics.PhospheneTopology
```

Integration file tests all tracks together:
```bash
lake build Gnosis.Optics.UnifiedVisualPhysics
```

Full workspace verification:
```bash
lake build Gnosis.Optics
```

---

## References

- **Lean Init Library**: Nat lemmas used are from `Std.Data.Nat.*` and `Init.Data.Nat.*`
- **Rustic Church Doctrine**: See `RUSTIC_CHURCH.md` for broader style guide
- **God Formula**: Defined in `Gnosis/Optics/OpticalFoundations.lean`
- **Theorem Index**: All 16 core theorems listed in summary at top of this document

---

## Summary

Optics formalizes visual perception as four interacting tracks unified by the God Formula. Each track uses Init-only proofs to establish domain-specific conservation laws. The style emphasizes explicit lemma application, monotonicity through structured bounds (division, subtraction, multiplication), and discrete boundary verification.

The four tracks together answer: *How does structured percept emerge from noisy photonic input, traverse physiological recovery boundaries, and organize into topological regimes?*

Answer: Through God's formula applied four ways.
