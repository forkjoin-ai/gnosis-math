# Continuous SU(2) → SO(3) Double Cover — Proof Skeleton (Mathlib-deferred)

Status: **NOT MACHINE-CHECKED HERE.** This is a precise proof skeleton, not a Lean
proof. See the Feasibility section for why no Lean module was produced in this ledger.

This document is the continuous-lift counterpart to the *discrete shadow* already proven
in `Gnosis/OrientationSpinorBridge.lean` (Init-only, zero `sorry`). It states exactly the
Mathlib definitions and lemmas one would assemble, in a Mathlib-enabled project, to lift
that bridge's `square_loses_sign` and `order_halves_under_quotient` to the genuine
continuous covering homomorphism `SU(2) → SO(3)`.

---

## 0. Feasibility finding (the honest deliverable)

`open-source/gnosis-math` is an **Init-only ledger**. Concretely, as of this writing:

- `lakefile.toml` declares one `lean_lib` (`Gnosis`) and has **no `[[require]]`** stanza.
- `lake-manifest.json` lists `"packages": []`. There is **no `.lake/packages/` directory**;
  no Mathlib `.olean` exists anywhere on disk.
- The repo deliberately ships its own continuum, `Gnosis.Real` — `abbrev BuleReal := Nat`,
  a scaled-integer continuum that the file's own docstring describes as avoiding "the
  classical Real cathedral."
- The ~32 stray `import Mathlib.Data.Real.Basic` lines scattered across `Gnosis/*` are
  **dangling**: building any of them fails with
  `error: unknown module prefix 'Mathlib' ... No directory 'Mathlib' or file 'Mathlib.olean'
  in the search path`. Those modules are part of the pre-broken RED surface, not a usable
  Mathlib foundation.

Therefore the continuous lift — which needs `Mathlib.Algebra.Quaternion`,
`Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup` / `…/Orthogonal`, real inner-product
spaces, `Matrix.specialOrthogonalGroup`, and (for periodicity) `Real.exp`/`expMapCircle`
and `Real.pi` — **cannot** be built in this ledger. Per the task's own guard, the correct
action was to STOP rather than vendor Mathlib for hours or fork a parallel project. The
deliverable in the Init-only case is this skeleton.

The discrete bridge file's own `Next exploration:` block already anticipates exactly this
Mathlib path; this document fills it in to the level of named lemmas and a proof outline.

---

## 1. Carrier choices in Mathlib

Two standard realizations; the quaternion route is the lighter lift.

### Route A — unit quaternions acting by conjugation (recommended)

```
open Quaternion          -- Mathlib.Algebra.Quaternion  (ℍ[ℝ] := Quaternion ℝ)

-- Unit quaternions = the multiplicative subgroup of norm-1 elements.
-- In Mathlib this is `Quaternion.unitSphere` flavored, or use the
-- `Submonoid`/`Subgroup` of `ℍ[ℝ]ˣ` cut out by `normSq q = 1`.
-- A clean carrier: `{ q : ℍ[ℝ] // normSq q = 1 }` with the induced group structure,
-- or `Metric.sphere (0 : ℍ[ℝ]) 1` (which Mathlib already knows is a topological space).

-- The pure-imaginary part ℝ³ ≅ { q : ℍ[ℝ] // q.re = 0 }  (the span of i, j, k).
-- Conjugation action:  ρ q v := q * v * q⁻¹      (q⁻¹ = conj q for unit q)
```

Key Mathlib facts available off the shelf:

- `Quaternion.normSq_mul : normSq (a * b) = normSq a * normSq b` — multiplicativity of the
  norm; gives that the action preserves the ℝ³ inner product when `normSq q = 1`.
- `Quaternion.normSq_eq_zero`, `Quaternion.coe_mul`, `Quaternion.star_mul`/`conj` lemmas —
  `q⁻¹ = star q` for unit `q` (since `q * star q = normSq q = 1`).
- `Quaternion.instInvolutiveStar` / `star_comm_self'` — the conjugation algebra needed to
  show `ρ q` maps pure-imaginary to pure-imaginary (`(q v q⁻¹).re = v.re = 0`).

### Route B — `SpecialUnitaryGroup (Fin 2) ℂ → specialOrthogonalGroup (Fin 3) ℝ`

```
open Matrix
-- Matrix.specialUnitaryGroup (Fin 2) ℂ          -- SU(2)
-- Matrix.specialOrthogonalGroup (Fin 3) ℝ        -- SO(3)
```

Heavier: requires building the adjoint action on the 3-dim space of traceless Hermitian
matrices (the Pauli basis) and identifying it with ℝ³. Route A avoids the Hermitian-matrix
detour. Prefer Route A unless a downstream consumer needs the matrix presentation.

---

## 2. The covering homomorphism `Φ : Spin → SO(3)`

Define `Φ q := LinearMap.toContinuousLinearMap (conjugation-by-q on ℝ³)`, packaged as an
element of `specialOrthogonalGroup (Fin 3) ℝ` (or `(ℝ³ →ₗ[ℝ] ℝ³)` constrained to be a
rotation). Concretely:

```
def conjAction (q : UnitQuat) : ℝ³ →ₗ[ℝ] ℝ³ :=
  { toFun    := fun v => imPart (q * embed v * q⁻¹)
    map_add' := ...     -- from `mul_add`, `add_mul`, linearity of `imPart`/`embed`
    map_smul':= ... }   -- from ℝ-bilinearity of quaternion mult and `smul_comm`

def Φ (q : UnitQuat) : Matrix.specialOrthogonalGroup (Fin 3) ℝ := ⟨matrixOf (conjAction q), _⟩
```

The `specialOrthogonalGroup` membership obligation (`Mᵀ * M = 1 ∧ det M = 1`) is discharged
from §1's `normSq_mul` (orthogonality / inner-product preservation) plus a determinant-sign
+ connectedness argument (det is continuous, integer-valued ±1, `Φ 1 = I` has det 1, the
unit-quaternion group is connected ⇒ det ≡ 1).

---

## 3. (i) Group homomorphism — *expected to go through cleanly*

```
theorem Φ_one      : Φ 1 = 1
theorem Φ_mul      : ∀ a b : UnitQuat, Φ (a * b) = Φ a * Φ b
def     ΦHom       : UnitQuat →* SO(3) := { toFun := Φ, map_one' := Φ_one, map_mul' := Φ_mul }
```

Proof outline: `Φ_one` from `(1 * v * 1⁻¹) = v`. `Φ_mul` from associativity:
`(ab) v (ab)⁻¹ = a (b v b⁻¹) a⁻¹`, using `mul_inv_rev` and `mul_assoc`. **No choice/classical
needed** beyond what the `LinearMap`/`Matrix` packaging pulls in. This is the safe core and
is the continuous lift of the bridge's structural homomorphism (cf. `toDirector_intertwines`,
the equivariance that survives the quotient).

## 4. (ii) Kernel `= {±1}` — *expected to go through with moderate work*

```
theorem ker_Φ : (ΦHom.ker : Set UnitQuat) = {1, -1}
```

Proof outline:
- `⊇`: `Φ (-1) = Φ 1 = 1` because `(-1) v (-1)⁻¹ = (-1)(-1)⁻¹ v = v` (the sign cancels — this
  is **the exact continuous lift of `square_loses_sign`**: both `+1` and `-1` map to the
  identity rotation, the sign is lost, a 2-element fibre over one image point).
- `⊆`: if `q v q⁻¹ = v` for all pure-imaginary `v`, then `q` commutes with `i, j, k`, hence
  lies in the center of `ℍ[ℝ]`, which is the real scalars; with `normSq q = 1` this forces
  `q = ±1`. Mathlib support: the quaternion centralizer / `Quaternion.commute` lemmas, and
  `normSq` pinning the scalar to unit length.

This `{±1}` kernel **is** the 2:1 double-cover property — the continuous statement whose
discrete shadow is `squaring_is_double_cover` (`preimage_is_two`, 2-element fibre).

## 5. (iii) Surjectivity onto SO(3) — *the hard part; leave as obligation*

```
theorem Φ_surjective : Function.Surjective ΦHom        -- DEFERRED
```

Standard math proof (to be formalized): every rotation is a rotation by angle `θ` about a
unit axis `u ∈ ℝ³`; the unit quaternion `q = cos(θ/2) + sin(θ/2)·u` satisfies `Φ q =` that
rotation (half-angle formula). Formalizing this in Mathlib requires:
- the axis–angle / Euler-axis decomposition of an arbitrary `SO(3)` element (eigenvalue-1
  eigenvector existence — `Module.End` spectral input over ℝ, or
  `Matrix.specialOrthogonalGroup` rotation-axis lemmas if present);
- the half-angle computation `cos²(θ/2) − sin²(θ/2) = cos θ`, etc. (`Real.cos_sq_half`,
  `Real.sin_two_mul`, available);
- equating the two `SO(3)` matrices entrywise.

This is the genuinely hard, real-analytic part and stays an explicit
**`Next exploration:` obligation** — not a `sorry`. Until it is machine-checked the cover
is "homomorphism with kernel `{±1}` onto its image"; the *onto-all-of-SO(3)* clause is the
cited continuous picture only.

---

## 6. Periodicity lift — the `2π`/`4π` statement (continuous lift of `order_halves_under_quotient`)

One-parameter subgroup about a fixed unit axis `u`:

```
def loop (u : ℝ³) (huni : ‖u‖ = 1) (t : ℝ) : UnitQuat :=
  ⟨Real.cos (t/2) • 1 + Real.sin (t/2) • embed u, by simp [normSq, huni, Real.sin_sq_add_cos_sq]⟩
```

Target theorems (all provable in Mathlib from `Real.cos`/`Real.sin` at `π`, `2π`):

```
theorem loop_zero    : loop u h 0      = 1                       -- cos0=1, sin0=0
theorem loop_2pi     : loop u h (2*π)  = -1                      -- cos π = -1, sin π = 0
theorem loop_4pi     : loop u h (4*π)  = 1                       -- cos 2π = 1, sin 2π = 0
-- the spinor returns only at 4π upstairs, but the ROTATION returns already at 2π:
theorem Φ_loop_2pi   : Φ (loop u h (2*π)) = 1                    -- = Φ(-1) = 1  by §3 ker
theorem Φ_loop_4pi   : Φ (loop u h (4*π)) = 1
theorem spinor_4pi_vs_rotation_2pi :
    loop u h (2*π) = -1 ∧ loop u h (4*π) = 1 ∧
    Φ (loop u h (2*π)) = 1 ∧ Φ (loop u h (4*π)) = 1
```

Mathlib support: `Real.cos_pi = -1`, `Real.sin_pi = 0`, `Real.cos_two_pi = 1`,
`Real.sin_two_pi = 0`, `Real.sin_sq_add_cos_sq` (for the `normSq = 1` membership).

This is the **continuous lift of `order_halves_under_quotient`**: upstairs the spinor loop
has period `4π` (`loop_4pi`, with `loop_2pi = -1 ≠ 1`); downstairs the rotation loop has
period `2π` (`Φ_loop_2pi = 1`). The discrete `Fin 4 → Fin 2` order-halving in the bridge
(`rotSheet` order 4, `rotDirector` order 2) is the `π₀`/order shadow of this
`loop_2pi = -1` vs `Φ_loop_2pi = 1` gap — the belt-trick / orientation-entanglement sign.

---

## 7. Relationship to the discrete bridge (precise, no identity claims)

| Discrete (`OrientationSpinorBridge.lean`, proven) | Continuous (this skeleton, deferred) |
|---|---|
| `square_loses_sign`: `square false = square true` | `Φ(-1) = Φ(1) = 1` (§4 `⊇` direction) — the sign-loss |
| `squaring_is_double_cover` / `preimage_is_two` (2-elt fibre) | `ker_Φ = {±1}` (§4) — the 2:1 fibre |
| `order_halves_under_quotient` (sheet order 4 / director order 2) | `loop_2pi = -1`, `Φ_loop_2pi = 1` (§6) — `4π` spinor vs `2π` rotation |
| `toDirector_intertwines` (equivariant quotient) | `Φ_mul` group homomorphism (§3) |

The discrete maps `square : Bool → Int` and `toDirector : Fin 4 → Fin 2` **map to** (are
the finite/`π₀` shadow of) the continuous cover; they do not reconstruct it. The bridge
file states this relationship as "MAPS TO," and this skeleton keeps that discipline: it
would *prove* the relationship `square` factors through `Φ`'s `{±1}`-component only once §3,
§4, §6 are machine-checked.

---

## 8. Expected axiom footprint (when built under Mathlib)

A continuous result over ℝ **will** pull `Classical.choice`, `propext`, and `Quot.sound`
via Mathlib's real-analysis and `LinearMap`/`Matrix` machinery. That is expected and
acceptable for a continuous theorem — it is the price of working over the classical reals,
and is exactly why the sovereign ledger keeps a separate Init-only `BuleReal` continuum for
its decidable core. The discrete bridge, by contrast, is `decide`-closed and prints only the
empty/structural axiom set; these two layers are *intentionally* different in footprint.

---

## 9. Recommended landing site (if/when Mathlib is added)

Do **not** add Mathlib to this ledger to chase this. The clean path is a **separate
Mathlib-enabled Lake project** (its own `lakefile` with `require mathlib`), e.g.
`open-source/gnosis-mathlib/` or a `Continuous/` lib target, importing nothing from the
Init-only `Gnosis` lib. Mixing a Mathlib lib into this `defaultTargets = ["Gnosis"]`
Init-only package would re-point the whole ledger at the classical-real cathedral the repo
explicitly rejects. Keep the two continua decoupled, mirroring how §5/§8 above keep their
proofs decoupled from the discrete `decide` core.

**Next exploration:** stand up that separate Mathlib project, formalize §3 (homomorphism)
and §4 (`ker = {±1}`) first — both expected-clean — then §6 (periodicity, expected-clean
from `Real.cos_pi`/`cos_two_pi`); leave §5 (surjectivity via axis–angle) as the single
remaining hard obligation. None of these belong as a `sorry` in the Init-only ledger.
