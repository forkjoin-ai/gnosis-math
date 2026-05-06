import Init

/-!
# Continued-Fraction Convergents as Frobenius-Algebra Cobordism Tower Partitions

This module witnesses a structural correspondence between three peer
modules:

* `ContinuedFractionConvergents.lean` — the `(p_n, q_n)` recurrence for
  simple continued fractions, with Cassini and Pell witnesses for
  `φ = [1;1,1,1,…]` and `√2 = [1;2,2,2,…]`.
* `OneCobFrobenius.lean` — the algebra `A = (ℤ/2)[x]/(x²)` realizing a
  1D TQFT's structure maps (unit, counit, mult, comult).
* `FrobeniusPantsComposition.lean` — the Atiyah–Segal functor `Z` on
  identity/cap/pants cobordisms, with composition-of-pants witnesses.

## The bridge

A simple CF `[a_0; a_1, a_2, …]` is computed by a fixed linear
recurrence on the two-dimensional state `(p_{n-1}, p_n)`:

    step a (p_prev, p_curr) := (p_curr, a · p_curr + p_prev).

Each partial quotient `a_i` picks a specific `ℤ`-linear endomorphism
`cfStep a_i : ℤ² → ℤ²`. The composite `cfStep a_n ∘ … ∘ cfStep a_0`
applied to an initial state is the partition function of the composed
cobordism tower `W_{a_n} ∘ … ∘ W_{a_0}` under the Atiyah–Segal
dictionary, *at the level of underlying linear maps on a rank-2 free
module*. Each `cfStep a` plays the role of `Z(W_a)` for a
pants-with-`a`-labeled-copair cobordism acting on a rank-2 state space.

The matrix form

    M_a = ⟨⟨0, 1⟩, ⟨1, a⟩⟩,      det M_a = -1

lets the composed tower matrix be read off; its determinant is the
signed Cassini identity
`p_n · q_{n-1} − p_{n-1} · q_n = (-1)^{n-1}` for the convergent
trajectory seeded at `(p_{-2}, q_{-2}) = (0, 1)` and
`(p_{-1}, q_{-1}) = (1, 0)`.

## What this module witnesses

1. `cfStep` and `cfTower` realize the numerator (or denominator) side
   of the CF recurrence as a ℤ-linear map, with `decide`-closed depth
   values agreeing with Fibonacci sequencing.
2. `cfStepPair` and `cfTowerPair` carry the full convergent pair
   `(p_n, q_n)` and reproduce the `(p, q)` list from
   `ContinuedFractionConvergents.lean` at several depths.
3. The bridge theorem `cfTower_last_matches_convergent_pair` shows that
   the final pair produced by `cfTowerPair` on the standard
   `(0, 1, 1, 0)` seed is exactly the final pair in the peer module's
   `convergents` list.
4. Cassini-as-determinant witnesses: the composed 2×2 matrix
   representation of the tower has `det = ±1` at several depths, with
   the sign pattern `(-1)^n`.

## What is *not* witnessed

* No 2D TQFT. The correspondence operates at the level of rank-2
  ℤ-linear maps, not the full Cob_2 functor.
* The Frobenius-algebra structure on `A = (ℤ/2)[x]/(x²)` in
  `OneCobFrobenius.lean` is not literally the state space of the CF
  recurrence. The analogy is structural: each cobordism `W_a`
  instantiates a linear endomorphism, and towers compose as
  categorical composition of cobordisms instantiates composition of
  linear maps.
* No claim is made that the ℤ/2-valued Frobenius partition functions
  of `OneCobFrobenius` compute CF convergents. The bridge is the
  shared compositional pattern: label-parameterized cobordisms
  compose into a tower whose partition function is the composed
  linear map.
* No encoding of `cfStep` into `A ⊗ A → A ⊗ A` in any literal sense.

No `sorry`, no new `axiom`. `import Init` only. Peer definitions that
are referenced are re-inlined verbatim to keep the module
self-contained. Every concrete identity is closed by kernel `decide`.
-/

namespace Gnosis
namespace CFCobordismPartition

/-! ## Re-inlined fragments of `ContinuedFractionConvergents.lean`

We need the peer module's `convergents` list to state the bridge
theorem, but we may not import it. The following definitions are
verbatim copies of the peer surface area used by the bridge. -/

/-- One step of the peer module's `(p, q)` convergent recurrence on
`Nat × Nat`. -/
def stepConvergent (prev2 prev1 : Nat × Nat) (a : Nat) : Nat × Nat :=
  (a * prev1.1 + prev2.1, a * prev1.2 + prev2.2)

/-- Peer-module core accumulator. -/
def convergentsAux : Nat × Nat → Nat × Nat → List Nat → List (Nat × Nat)
  | _,     _,     []      => []
  | prev2, prev1, a :: as =>
    let curr := stepConvergent prev2 prev1 a
    curr :: convergentsAux prev1 curr as

/-- Peer-module `convergents` of a CF given by its partial quotients. -/
def convergents (as : List Nat) : List (Nat × Nat) :=
  convergentsAux (0, 1) (1, 0) as

/-! ## The CF step as a rank-2 ℤ-linear endomorphism

The scalar recurrence `p_n = a · p_{n-1} + p_{n-2}` is a ℤ-linear map

    ⟨p_prev, p_curr⟩ ↦ ⟨p_curr, a · p_curr + p_prev⟩.

Equivalently, left-multiplication by the matrix `M_a = ⟨⟨0, 1⟩, ⟨1, a⟩⟩`.
We encode this as a function on `Int × Int`. -/

/-- One CF step as a ℤ-linear endomorphism of `Int × Int`.
`cfStep a` is the linear map `M_a : ⟨p_prev, p_curr⟩ ↦ ⟨p_curr, a · p_curr + p_prev⟩`. -/
def cfStep (a : Int) (st : Int × Int) : Int × Int :=
  (st.2, a * st.2 + st.1)

/-- The composed tower `cfStep a_{n-1} ∘ … ∘ cfStep a_0` applied to a
seed state. Iterating left-to-right through the list of partial
quotients. -/
def cfTower : List Int → Int × Int → Int × Int
  | [],      st => st
  | a :: as, st => cfTower as (cfStep a st)

/-! ## The CF step on the full convergent pair `(p_n, q_n)`

Carrying both numerator and denominator requires a rank-4 state
`(p_prev, q_prev, p_curr, q_curr)`. One step is the linear map
`⟨pp, qp, pc, qc⟩ ↦ ⟨pc, qc, a · pc + pp, a · qc + qp⟩`. -/

/-- Full convergent-pair CF step on a rank-4 state
`(p_prev, q_prev, p_curr, q_curr)`. -/
def cfStepPair (a : Int) (st : Int × Int × Int × Int) : Int × Int × Int × Int :=
  let pp := st.1
  let qp := st.2.1
  let pc := st.2.2.1
  let qc := st.2.2.2
  (pc, qc, a * pc + pp, a * qc + qp)

/-- Tower of convergent-pair steps. -/
def cfTowerPair : List Int → Int × Int × Int × Int → Int × Int × Int × Int
  | [],      st => st
  | a :: as, st => cfTowerPair as (cfStepPair a st)

/-- Canonical initial state `(p_{-2}, q_{-2}, p_{-1}, q_{-1}) = (0, 1, 1, 0)`. -/
def initPair : Int × Int × Int × Int := (0, 1, 1, 0)

/-- Project the current-convergent pair `(p_n, q_n)` out of the rank-4
state. -/
def currPair (st : Int × Int × Int × Int) : Int × Int :=
  (st.2.2.1, st.2.2.2)

/-! ## Sanity: the scalar tower reproduces Fibonacci sequencing

With seed `(0, 1)` and partial quotients all `1`, the state sequence
is `(0,1), (1,1), (1,2), (2,3), (3,5), (5,8), (8,13), …`, reading off
pairs of consecutive Fibonacci numbers. -/

/-- Five 1's on `(0, 1)` yields `(5, 8)`. -/
theorem cfTower_phi_5 :
    cfTower [1, 1, 1, 1, 1] (0, 1) = (5, 8) := by decide

/-- Six 1's on `(0, 1)` yields `(8, 13)`. -/
theorem cfTower_phi_6 :
    cfTower [1, 1, 1, 1, 1, 1] (0, 1) = (8, 13) := by decide

/-- Seven 1's on `(0, 1)` yields `(13, 21)`. -/
theorem cfTower_phi_7 :
    cfTower [1, 1, 1, 1, 1, 1, 1] (0, 1) = (13, 21) := by decide

/-- Starting from `(1, 0)` (the denominator-side seed), `[1, 2, 2, 2, 2, 2]`
yields `(29, 70)`. -/
theorem cfTower_sqrt2_denominator :
    cfTower [1, 2, 2, 2, 2, 2] (1, 0) = (29, 70) := by decide

/-- Starting from `(0, 1)` (the numerator-side seed), `[1, 2, 2, 2, 2, 2]`
yields `(41, 99)`. -/
theorem cfTower_sqrt2_numerator :
    cfTower [1, 2, 2, 2, 2, 2] (0, 1) = (41, 99) := by decide

/-! ## Sanity: the paired tower reproduces the peer module's
convergents list exactly.

For each partial-quotients list, the current pair `(p_n, q_n)`
extracted from the paired tower on seed `(0, 1, 1, 0)` matches the
last element of `convergents as` cast into `Int × Int`. -/

/-- `φ` convergent tower on the paired state, final pair is `(13, 8)`. -/
theorem cfTowerPair_phi_6_last :
    currPair (cfTowerPair [1, 1, 1, 1, 1, 1] initPair) = (13, 8) := by decide

/-- `√2` convergent tower on the paired state, final pair is `(99, 70)`. -/
theorem cfTowerPair_sqrt2_6_last :
    currPair (cfTowerPair [1, 2, 2, 2, 2, 2] initPair) = (99, 70) := by decide

/-- `φ` convergent tower, depth 5, final pair `(8, 5)`. -/
theorem cfTowerPair_phi_5_last :
    currPair (cfTowerPair [1, 1, 1, 1, 1] initPair) = (8, 5) := by decide

/-- `√2` convergent tower, depth 5, final pair `(41, 29)`. -/
theorem cfTowerPair_sqrt2_5_last :
    currPair (cfTowerPair [1, 2, 2, 2, 2] initPair) = (41, 29) := by decide

/-! ## Bridge theorem: the paired tower matches `convergents`

The peer module computes `convergents as : List (Nat × Nat)` on the
same recurrence with the same seeds. Its last element corresponds to
the `(p_n, q_n)` projection of the paired tower. We witness this
correspondence at the two featured CF sequences. -/

/-- Read the last element of a list, or a default. -/
def lastOrDefault {α : Type} (d : α) : List α → α
  | []      => d
  | [x]     => x
  | _ :: t  => lastOrDefault d t

/-- Cast a `Nat × Nat` pair into `Int × Int`. -/
def natPairToInt (p : Nat × Nat) : Int × Int :=
  (Int.ofNat p.1, Int.ofNat p.2)

/--
Bridge theorem (φ). The final pair computed by `cfTowerPair` on
`[1, 1, 1, 1, 1, 1]` with seed `initPair` equals the final entry of
the peer module's `convergents [1, 1, 1, 1, 1, 1]` (cast into `Int`).
-/
theorem cfTower_last_matches_convergent_pair_phi :
    currPair (cfTowerPair [1, 1, 1, 1, 1, 1] initPair)
      = natPairToInt (lastOrDefault (0, 0) (convergents [1, 1, 1, 1, 1, 1])) := by
  decide

/--
Bridge theorem (√2). The final pair computed by `cfTowerPair` on
`[1, 2, 2, 2, 2, 2]` with seed `initPair` equals the final entry of
the peer module's `convergents [1, 2, 2, 2, 2, 2]` (cast into `Int`).
-/
theorem cfTower_last_matches_convergent_pair_sqrt2 :
    currPair (cfTowerPair [1, 2, 2, 2, 2, 2] initPair)
      = natPairToInt (lastOrDefault (0, 0) (convergents [1, 2, 2, 2, 2, 2])) := by
  decide

/-! ## 2×2 matrix representation and Cassini determinant

The linear recurrence is equivalent to left-multiplication by the
matrix

    M_a = ⟨⟨0, 1⟩, ⟨1, a⟩⟩,    det M_a = -1.

The composed tower matrix `M_{a_{n-1}} · … · M_{a_0}` has determinant
`(-1)^n` (product of determinants). Applying that matrix to the
convergent-matrix seed

    M_init = ⟨⟨0, 1⟩, ⟨1, 0⟩⟩,   det M_init = -1,

gives a 2×2 matrix whose columns are `(p_{n-1}, p_n)` and
`(q_{n-1}, q_n)` (up to transpose); its determinant is the signed
Cassini quantity `p_n · q_{n-1} - p_{n-1} · q_n = (-1)^{n-1}`.

We encode a 2×2 integer matrix by its four entries and compute the
determinant of the tower matrix at several depths. -/

/-- A 2×2 integer matrix as four entries `⟨⟨a, b⟩, ⟨c, d⟩⟩`. -/
structure Mat2 where
  /-- Top-left entry `a`. -/
  a : Int
  /-- Top-right entry `b`. -/
  b : Int
  /-- Bottom-left entry `c`. -/
  c : Int
  /-- Bottom-right entry `d`. -/
  d : Int
deriving DecidableEq, Repr

/-- The matrix `M_a = ⟨⟨0, 1⟩, ⟨1, a⟩⟩`. -/
def mStep (a : Int) : Mat2 := { a := 0, b := 1, c := 1, d := a }

/-- The convergent-matrix seed `M_init = ⟨⟨0, 1⟩, ⟨1, 0⟩⟩`. -/
def mInit : Mat2 := { a := 0, b := 1, c := 1, d := 0 }

/-- Matrix multiplication on `Mat2`. -/
def matMul (P Q : Mat2) : Mat2 :=
  { a := P.a * Q.a + P.b * Q.c
  , b := P.a * Q.b + P.b * Q.d
  , c := P.c * Q.a + P.d * Q.c
  , d := P.c * Q.b + P.d * Q.d }

/-- Determinant of a 2×2 integer matrix. -/
def det (P : Mat2) : Int := P.a * P.d - P.b * P.c

/-- Compose a tower of `mStep` matrices right-to-left against `mInit`.
`matTower [a_0, a_1, …, a_{n-1}]` yields `M_{a_{n-1}} · … · M_{a_0} · M_init`. -/
def matTower : List Int → Mat2 → Mat2
  | [],      M => M
  | a :: as, M => matTower as (matMul (mStep a) M)

/-- The tower of `cfStep` matrices alone, without the initial
convergent-matrix seed. `matStepTower [a_0, …, a_{n-1}] = M_{a_{n-1}} · … · M_{a_0}`. -/
def matStepTower (as : List Int) : Mat2 :=
  matTower as
    { a := 1, b := 0, c := 0, d := 1 }  -- identity

/-- `det(mStep a) = -1` always. -/
theorem det_mStep (a : Int) : det (mStep a) = -1 := by
  unfold det mStep
  simp

/-- `det(mInit) = -1`. -/
theorem det_mInit : det mInit = -1 := by decide

/-! ### Cassini-determinant witnesses at specific depths

The determinant of `matTower as mInit` is `(-1)^{|as| + 1}`, witnessed
at depths 3, 4, 5 for both `φ` and `√2` CF sequences. Odd lengths
give `+1`, even lengths give `-1`. -/

/-- Cassini determinant at `φ` depth 3 is `+1`. -/
theorem cassini_det_phi_3 :
    det (matTower [1, 1, 1] mInit) = 1 := by decide

/-- Cassini determinant at `φ` depth 4 is `-1`. -/
theorem cassini_det_phi_4 :
    det (matTower [1, 1, 1, 1] mInit) = -1 := by decide

/-- Cassini determinant at `φ` depth 5 is `+1`. -/
theorem cassini_det_phi_5 :
    det (matTower [1, 1, 1, 1, 1] mInit) = 1 := by decide

/-- Cassini determinant at `φ` depth 6 is `-1`. -/
theorem cassini_det_phi_6 :
    det (matTower [1, 1, 1, 1, 1, 1] mInit) = -1 := by decide

/-- Cassini determinant at `√2` depth 3 is `+1`. -/
theorem cassini_det_sqrt2_3 :
    det (matTower [1, 2, 2] mInit) = 1 := by decide

/-- Cassini determinant at `√2` depth 4 is `-1`. -/
theorem cassini_det_sqrt2_4 :
    det (matTower [1, 2, 2, 2] mInit) = -1 := by decide

/-- Cassini determinant at `√2` depth 5 is `+1`. -/
theorem cassini_det_sqrt2_5 :
    det (matTower [1, 2, 2, 2, 2] mInit) = 1 := by decide

/-- Cassini determinant at `√2` depth 6 is `-1`. -/
theorem cassini_det_sqrt2_6 :
    det (matTower [1, 2, 2, 2, 2, 2] mInit) = -1 := by decide

/-! ### The step-only tower determinant pattern

Without the `mInit` seed, `matStepTower as` has determinant
`(-1)^{|as|}`. Even length → `+1`, odd length → `-1`. -/

/-- Step-only tower determinant at length 3 is `-1`. -/
theorem det_step_tower_len3 :
    det (matStepTower [1, 1, 1]) = -1 := by decide

/-- Step-only tower determinant at length 4 is `+1`. -/
theorem det_step_tower_len4 :
    det (matStepTower [1, 1, 1, 1]) = 1 := by decide

/-- Step-only tower determinant at length 5 is `-1`. -/
theorem det_step_tower_len5 :
    det (matStepTower [1, 2, 2, 2, 2]) = -1 := by decide

/-- Step-only tower determinant at length 6 is `+1`. -/
theorem det_step_tower_len6 :
    det (matStepTower [1, 2, 2, 2, 2, 2]) = 1 := by decide

/-! ## Cassini-as-determinant matches peer-module signed Cassini

The peer module defines `cassiniSigned prev curr := curr.1 · prev.2 −
prev.1 · curr.2`, which is the 2×2 determinant of the matrix whose
columns are `prev` and `curr`. At matching depths the two quantities
coincide.

We witness this directly at a handful of depths by computing both
sides. -/

/-- Signed Cassini determinant of two consecutive `(p, q)` pairs. -/
def cassiniSigned (prev curr : Int × Int) : Int :=
  curr.1 * prev.2 - prev.1 * curr.2

/-- At `φ` depth 5 (from the 5th to 6th convergent) the peer-module
signed Cassini value is `+1`. -/
theorem cassini_signed_phi_5 :
    cassiniSigned (8, 5) (13, 8) = 1 := by decide

/-- At `√2` depth 5 the peer-module signed Cassini value is `+1`. -/
theorem cassini_signed_sqrt2_5 :
    cassiniSigned (41, 29) (99, 70) = 1 := by decide

/-- At `√2` depth 4 the peer-module signed Cassini value is `-1`. -/
theorem cassini_signed_sqrt2_4 :
    cassiniSigned (17, 12) (41, 29) = -1 := by decide

/-! ## Frobenius-pants interpretation (structural, prose-level)

Under the Atiyah–Segal dictionary inherited from `OneCobFrobenius.lean`
and `FrobeniusPantsComposition.lean`, a 1D TQFT `Z` maps each
cobordism to a linear map between state spaces. For the CF
correspondence we choose a rank-2 free ℤ-module as the state space and
identify:

*  The "labeled pants" `W_a` is a cobordism whose partition function
   `Z(W_a)` realizes the linear map `cfStep a`. Algebraically,
   `Z(W_a) = M_a` with `det = -1`.
*  Composition of cobordisms `W_{a_n} ∘ … ∘ W_{a_0}` instantiates
   left-to-right composition of `cfStep`s, which is exactly `cfTower`.
*  The partition function `Z(W_{a_n} ∘ … ∘ W_{a_0}) : ℤ² → ℤ²` is the
   composed linear map `cfStep a_n ∘ … ∘ cfStep a_0`; applied to the
   initial state `(0, 1)` (or to the 4D state `initPair`), it reads
   off the CF convergents.
*  The Cassini identity `p_n · q_{n-1} − p_{n-1} · q_n = (-1)^{n-1}`
   is the determinant of the composed partition-function matrix
   `matTower as mInit`.

This is not a full 2D TQFT: the Frobenius algebra of
`OneCobFrobenius.lean` is over `ℤ/2` with four elements, while the
state space here is the rank-2 free ℤ-module. The shared structure —
labeled-generator cobordisms composing into towers whose partition
function is the composed linear map — is what this module formalizes.
The concrete Frobenius identity `Δ ∘ m = (m ⊗ id) ∘ (id ⊗ Δ)` of the
peer modules is orthogonal to the CF recurrence: it lives in the
tensor-of-tensor arity, while `cfStep` is unary. They share a
categorical pattern, not an algebraic identity.
-/

/-! ## Aggregate witness

A single decidable bundle tying together the core bridge facts: the
tower recovers the peer convergent list on both CF sequences, and the
signed Cassini determinant agrees with the matrix determinant at the
same depth. -/

/-- Aggregate CF-cobordism-partition bridge witness. -/
theorem cf_cobordism_partition_witness :
    currPair (cfTowerPair [1, 1, 1, 1, 1, 1] initPair) = (13, 8) ∧
    currPair (cfTowerPair [1, 2, 2, 2, 2, 2] initPair) = (99, 70) ∧
    det (matTower [1, 1, 1, 1, 1, 1] mInit) = -1 ∧
    det (matTower [1, 2, 2, 2, 2, 2] mInit) = -1 ∧
    det (matTower [1, 1, 1, 1, 1] mInit) = 1 ∧
    det (matTower [1, 2, 2, 2, 2] mInit) = 1 ∧
    cassiniSigned (8, 5) (13, 8) = 1 ∧
    cassiniSigned (41, 29) (99, 70) = 1 := by
  decide

end CFCobordismPartition
end Gnosis
