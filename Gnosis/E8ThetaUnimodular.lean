/-
  E8ThetaUnimodular
  =================

  The theta series of the `E_8` lattice and its even-unimodular
  arithmetic, as FINITE DECIDABLE shadows.

  The theta series of `E_8` equals the weight-4 Eisenstein series `E₄`:

      Θ_{E₈}(q)  =  E₄(q)  =  1 + 240 ∑_{n≥1} σ₃(n) qⁿ
                            =  1 + 240q + 2160q² + 6720q³ + 17520q⁴ + ⋯

  where `σ₃(n) = ∑_{d ∣ n} d³` is the sum of cubes of divisors.  The
  coefficient of `qⁿ` counts the lattice vectors of squared-norm `2n`:

      r(2n)  =  #{ v ∈ E₈ : ⟨v,v⟩ = 2n }  =  240 · σ₃(n),   n ≥ 1,
      r(0)   =  1                                 (the zero vector).

  In particular `r(2) = 240` — the minimal (norm²=2) vectors are exactly
  the 240 roots (cross-checks `E8Lattice.e8_root_count`).

  WHAT WE PROVE (all kernel `decide`/`rfl`, Init-only, no Mathlib):
    • `σ₃(n)` computed by a decidable divisor-cube sum, for n = 1..5;
    • the first five theta coefficients `r(2n) = 240·σ₃(n)`;
    • the products `240·9`, `240·28`, `240·73`, `240·126`;
    • `r(2) = 240` tied to the root count;
    • `r(0) = 1`;
    • the determinant of the `E_8` Cartan / Gram matrix `= 1`
      (an integer Laplace-cofactor determinant, proved by `decide`),
      certifying the lattice is UNIMODULAR.

  HONESTY (read before trusting any number).  Every coefficient and
  every `σ₃` value below was COMPUTED before being proved:

      σ₃(1)=1,  σ₃(2)=9,  σ₃(3)=28,  σ₃(4)=73,  σ₃(5)=126
      r(2)=240, r(4)=2160, r(6)=6720, r(8)=17520, r(10)=30240
      240·9=2160, 240·28=6720, 240·73=17520, 240·126=30240
      det(Cartan E₈)=1

  All matched the design brief exactly; NO number was dropped or
  corrected (unlike the sibling `LeechLatticeArithmetic`, where two
  brief numbers were false).  See `verified_numbers` at the bottom.

  We never write "X IS the Y": we say "equals", "counts", "is the
  coefficient of".  The genuine modular-forms statement (that the
  theta series of `E_8` IS `E₄` as holomorphic modular forms on the
  upper half-plane, via the dimension-1 space `M₄(SL₂ℤ)`) is DEFERRED
  — it needs far more than `Init`.  We prove only the integer
  coefficient arithmetic and the unimodular determinant.

  SSOT.  The 240 roots / minimal vectors live in `E8Lattice` (240 =
  `E8Lattice.e8_root_count`, norm²=8 in the ×2 scaled model = norm²=2
  standard).  The even-unimodular rank-8 uniqueness sits beside the
  rank-24 Niemeier count in `LeechLatticeArithmetic`.
-/

import Gnosis.E8Lattice

namespace E8ThetaUnimodular

-- ══════════════════════════════════════════════════════════
-- σ₃ : THE SUM OF CUBES OF DIVISORS
-- ══════════════════════════════════════════════════════════

/-- The divisors of `n` in `[1, n]` (decidable over a finite range). -/
def divisors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter (fun d => d ≠ 0 ∧ n % d == 0)

/-- `σ₃(n) = ∑_{d ∣ n} d³`, the sum of cubes of the divisors of `n`. -/
def sigma3 (n : Nat) : Nat := (divisors n).foldl (fun s d => s + d ^ 3) 0

/-- `σ₃(1) = 1`  (divisor `1`; `1³ = 1`). -/
theorem sigma3_one : sigma3 1 = 1 := by decide
/-- `σ₃(2) = 9 = 1 + 8`  (divisors `1, 2`). -/
theorem sigma3_two : sigma3 2 = 9 := by decide
/-- `σ₃(3) = 28 = 1 + 27`  (divisors `1, 3`). -/
theorem sigma3_three : sigma3 3 = 28 := by decide
/-- `σ₃(4) = 73 = 1 + 8 + 64`  (divisors `1, 2, 4`). -/
theorem sigma3_four : sigma3 4 = 73 := by decide
/-- `σ₃(5) = 126 = 1 + 125`  (divisors `1, 5`). -/
theorem sigma3_five : sigma3 5 = 126 := by decide

/-- The cube-sum identities behind the `σ₃` values, spelled out so the
    arithmetic is visible and not hidden inside the divisor folder. -/
theorem sigma3_cube_sums :
    (1 = 1) ∧ (1 + 8 = 9) ∧ (1 + 27 = 28) ∧ (1 + 8 + 64 = 73)
    ∧ (1 + 125 = 126) := by
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- THE THETA COEFFICIENTS  r(2n) = 240 · σ₃(n)
-- ══════════════════════════════════════════════════════════

/-- The Eisenstein/theta prefactor `240`. -/
def thetaPrefactor : Nat := 240

/-- `r(2n)` for `n ≥ 1`: the number of `E_8` vectors of squared-norm
    `2n`, defined as `240 · σ₃(n)`. -/
def rNorm (n : Nat) : Nat := thetaPrefactor * sigma3 n

/-- The constant term of the theta series, `r(0) = 1` (the zero vector
    is the unique vector of norm `0`). -/
def rZero : Nat := 1

-- ── the five products, verified first ──────────────────────
/-- `240 · 9 = 2160`. -/
theorem prod_240_9   : 240 * 9   = 2160  := by decide
/-- `240 · 28 = 6720`. -/
theorem prod_240_28  : 240 * 28  = 6720  := by decide
/-- `240 · 73 = 17520`. -/
theorem prod_240_73  : 240 * 73  = 17520 := by decide
/-- `240 · 126 = 30240`. -/
theorem prod_240_126 : 240 * 126 = 30240 := by decide

-- ── the coefficients r(2n) = 240·σ₃(n) ─────────────────────
/-- `r(2) = 240·σ₃(1) = 240` — the minimal vectors (the roots). -/
theorem r2_eq_240 : rNorm 1 = 240 := by decide
/-- `r(4) = 240·σ₃(2) = 240·9 = 2160`. -/
theorem r4_eq_2160 : rNorm 2 = 2160 := by decide
/-- `r(6) = 240·σ₃(3) = 240·28 = 6720`. -/
theorem r6_eq_6720 : rNorm 3 = 6720 := by decide
/-- `r(8) = 240·σ₃(4) = 240·73 = 17520`. -/
theorem r8_eq_17520 : rNorm 4 = 17520 := by decide
/-- `r(10) = 240·σ₃(5) = 240·126 = 30240`. -/
theorem r10_eq_30240 : rNorm 5 = 30240 := by decide

/-- The defining relation `r(2n) = 240 · σ₃(n)` holds by definition for
    every `n` (`rNorm` is literally that product). -/
theorem rNorm_is_240_sigma3 (n : Nat) : rNorm n = 240 * sigma3 n := rfl

-- ══════════════════════════════════════════════════════════
-- r(2) = 240 = THE E_8 ROOT COUNT  (SSOT tie)
-- ══════════════════════════════════════════════════════════

/-- The number of `E_8` roots (minimal vectors), `240`, as tabulated in
    `E8Lattice` (`E8Lattice.e8_root_count : e8Roots.length = 240`). -/
def e8RootCount : Nat := 240

/-- **The norm² = 2 coefficient equals the root count.**  `r(2) = 240`
    and the `E_8` root count is `240`: the minimal vectors counted by
    the first theta coefficient are exactly the 240 roots. -/
theorem r2_eq_root_count : rNorm 1 = e8RootCount := by decide

/-- The tabulated root count `240` matches `E8Lattice.e8Roots.length`
    (the `native_decide`-backed enumeration of the 240 root vectors). -/
theorem e8_root_count_ties_lattice : e8RootCount = E8Lattice.e8Roots.length := by
  have h : E8Lattice.e8Roots.length = 240 := E8Lattice.e8_root_count
  simp [e8RootCount, h]

/-- The constant term is `r(0) = 1` (the zero vector). -/
theorem rZero_eq_one : rZero = 1 := by decide

-- ══════════════════════════════════════════════════════════
-- THE FIRST FIVE COEFFICIENTS, LISTED  (= the head of E₄)
-- ══════════════════════════════════════════════════════════

/-- The leading theta coefficients `[r(0), r(2), r(4), r(6), r(8), r(10)]`
    `= [1, 240, 2160, 6720, 17520, 30240]` — the head of the `q`-expansion
    of `E₄`. -/
def thetaHead : List Nat := [rZero, rNorm 1, rNorm 2, rNorm 3, rNorm 4, rNorm 5]

/-- **Theta series head (VERIFIED).**  `Θ_{E₈} = E₄` begins
    `1 + 240q + 2160q² + 6720q³ + 17520q⁴ + 30240q⁵ + ⋯`. -/
theorem theta_head_values :
    thetaHead = [1, 240, 2160, 6720, 17520, 30240] := by decide

-- ══════════════════════════════════════════════════════════
-- EVEN UNIMODULAR : det(Gram) = 1
-- ══════════════════════════════════════════════════════════
-- `E_8` is the unique even unimodular lattice in dimension 8.  In the
-- basis of simple roots the Gram matrix is the `E_8` Cartan matrix
-- (diagonal 2, off-diagonal 0 or −1 along the Dynkin diagram); its
-- determinant is 1, which certifies the lattice is UNIMODULAR
-- (covolume 1).  We build the 8×8 integer Cartan matrix and prove its
-- determinant `= 1` by a Laplace cofactor expansion — a decidable
-- integer computation.

/-- Delete the `j`-th entry of a row (structural recursion on `Nat` and
    the list, so the kernel can reduce it under `decide`). -/
def dropNth : Nat → List Int → List Int
  | _, [] => []
  | 0,     _ :: tl => tl
  | (n+1), h :: tl => h :: dropNth n tl

/-- Laplace (cofactor) determinant of a square integer matrix given as a
    list of rows, expanding along the first row.  `fuel` bounds the
    recursion by the matrix size (structural recursion only, so kernel
    `decide` reduces it).  The `aij = 0` short-circuit skips the minor
    for zero pivots — essential for the SPARSE Cartan matrix to reduce
    inside the heartbeat budget. -/
def detRec : Nat → List (List Int) → Int
  | _,       []           => 1
  | 0,       _            => 0
  | (fuel+1), (row :: rows) =>
      ((List.range row.length).map (fun j =>
        let aij := row.getD j 0
        if aij == 0 then (0 : Int) else
          let sign : Int := if j % 2 == 0 then 1 else -1
          let minor := rows.map (fun r => dropNth j r)
          sign * aij * detRec fuel minor)).foldl (· + ·) 0

/-- Determinant of a square integer matrix (`fuel` = number of rows). -/
def det (m : List (List Int)) : Int := detRec m.length m

/-- The `E_8` Cartan matrix = Gram matrix of the simple-root basis
    (norm² = 2 convention), in Bourbaki node order.  Diagonal `2`;
    off-diagonal `−1` exactly on the edges of the `E_8` Dynkin diagram
    (a 7-node chain with the extra node attached at the 5th). -/
def e8Cartan : List (List Int) :=
  [ [ 2, -1,  0,  0,  0,  0,  0,  0],
    [-1,  2, -1,  0,  0,  0,  0,  0],
    [ 0, -1,  2, -1,  0,  0,  0,  0],
    [ 0,  0, -1,  2, -1,  0,  0,  0],
    [ 0,  0,  0, -1,  2, -1,  0, -1],
    [ 0,  0,  0,  0, -1,  2, -1,  0],
    [ 0,  0,  0,  0,  0, -1,  2,  0],
    [ 0,  0,  0,  0, -1,  0,  0,  2] ]

/-- The matrix is `8 × 8`. -/
theorem e8Cartan_is_8x8 :
    e8Cartan.length = 8 ∧ e8Cartan.all (fun r => r.length == 8) = true := by
  decide

/-- The diagonal entries are all `2` (every root has norm² = 2). -/
theorem e8Cartan_diagonal_two :
    (e8Cartan.zipIdx).all (fun p => p.1.getD p.2 0 == 2) = true := by decide

/-- **`E_8` is unimodular (VERIFIED).**  The determinant of the `E_8`
    Cartan / Gram matrix is `1`, so the lattice has covolume 1 — it is
    unimodular.  (Combined with all roots having even norm² = 2, this is
    the defining pair: `E_8` is even unimodular.) -/
theorem e8Cartan_det_one : det e8Cartan = 1 := by decide

-- ══════════════════════════════════════════════════════════
-- THE WHOLE E8 THETA / UNIMODULAR LEDGER (one decidable conjunction)
-- ══════════════════════════════════════════════════════════

/-- The `E_8` theta / even-unimodular arithmetic proved in this module,
    in one decidable conjunction:
      • σ₃ values      1, 9, 28, 73, 126
      • coefficients   r(2n) = 240·σ₃(n): 240, 2160, 6720, 17520, 30240
      • constant term  r(0) = 1
      • root tie       r(2) = 240 = root count
      • unimodular     det(Cartan E₈) = 1
    Each conjunct is a genuine, verified arithmetic fact. -/
theorem e8_theta_ledger :
    sigma3 1 = 1 ∧ sigma3 2 = 9 ∧ sigma3 3 = 28 ∧ sigma3 4 = 73
      ∧ sigma3 5 = 126
    ∧ rNorm 1 = 240 ∧ rNorm 2 = 2160 ∧ rNorm 3 = 6720 ∧ rNorm 4 = 17520
      ∧ rNorm 5 = 30240
    ∧ rZero = 1
    ∧ rNorm 1 = e8RootCount
    ∧ det e8Cartan = 1 := by
  exact ⟨by decide, by decide, by decide, by decide, by decide,
         by decide, by decide, by decide, by decide, by decide,
         by decide, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- VERIFIED NUMBERS  (honest record — nothing dropped)
-- ══════════════════════════════════════════════════════════
/--
  `verified_numbers` — a marker theorem whose docstring records that
  EVERY number in the design brief was computed and confirmed BEFORE
  being proved, and NONE was false:

    σ₃:   σ₃(1)=1, σ₃(2)=9 (1+8), σ₃(3)=28 (1+27),
          σ₃(4)=73 (1+8+64), σ₃(5)=126 (1+125)            all TRUE
    r:    r(2)=240, r(4)=2160, r(6)=6720,
          r(8)=17520, r(10)=30240                          all TRUE
    prod: 240·9=2160, 240·28=6720,
          240·73=17520, 240·126=30240                      all TRUE
    r(0)=1, r(2)=240=root count, det(Cartan E₈)=1          all TRUE

  Unlike the sibling `LeechLatticeArithmetic` (two brief numbers were
  false there), this brief required NO correction and NO drop.
-/
theorem verified_numbers : True := trivial

-- ══════════════════════════════════════════════════════════
-- SCOPE  (honesty over coverage)
-- ══════════════════════════════════════════════════════════
/--
  `deferred_scope` — honest scope marker.

  PROVED HERE (all kernel `decide`/`rfl`, Init-only):
    • σ₃(n) for n = 1..5 by decidable divisor-cube sum
    • r(2n) = 240·σ₃(n) for n = 1..5 (the head of E₄)
    • the products 240·{9,28,73,126}
    • r(0) = 1, r(2) = 240 = E₈ root count (SSOT tie to E8Lattice)
    • det(E₈ Cartan / Gram) = 1  ⇒  unimodular

  DEFERRED (NOT formalized here — needs far more than Init):
    • The MODULAR-FORMS identity Θ_{E₈} = E₄: that the theta series and
      the Eisenstein series agree as holomorphic modular forms of
      weight 4 for SL₂(ℤ), via dim M₄(SL₂ℤ) = 1.  We prove only the
      integer coefficient arithmetic.
    • The full counting theorem r(2n) = 240·σ₃(n) for ALL n (it follows
      from the modular-forms identity).  We prove the first five
      coefficients as decidable arithmetic shadows.
    • The uniqueness theorem (E₈ is the UNIQUE even unimodular lattice
      in dimension 8).  We prove only that THIS Gram matrix is even
      (diagonal 2) and unimodular (det 1).
    • The lattice itself as a subgroup of ℝ⁸; here the 240 minimal
      vectors live in E8Lattice (×2 scaled integer model).

  These shadows are TRUE and DECIDABLE; the analytic/uniqueness pieces
  are deferred honestly, exactly as `E8Lattice` and
  `LeechLatticeArithmetic` defer their continuous and Mathlib parts.
-/
theorem deferred_scope : True := trivial

end E8ThetaUnimodular
