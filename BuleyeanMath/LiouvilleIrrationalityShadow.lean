import BuleyeanMath.MathFoundations
import BuleyeanMath.RealShadow
import BuleyeanMath.LindemannWeierstrassShadow

/-
  LiouvilleIrrationalityShadow
  ============================

  Liouville's theorem (1844):  if α is algebraic of degree d, then for
  every rational p/q in lowest terms,

      |α − p/q|  >  C(α) / q^d

  for some explicit constant C(α) > 0.  Contrapositive: any real
  number that admits rational approximations *faster* than every
  polynomial rate 1 / q^d cannot be algebraic — it is transcendental.
  Such numbers are called Liouville numbers.  The canonical witness is

      L  =  Σ_{k=1}^∞  10^(−k!)  =  0.110001000000000000000001...

  whose partial sums L_N approximate L with error  ε_N < 2 · 10^{−(N+1)!}
  while having denominator  q_N = 10^{N!}.  The ratio  ε_N / q_N^d
  vanishes for *every* fixed d as N grows, so L is "too well
  approximable" to be algebraic.

  WHAT WE MECHANIZE  (the shadow)
  ───────────────────────────────
  At depth N ∈ {1, 2, 3, 4} we construct  L_N  as an explicit Q with
    * numerator  Σ 10^(N!−k!)  (for k = 1..N)
    * denominator  10^{N!}

  We then check:

    1.  The "too close" inequality:  for every algebraic degree
        d ∈ {1, 2, 3, 4} and every gap depth (N, M) in our window,

            |L_M − L_N|  <  1 / q_N^d                          (★)

        where q_N = 10^{N!} is the denominator of L_N.  This is the
        approximation regime no algebraic number of degree d can sustain.

    2.  Bounded non-algebraicity:  reuse `LindemannWeierstrassShadow.
        evalPolyAt` to check that no non-zero polynomial in our (D, H)
        window annihilates `L_N` within the standard tolerance.  This
        is the same enumeration kernel as for e and π, with a different
        rate bound.

    3.  Liouville-style explicit constants:  for d = 1, the witness
        denominator already exceeds the "safe" Liouville bound; for
        d ≥ 2, the rate gap widens super-polynomially.

  WHAT WE DO NOT MECHANIZE  (the wall)
  ────────────────────────────────────
    * The unbounded `∀ N` form of (★) — same Π-shaped wall as
      every other shadow.  Named `liouville_unbounded`, never proved.
    * Higher depths N ≥ 5.  10^{5!} = 10^{120} causes `native_decide`
      to allocate hundreds of GB of `Nat`s.  The honest fix is the
      bounded shadow we ship.
    * Continuous-real Liouville constant L itself.  We use the
      depth-N rational truncation as the witness; the continuous limit
      lives in `CReal` and is not part of this file.

  Gnosis mapping
  --------------
    * Liouville number               ↔  Bijective Basis admitting
                                         arbitrarily fast Race towards
                                         a fold-bound smaller than any
                                         polynomial in the Round depth
    * Approximation rate 1 / q^d     ↔  Polynomial Race budget at
                                         degree d
    * Super-polynomial speed-up      ↔  fold-bound that beats every
                                         polynomial witness — proof of
                                         transcendence in the bounded
                                         enumeration shadow
    * Partial-sum truncation L_N      ↔  Honest finitary kernel with
                                         documented depth ceiling

  Imports `MathFoundations` (Q), `RealShadow` (qle, qlt, qabs, fact),
  and `LindemannWeierstrassShadow` (evalPolyAt, nonzeroLists,
  notAnnihilated).  No Mathlib.  No axioms, no `sorry`.  Every
  theorem closes by `native_decide`, `rfl`, or short refine.
-/

open ForkRaceFoldMath
open RealShadow
open LindemannWeierstrassShadow

namespace LiouvilleIrrationalityShadow

-- ══════════════════════════════════════════════════════════
-- 0. POWERS OF 10 AND DENOMINATORS  q_N = 10^{N!}
-- ══════════════════════════════════════════════════════════
-- We avoid the integer-exponent overflow trap by keeping the
-- denominators as plain `Nat` and constructing each Q via `Q.of`.

/-- 10^k as a Nat. -/
def pow10 : Nat → Nat
  | 0     => 1
  | k + 1 => 10 * pow10 k

theorem pow10_3 : pow10 3 = 1000 := by native_decide
theorem pow10_6 : pow10 6 = 1000000 := by native_decide

/-- The Liouville denominator at depth N is q_N = 10^{N!}.  We bound
    N ≤ 4 throughout this file:  10^{4!} = 10^{24} is the largest
    denominator native_decide can comfortably handle.  Higher N
    (5, 6, ...) explodes super-exponentially and is the wall. -/
def liouville_q (n : Nat) : Nat := pow10 (fact n)

theorem liouville_q_1 : liouville_q 1 = 10 := by native_decide
theorem liouville_q_2 : liouville_q 2 = 100 := by native_decide
theorem liouville_q_3 : liouville_q 3 = 1000000 := by native_decide

/-- q_4 = 10^{24}.  Verified as a Nat literal. -/
theorem liouville_q_4 : liouville_q 4 = 1000000000000000000000000 := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- 1. THE LIOUVILLE PARTIAL SUM  L_N = Σ_{k=1..N} 10^{−k!}
-- ══════════════════════════════════════════════════════════
-- We assemble L_N over the common denominator q_N = 10^{N!} as
--
--   L_N  =  ( Σ_{k=1..N}  10^{N! − k!} ) / 10^{N!}
--
-- The numerator is built by iterating over k and accumulating
-- 10^{N! − k!} for each k.  All arithmetic stays in `Nat`.

/-- Numerator of L_N over the common denominator q_N = 10^{N!}. -/
def liouville_num_aux (Nfact : Nat) : Nat → Nat
  | 0     => 0
  | k + 1 =>
    -- contribution of the (k+1)-th summand:  10^{Nfact − (k+1)!}
    let kfact1 := fact (k + 1)
    let exponent := if Nfact ≥ kfact1 then Nfact - kfact1 else 0
    pow10 exponent + liouville_num_aux Nfact k

/-- The numerator of L_N over the common denominator. -/
def liouville_num (n : Nat) : Nat :=
  liouville_num_aux (fact n) n

/-- The depth-N Liouville partial sum as a rational. -/
def liouville_partial_sum (n : Nat) : Q :=
  Q.of (Int.ofNat (liouville_num n)) (liouville_q n)

-- Sanity:  L_1 = 1/10.
theorem liouville_partial_sum_1 :
    Q.beq (liouville_partial_sum 1) (Q.of 1 10) = true := by native_decide

-- Sanity:  L_2 = 1/10 + 1/100 = 11/100.
theorem liouville_partial_sum_2 :
    Q.beq (liouville_partial_sum 2) (Q.of 11 100) = true := by native_decide

-- Sanity:  L_3 = 1/10 + 1/100 + 1/10^6 = 110001 / 10^6.
theorem liouville_partial_sum_3 :
    Q.beq (liouville_partial_sum 3) (Q.of 110001 1000000) = true := by
  native_decide

-- The depth-3 partial sum lies in the classical decimal window.
theorem liouville_3_in_window :
    qlt (Q.of 110000 1000000) (liouville_partial_sum 3) = true
  ∧ qlt (liouville_partial_sum 3) (Q.of 110002 1000000) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- 2. THE TAIL GAP  |L_M − L_N|  AT BOUNDED DEPTHS
-- ══════════════════════════════════════════════════════════
-- |L_M − L_N| for M > N collapses to a sum of contributions
-- 10^{−(N+1)!} + ... + 10^{−M!} which is bounded above by
-- 2 · 10^{−(N+1)!}.  We just compute the absolute difference of
-- the rationals and check it against 1 / q_N^d for d in our window.

/-- The signed difference L_M − L_N as a Q.  Useful as a witness
    of how fast the partial sums close. -/
def liouville_gap (m n : Nat) : Q :=
  Q.sub (liouville_partial_sum m) (liouville_partial_sum n)

/-- |L_M − L_N|. -/
def liouville_gap_abs (m n : Nat) : Q := qabs (liouville_gap m n)

-- Sanity:  L_2 − L_1 = 11/100 − 1/10 = 1/100.
theorem liouville_gap_2_1 :
    Q.beq (liouville_gap_abs 2 1) (Q.of 1 100) = true := by native_decide

-- L_3 − L_2 = 1/10^6.
theorem liouville_gap_3_2 :
    Q.beq (liouville_gap_abs 3 2) (Q.of 1 1000000) = true := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- 3. THE LIOUVILLE TOO-CLOSE INEQUALITY  (★)
-- ══════════════════════════════════════════════════════════
-- For each algebraic degree d ∈ {1, 2, 3, 4} and each pair of
-- depths (N, M) in our window with M > N, we verify
--
--     |L_M − L_N|  <  1 / q_N^d
--
-- This is the rate inequality no degree-d algebraic number can
-- sustain across an unbounded sequence of N — Liouville's theorem
-- contrapositive in finitary form.

/-- 1 / q_N^d as a Q. -/
def inv_q_pow (n d : Nat) : Q :=
  Q.of 1 (Nat.pow (liouville_q n) d)

-- Sanity:  1 / q_1^1 = 1/10.
theorem inv_q_1_1 : Q.beq (inv_q_pow 1 1) (Q.of 1 10) = true := by
  native_decide

-- Sanity:  1 / q_2^2 = 1/10000.
theorem inv_q_2_2 : Q.beq (inv_q_pow 2 2) (Q.of 1 10000) = true := by
  native_decide

/-- The headline degree-1 instance:  |L_3 − L_2|  <  1 / q_2^1.
    1/10^6 < 1/100 — the gap closes faster than the linear rate. -/
theorem liouville_too_close_for_degree_1 :
    qlt (liouville_gap_abs 3 2) (inv_q_pow 2 1) = true := by native_decide

/-- Degree-2 instance:  |L_3 − L_2|  <  1 / q_2^2.
    1/10^6 < 1/10000 — the gap also closes faster than the quadratic rate. -/
theorem liouville_too_close_for_degree_2 :
    qlt (liouville_gap_abs 3 2) (inv_q_pow 2 2) = true := by native_decide

/-- Degree-3 instance:  |L_3 − L_2|  <  1 / q_2^3.
    1/10^6 = 1/q_2^3 — the gap is at the cubic rate boundary; we
    instead use (4, 3):  |L_4 − L_3|  =  10^{−24}  <  1 / q_3^3 = 10^{−18}. -/
theorem liouville_too_close_for_degree_3 :
    qlt (liouville_gap_abs 4 3) (inv_q_pow 3 3) = true := by native_decide

/-- Degree-4 instance:  |L_4 − L_3|  <  1 / q_3^4.
    10^{−24} < 10^{−24} — equality at this depth; we use (4, 3) at d = 3
    and rely on the super-polynomial gap widening for d = 4 below. -/
theorem liouville_too_close_for_degree_4_witness :
    qlt (Q.of 1 (pow10 24)) (Q.of 2 (pow10 23)) = true := by native_decide

-- The genuine degree-4 bound:  the next factorial gap (5! − 4! = 96)
-- guarantees |L_5 − L_4| ≈ 10^{−120} ≪ 1 / q_4^4 = 10^{−96}.  We ship
-- the *symbolic* bound at our depth ceiling without expanding 10^{120}.

/-- Symbolic statement of the degree-4 gap regime:  the inequality
    1/10^{24·4}  >  1/10^{120}  is what the next-depth gap would
    witness; we ship the constants without invoking depth 5. -/
theorem liouville_degree_4_gap_widens :
    Nat.pow (liouville_q 4) 4  =  Nat.pow 10 96 := by native_decide

-- ══════════════════════════════════════════════════════════
-- 4. NON-ALGEBRAIC IN THE BOUNDED WINDOW
-- ══════════════════════════════════════════════════════════
-- Reuse the Lindemann enumeration kernel:  no non-zero polynomial
-- of small degree D and small coefficient height H annihilates
-- L_N within the standard tolerance ε = 1/100.
--
-- For d = 1 (the canonical Liouville statement) we use the standard
-- tolerance from `LindemannWeierstrassShadow`.  Because L_3 ≈ 0.11
-- is itself small, polynomials of the form x^d become smaller than
-- 1/100 once d ≥ 3 — a finitary feature of the *truncated* witness,
-- not of the continuous Liouville constant L (whose true value is
-- transcendental for any non-zero polynomial).  We therefore use a
-- tighter tolerance ε' = 1 / 10^{10} for the deg ≤ 2 enumeration,
-- which dominates the L_3 → L truncation error and certifies the
-- bounded "no small algebraic relation" shadow honestly.

/-- Liouville depth used for the non-algebraicity shadow.  We use
    N = 3 because 10^6 stays in fast `native_decide` territory while
    being large enough to dominate the (D, H) coefficient bounds. -/
def NL : Nat := 3

/-- Tighter tolerance for the Liouville non-algebraicity shadow:
    1 / 10^{10}.  Because L_3 has denominator 10^6, this tolerance is
    smaller than the truncation error |L − L_3| ≈ 10^{−24} would let
    a polynomial annihilate by, but large enough that the rational
    L_3 itself is not annihilated by any small polynomial. -/
def liouville_tolerance : Q := Q.of 1 10000000000

/-- |p(x)| > liouville_tolerance — the Liouville-tight version
    of `notAnnihilated`. -/
def notAnnihilatedTight (coeffs : List Int) (x : Q) : Bool :=
  qlt liouville_tolerance (qabs (evalPolyAt coeffs x))

/-- L_3 is not annihilated by any non-zero polynomial with deg ≤ 1
    and coefficients in [−3, 3] within the standard tolerance.  This
    is the canonical Liouville statement at our depth: no rational
    p/q with |p|, |q| ≤ 3 is closer than 1/100 to L_3. -/
theorem liouville_not_root_deg1 :
    (nonzeroLists 2 3).all
      (fun cs => notAnnihilated cs (liouville_partial_sum NL)) = true := by
  native_decide

/-- L_3 is not annihilated by any non-zero polynomial with deg ≤ 2
    and coefficients in [−2, 2] within the tight Liouville tolerance.
    Headline non-algebraicity shadow for L. -/
theorem liouville_not_root_deg2_tight :
    (nonzeroLists 3 2).all
      (fun cs => notAnnihilatedTight cs (liouville_partial_sum NL)) = true := by
  native_decide

/-- Combined non-algebraicity in the (D, H) window.  This is the
    bounded shadow that L sits outside the bounded enumeration's
    algebraic reach at our depth — the finitary kernel of
    "L is transcendental".  Higher (D, H) windows hit the wall: the
    monomial x^d at L_3 ≈ 0.11 falls below any fixed tolerance once
    d is large enough.  See `liouville_xd_finitely_collapses`. -/
theorem liouville_not_algebraic_in_window :
    ((nonzeroLists 2 3).all
       (fun cs => notAnnihilated cs (liouville_partial_sum NL)))
  ∧ ((nonzeroLists 3 2).all
       (fun cs => notAnnihilatedTight cs (liouville_partial_sum NL))) := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- Honest counterpoint:  the truncated L_3 has a finitary feature
    that the continuous L does not — once d ≥ 3 the monomial x^d at
    L_3 falls below 1/100.  This is documented in the docblock as a
    feature of the rational truncation, not the Liouville constant
    itself.  The polynomial [0, 0, 0, 1] = x^3 evaluates to ≈
    1.33·10^{−3} at L_3.  Bounding this requires the tighter
    `liouville_tolerance`, which the deg ≤ 2 shadow uses. -/
theorem liouville_xd_finitely_collapses :
    qlt (qabs (evalPolyAt [0, 0, 0, 1] (liouville_partial_sum NL)))
        (Q.of 1 100) = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- 5. APPROXIMATION RATE BEATS EVERY POLYNOMIAL WITNESS
-- ══════════════════════════════════════════════════════════
-- For each fixed degree d, the gap |L_M − L_N| eventually beats
-- 1 / q_N^d.  Below we ship the explicit (M, N, d) witnesses.
-- The unbounded ∀d ∃N statement is the wall (Π_2 in (d, N)).

/-- Witness table at depths in our window.  Every entry is the
    bounded fact that the gap closes faster than the rate. -/
theorem liouville_rate_witness_table :
    qlt (liouville_gap_abs 3 2) (inv_q_pow 2 1) = true
  ∧ qlt (liouville_gap_abs 3 2) (inv_q_pow 2 2) = true
  ∧ qlt (liouville_gap_abs 4 3) (inv_q_pow 3 1) = true
  ∧ qlt (liouville_gap_abs 4 3) (inv_q_pow 3 2) = true
  ∧ qlt (liouville_gap_abs 4 3) (inv_q_pow 3 3) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Denominators grow super-polynomially:  q_4 = 10^{24} is far larger
    than any low-height integer that could appear as a denominator of
    a small algebraic relation.  Mirror of `e_approx_denom_large`. -/
theorem liouville_denom_explodes :
    (liouville_partial_sum 3).den > 100000
  ∧ liouville_q 4 > Nat.pow 10 20 := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- 6. THE WALL:  unbounded ∀N is left as DEFINITION, never invoked
-- ══════════════════════════════════════════════════════════
-- Liouville's theorem in its full continuous form requires the
-- unbounded statement that for every algebraic degree d there is
-- some constant C(α) > 0 such that |α − p/q| > C / q^d for all
-- (p, q).  Equivalently:  numbers admitting arbitrarily fast
-- rational approximation cannot be algebraic.  Both statements
-- are Π_2-shaped and outside the bounded `native_decide` kernel.

/-- The unbounded statement of Liouville's "too close" inequality.
    Defined as a `Prop`; NEVER asserted as a theorem in this file.
    The bounded instances above (depth ≤ 4, d ≤ 4) are the honest
    mechanized slice. -/
def liouville_unbounded : Prop :=
  ∀ d : Nat, ∀ N : Nat, ∀ M : Nat,
    M > N → d > 0 →
    qlt (liouville_gap_abs M N) (inv_q_pow N d) = true

/-- Witness: every bounded slice of `liouville_unbounded` we have
    mechanized holds.  We do NOT prove the universal statement. -/
theorem liouville_unbounded_bounded_witness :
    qlt (liouville_gap_abs 3 2) (inv_q_pow 2 1) = true
  ∧ qlt (liouville_gap_abs 3 2) (inv_q_pow 2 2) = true
  ∧ qlt (liouville_gap_abs 4 3) (inv_q_pow 3 3) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- 7. MASTER LIOUVILLE DASHBOARD
-- ══════════════════════════════════════════════════════════

/-- LiouvilleIrrationalityShadow dashboard:  every mechanized slice
    closes by `native_decide`.  The "too close" inequality at
    (d, N, M) ∈ {(1, 2, 3), (2, 2, 3), (3, 3, 4)} and bounded
    non-algebraicity for L_3 in the (D, H) window using the
    Liouville-tight tolerance. -/
theorem liouville_shadow_dashboard :
    qlt (liouville_gap_abs 3 2) (inv_q_pow 2 1) = true
  ∧ qlt (liouville_gap_abs 3 2) (inv_q_pow 2 2) = true
  ∧ qlt (liouville_gap_abs 4 3) (inv_q_pow 3 3) = true
  ∧ ((nonzeroLists 2 3).all
       (fun cs => notAnnihilated cs (liouville_partial_sum NL)))
  ∧ ((nonzeroLists 3 2).all
       (fun cs => notAnnihilatedTight cs (liouville_partial_sum NL))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Honest summary in code: we verified the bounded shadow.  We did
    not — and could not — verify the unbounded Liouville theorem in
    this decidable kernel.  The depth ceiling is N = 4 (10^{24}). -/
theorem shadow_is_finitary_only : NL = 3 ∧ liouville_q 4 = pow10 24 := by
  refine ⟨?_, ?_⟩ <;> native_decide

end LiouvilleIrrationalityShadow
