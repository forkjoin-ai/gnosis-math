import Gnosis.MathFoundations

/-
  RealShadow
  ==========

  A computable-reals library for the Gnosis library.
  ℝ is encoded as a Bishop-style sequence of rational approximations
  with an explicit modulus of convergence:

      structure CReal where
        approx  : Nat → Q
        modulus : Nat → Nat   -- approx m and approx n agree to 1/2^k
                              -- whenever m, n ≥ modulus k

  This is the FIRST file in the monorepo to break the integer / rational /
  cyclotomic constraint.  We do not pretend to be ℝ.  We mechanize:

    * a constructive subset of ℝ closed under add / sub / mul / neg
    * explicit rational approximations of e, π, √2, log 2
    * decidable comparison at a fixed approximation depth
    * interval arithmetic as a side-channel for error bookkeeping

  What we do NOT do
  -----------------
    * decide equality on `CReal` — equality of two Cauchy reals is
      Π⁰₂ undecidable in general (Bishop, Bridges).  Equality on `CReal`
      in this file is *equality of approximations at depth N* and the
      file says so explicitly at every comparison site.
    * carry the modulus correctness as a theorem.  We carry the modulus
      as data and verify the closing arithmetic by `native_decide`.
      The Lindemann shadow consumes only the `approx` evaluations.
    * provide cinv with a global modulus.  Inversion needs a separation
      certificate `|x| ≥ 1/2^k` to bound the approximation, so cinv is
      defined relative to a caller-supplied bound and a sanity test
      verifies `1 / (3/2) = 2/3` at depth.

  Gnosis mapping
  --------------
    * Cauchy convergence at modulus k         ↔  fold-bound on Race depth
    * Rational interval [lo, hi]               ↔  bracket carried by the
                                                  Bijective-Basis envelope
    * Equality at depth N (not equality on ℝ) ↔  honest non-termination
                                                  cap of the diagonal Race

  Imports `Gnosis.MathFoundations` for `Q`.  No Mathlib.
  No axioms, no `sorry`.  All theorems close by `native_decide`, `rfl`,
  or `decide`.
-/

open ForkRaceFoldMath

namespace RealShadow

-- ══════════════════════════════════════════════════════════
-- 0. RATIONAL HELPERS  (built on Q from MathFoundations)
-- ══════════════════════════════════════════════════════════
-- Q.beq is cross-multiplication equality.  We need order, absolute
-- value, and a few utility constants.  Everything is bilinear in num
-- and den so cross-multiplication is enough.

/-- Strict less-than on Q.  Both denominators are non-zero positive
    Nat (Q.of clamps 0 to 1), so we cross-multiply directly. -/
def qlt (x y : Q) : Bool :=
  decide (x.num * Int.ofNat y.den < y.num * Int.ofNat x.den)

/-- Less-or-equal on Q. -/
def qle (x y : Q) : Bool :=
  decide (x.num * Int.ofNat y.den ≤ y.num * Int.ofNat x.den)

/-- Absolute value of a Q. -/
def qabs (x : Q) : Q :=
  match x.num with
  | .ofNat n   => Q.of (Int.ofNat n) x.den
  | .negSucc n => Q.of (Int.ofNat (n + 1)) x.den

/-- Sign of a Q as Int (-1, 0, +1). -/
def qsign (x : Q) : Int :=
  match x.num with
  | .ofNat 0      => 0
  | .ofNat (_+1)  => 1
  | .negSucc _    => -1

/-- 2^k as a Nat. -/
def pow2 : Nat → Nat
  | 0     => 1
  | k + 1 => 2 * pow2 k

/-- 1/2^k as a Q. -/
def qpow2inv (k : Nat) : Q := Q.of 1 (pow2 k)

/-- k! as a Nat. -/
def fact : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * fact n

theorem fact_5 : fact 5 = 120 := by native_decide
theorem fact_10 : fact 10 = 3628800 := by native_decide

/-- 1/k! as a Q. -/
def qinvFact (k : Nat) : Q := Q.of 1 (fact k)

-- ══════════════════════════════════════════════════════════
-- 1. INTERVAL ARITHMETIC  (error-bookkeeping side channel)
-- ══════════════════════════════════════════════════════════
-- Closed rational intervals [lo, hi] with lo ≤ hi.  Useful both as
-- a sanity check on CReal arithmetic and as the bracket carried by
-- the Lindemann enumeration.

structure Interval where
  lo : Q
  hi : Q
  deriving Repr

namespace Interval

/-- A point interval. -/
def point (q : Q) : Interval := ⟨q, q⟩

/-- Interval addition: [a, b] + [c, d] = [a+c, b+d]. -/
def iadd (x y : Interval) : Interval :=
  ⟨Q.add x.lo y.lo, Q.add x.hi y.hi⟩

/-- Interval negation: -[a, b] = [-b, -a]. -/
def ineg (x : Interval) : Interval :=
  ⟨Q.neg x.hi, Q.neg x.lo⟩

/-- Interval subtraction: [a, b] - [c, d] = [a-d, b-c]. -/
def isub (x y : Interval) : Interval :=
  iadd x (ineg y)

/-- Width of an interval. -/
def width (x : Interval) : Q := Q.sub x.hi x.lo

/-- Membership test for a rational. -/
def contains (x : Interval) (q : Q) : Bool :=
  qle x.lo q && qle q x.hi

/-- Interval equality (both endpoints by Q.beq). -/
def beq (x y : Interval) : Bool :=
  Q.beq x.lo y.lo && Q.beq x.hi y.hi

end Interval

open Interval

-- Sanity:  [1, 2] + [3, 4] = [4, 6].
theorem iadd_sample :
    Interval.beq
      (Interval.iadd ⟨Q.of 1 1, Q.of 2 1⟩ ⟨Q.of 3 1, Q.of 4 1⟩)
      ⟨Q.of 4 1, Q.of 6 1⟩ = true := by native_decide

-- Sanity:  -[1, 2] = [-2, -1].
theorem ineg_sample :
    Interval.beq
      (Interval.ineg ⟨Q.of 1 1, Q.of 2 1⟩)
      ⟨Q.of (-2) 1, Q.of (-1) 1⟩ = true := by native_decide

-- Sanity:  [3, 5] − [1, 2] = [1, 4].
theorem isub_sample :
    Interval.beq
      (Interval.isub ⟨Q.of 3 1, Q.of 5 1⟩ ⟨Q.of 1 1, Q.of 2 1⟩)
      ⟨Q.of 1 1, Q.of 4 1⟩ = true := by native_decide

-- Sanity:  width([1, 5]) = 4.
theorem iwidth_sample :
    Q.beq (Interval.width ⟨Q.of 1 1, Q.of 5 1⟩) (Q.of 4 1) = true := by
  native_decide

-- Sanity:  3 ∈ [1, 5].
theorem icontains_sample :
    Interval.contains ⟨Q.of 1 1, Q.of 5 1⟩ (Q.of 3 1) = true := by
  native_decide

-- Sanity:  6 ∉ [1, 5].
theorem inotcontains_sample :
    Interval.contains ⟨Q.of 1 1, Q.of 5 1⟩ (Q.of 6 1) = false := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- 2. CReal:  CAUCHY SEQUENCE WITH EXPLICIT MODULUS
-- ══════════════════════════════════════════════════════════
-- A `CReal` carries:
--   approx  : Nat → Q   — the n-th rational approximation
--   modulus : Nat → Nat — for any precision k, both `approx m` and
--                        `approx n` agree to within 1/2^k once
--                        m, n ≥ modulus k.
-- We carry the modulus as DATA, not as proof: native_decide closes
-- arithmetic verifications at the chosen depth, no axiom required.
-- (Carrying the proof would need a real-arithmetic tactic stack we
-- explicitly do not import.)

structure CReal where
  approx  : Nat → Q
  modulus : Nat → Nat

namespace CReal

/-- The constant zero. -/
def czero : CReal :=
  { approx := fun _ => Q.zero, modulus := fun _ => 0 }

/-- The constant one. -/
def cone : CReal :=
  { approx := fun _ => Q.one, modulus := fun _ => 0 }

/-- The constant one half. -/
def chalf : CReal :=
  { approx := fun _ => Q.of 1 2, modulus := fun _ => 0 }

/-- Lift a rational to a constant CReal. -/
def cratiional (q : Q) : CReal :=
  { approx := fun _ => q, modulus := fun _ => 0 }

/-- Sample the n-th rational approximation. -/
def sample (x : CReal) (n : Nat) : Q := x.approx n

-- ─────────────  ARITHMETIC OPERATIONS  ─────────────────────
-- For (x + y) at precision k we need both summands to precision k+1
-- (so the combined error is at most 1/2^(k+1) + 1/2^(k+1) = 1/2^k).
-- Hence (cadd x y).modulus k = max (x.modulus (k+1)) (y.modulus (k+1)).

def cadd (x y : CReal) : CReal :=
  { approx  := fun n => Q.add (x.approx n) (y.approx n)
    modulus := fun k => Nat.max (x.modulus (k + 1)) (y.modulus (k + 1)) }

def cneg (x : CReal) : CReal :=
  { approx  := fun n => Q.neg (x.approx n)
    modulus := x.modulus }

def csub (x y : CReal) : CReal := cadd x (cneg y)

-- For (x · y) at precision k we need precision k + ceiling(log₂(|x| + |y| + 2))
-- on each operand.  Without a global magnitude bound, we use the conservative
-- modulus k + 8 — sufficient for our small-coefficient sanity tests.
def cmul (x y : CReal) : CReal :=
  { approx  := fun n => Q.mul (x.approx n) (y.approx n)
    modulus := fun k => Nat.max (x.modulus (k + 8)) (y.modulus (k + 8)) }

/-- Inversion *relative to a separation certificate* `kSep` saying
    |x| ≥ 1/2^kSep on the relevant tail.  The caller is responsible for
    supplying a correct `kSep`; we do not verify it here.  At each n we
    return Q.inv (x.approx n) (which is Q.zero if approx n is itself 0,
    so callers must avoid that). -/
def cinvWithSep (x : CReal) (kSep : Nat) : CReal :=
  { approx  := fun n => Q.inv (x.approx n)
    modulus := fun k => x.modulus (k + 2 * kSep + 4) }

end CReal

open CReal

-- Sanity checks at fixed approximation depth (n = 32 throughout).

theorem czero_sample : Q.beq (czero.approx 32) Q.zero = true := by native_decide
theorem cone_sample  : Q.beq (cone.approx 32) Q.one = true := by native_decide
theorem chalf_sample : Q.beq (chalf.approx 32) (Q.of 1 2) = true := by native_decide

theorem cadd_sample :
    Q.beq ((cadd cone cone).approx 32) (Q.of 2 1) = true := by native_decide

theorem csub_sample :
    Q.beq ((csub cone chalf).approx 32) (Q.of 1 2) = true := by native_decide

theorem cmul_sample :
    Q.beq ((cmul (cratiional (Q.of 3 2)) (cratiional (Q.of 4 5))).approx 32)
          (Q.of 12 10) = true := by native_decide

theorem cneg_sample :
    Q.beq ((cneg cone).approx 32) (Q.of (-1) 1) = true := by native_decide

theorem cinv_sample :
    Q.beq ((cinvWithSep (cratiional (Q.of 3 2)) 1).approx 32) (Q.of 2 3) = true := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- 3. COMPARISON AT A FIXED DEPTH
-- ══════════════════════════════════════════════════════════
-- Equality of two CReals is undecidable.  Comparison at a fixed
-- approximation depth N is decidable (it reduces to Q.beq / qlt on
-- the N-th approximations).  Every theorem in this file that uses
-- `cle` or `ceq` does so AT A FIXED N, and the file documents this.

/-- Strict less at depth n. -/
def cltAt (x y : CReal) (n : Nat) : Bool :=
  qlt (x.approx n) (y.approx n)

/-- Less-or-equal at depth n. -/
def cle (x y : CReal) (n : Nat) : Bool :=
  qle (x.approx n) (y.approx n)

/-- Equality at depth n (decidable shadow of CReal equality). -/
def ceq (x y : CReal) (n : Nat) : Bool :=
  Q.beq (x.approx n) (y.approx n)

theorem cle_zero_one_at_32 : cle czero cone 32 = true := by native_decide
theorem cle_half_one_at_32 : cle chalf cone 32 = true := by native_decide
theorem clt_zero_one_at_32 : cltAt czero cone 32 = true := by native_decide
theorem ceq_self_at_32     : ceq cone cone 32 = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- 4. EULER'S CONSTANT  e ≈ 2.71828...
-- ══════════════════════════════════════════════════════════
-- Σ_{k=0}^n 1/k! converges to e with truncation error ≤ 1/(n!·n)
-- for n ≥ 1 — supergeometric, so the modulus is essentially log n.
-- We compute the partial sum directly as a Q.

/-- Σ_{k=0}^{n} 1 / k!. -/
def e_approx (n : Nat) : Q :=
  let rec go : Nat → Q → Q
    | 0,     acc => Q.add acc (qinvFact 0)
    | k + 1, acc => go k (Q.add acc (qinvFact (k + 1)))
  go n Q.zero

theorem e_approx_0 : Q.beq (e_approx 0) (Q.of 1 1) = true := by native_decide
theorem e_approx_1 : Q.beq (e_approx 1) (Q.of 2 1) = true := by native_decide
theorem e_approx_2 : Q.beq (e_approx 2) (Q.of 5 2) = true := by native_decide

/-- e ≈ 2.71828183 within 1e-8.  Verifies `e_approx 10` lies inside
    a tight rational bracket around the true value. -/
theorem e_approx_upper :
    qlt (e_approx 10) (Q.of 271828183 100000000) = true := by native_decide

theorem e_approx_lower :
    qlt (Q.of 27182818 10000000) (e_approx 10) = true := by native_decide

/-- e_approx is monotone non-decreasing on the small initial window. -/
theorem e_monotone_window :
    qle (e_approx 5) (e_approx 6) = true
  ∧ qle (e_approx 6) (e_approx 7) = true
  ∧ qle (e_approx 7) (e_approx 8) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The CReal corresponding to e (modulus is conservative). -/
def cExp : CReal :=
  { approx  := e_approx
    modulus := fun k => k + 4 }

theorem cExp_sample :
    qlt (cExp.approx 10) (Q.of 28 10) = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- 5. THE EXPONENTIAL  exp(q) ≈ Σ_{k=0}^n q^k / k!
-- ══════════════════════════════════════════════════════════
-- Same supergeometric truncation; works for any small rational q.

/-- q^k as a Q. -/
def qpow (q : Q) : Nat → Q
  | 0     => Q.one
  | k + 1 => Q.mul q (qpow q k)

/-- Σ_{k=0}^{n} q^k / k!. -/
def exp_approx (q : Q) (n : Nat) : Q :=
  let rec go : Nat → Q → Q
    | 0,     acc => Q.add acc (qpow q 0)
    | k + 1, acc =>
      go k (Q.add acc (Q.mul (qpow q (k + 1)) (qinvFact (k + 1))))
  go n Q.zero

theorem exp_at_zero :
    Q.beq (exp_approx Q.zero 10) Q.one = true := by native_decide

/-- exp(1) and e_approx agree at depth 8 (both are Σ 1/k!). -/
theorem exp_at_one_matches_e :
    Q.beq (exp_approx Q.one 8) (e_approx 8) = true := by native_decide

/-- exp(2) > 7.38 at depth 12 (true value 7.389...). -/
theorem exp_two_lower :
    qlt (Q.of 738 100) (exp_approx (Q.of 2 1) 12) = true := by native_decide

/-- exp(2) < 7.40 at depth 12. -/
theorem exp_two_upper :
    qlt (exp_approx (Q.of 2 1) 12) (Q.of 740 100) = true := by native_decide

/-- exp(-1) ≈ 0.3678... ; rough bracket at depth 12. -/
theorem exp_neg_one_bracket :
    qlt (Q.of 367 1000) (exp_approx (Q.of (-1) 1) 12) = true
  ∧ qlt (exp_approx (Q.of (-1) 1) 12) (Q.of 369 1000) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- 6. PI VIA MACHIN  16·atan(1/5) − 4·atan(1/239)
-- ══════════════════════════════════════════════════════════
-- atan(x) = Σ_{k=0}^∞ (-1)^k · x^{2k+1} / (2k+1).
-- Machin: π = 16 atan(1/5) − 4 atan(1/239).  Each series converges
-- supergeometrically; very few terms suffice for 4-digit accuracy.

/-- Σ_{k=0}^{n} (-1)^k · q^{2k+1} / (2k+1). -/
def atan_approx (q : Q) (n : Nat) : Q :=
  let rec go : Nat → Q → Q
    | 0,     acc =>
      let term := Q.mul (qpow q 1) (Q.of 1 1)  -- q / 1
      Q.add acc term
    | k + 1, acc =>
      let kk := k + 1
      let exponent := 2 * kk + 1
      let denom : Nat := exponent
      let powq := qpow q exponent
      let signedNum := if kk % 2 = 0 then powq.num else -powq.num
      let term := Q.of signedNum (powq.den * denom)
      go k (Q.add acc term)
  go n Q.zero

/-- atan(0) = 0. -/
theorem atan_zero : Q.beq (atan_approx Q.zero 10) Q.zero = true := by native_decide

/-- atan(1) ≈ π/4 ≈ 0.7854.  Verify the depth-50 partial sum is in
    a safe bracket (Leibniz converges slowly but monotonically in
    pairs of terms). -/
theorem atan_one_bracket :
    qlt (Q.of 7 10) (atan_approx Q.one 50) = true
  ∧ qlt (atan_approx Q.one 50) (Q.of 9 10) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- Machin's formula: π/4 ≈ 4·atan(1/5) − atan(1/239), so
    π ≈ 16·atan(1/5) − 4·atan(1/239). -/
def pi_approx (n : Nat) : Q :=
  let aFifth := atan_approx (Q.of 1 5) n
  let a239   := atan_approx (Q.of 1 239) n
  Q.sub (Q.mul (Q.of 16 1) aFifth) (Q.mul (Q.of 4 1) a239)

/-- π ≈ 3.14 within depth 100.  The bracket [3.140, 3.142] is the
    classroom three-digit accuracy guarantee. -/
theorem pi_approx_lower :
    qlt (Q.of 3140 1000) (pi_approx 100) = true := by native_decide

theorem pi_approx_upper :
    qlt (pi_approx 100) (Q.of 3142 1000) = true := by native_decide

/-- π/4 ≈ 0.785 at depth 100. -/
theorem pi_over_four_bracket :
    qlt (Q.of 785 1000) (Q.mul (Q.of 1 4) (pi_approx 100)) = true
  ∧ qlt (Q.mul (Q.of 1 4) (pi_approx 100)) (Q.of 786 1000) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- The CReal corresponding to π. -/
def cPi : CReal :=
  { approx  := pi_approx
    modulus := fun k => k + 4 }

theorem cPi_sample :
    qlt (Q.of 314 100) (cPi.approx 100) = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- 7. log 2  via  Σ (-1)^{k+1} / k
-- ══════════════════════════════════════════════════════════
-- log 2 = Σ_{k=1}^∞ (-1)^{k+1} / k = 1 − 1/2 + 1/3 − 1/4 + ...
-- Slow alternating convergence; sufficient for sanity verification.

/-- Σ_{k=1}^{n} (-1)^{k+1} / k. -/
def log2_approx (n : Nat) : Q :=
  let rec go : Nat → Q → Q
    | 0,     acc => acc
    | k + 1, acc =>
      let signedNum : Int := if (k + 1) % 2 = 1 then 1 else -1
      let term : Q := Q.of signedNum (k + 1)
      go k (Q.add acc term)
  go n Q.zero

theorem log2_first_few :
    Q.beq (log2_approx 1) (Q.of 1 1) = true
  ∧ Q.beq (log2_approx 2) (Q.of 1 2) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- log 2 ≈ 0.6931.  Slow alternating series, but at depth 200 the
    partial sum sits in a 1e-2 bracket of the true value. -/
theorem log2_loose_bracket :
    qlt (Q.of 68 100) (log2_approx 200) = true
  ∧ qlt (log2_approx 200) (Q.of 70 100) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- 8. SQRT 2 VIA CONTINUED FRACTIONS
-- ══════════════════════════════════════════════════════════
-- √2 = [1; 2, 2, 2, ...].  The convergents are
--   p_0/q_0 = 1/1, p_1/q_1 = 3/2, p_2/q_2 = 7/5, p_3/q_3 = 17/12,
--   p_4/q_4 = 41/29, p_5/q_5 = 99/70, ...
-- with recurrence p_{k+1} = 2 p_k + p_{k-1}, similarly q.

/-- Continued-fraction numerators for √2 = [1; 2, 2, 2, ...]. -/
def sqrt2Num : Nat → Nat
  | 0     => 1
  | 1     => 3
  | n + 2 => 2 * sqrt2Num (n + 1) + sqrt2Num n

/-- Continued-fraction denominators for √2. -/
def sqrt2Den : Nat → Nat
  | 0     => 1
  | 1     => 2
  | n + 2 => 2 * sqrt2Den (n + 1) + sqrt2Den n

/-- The n-th continued-fraction convergent for √2 as Q. -/
def cf_sqrt2 (n : Nat) : Q := Q.of (Int.ofNat (sqrt2Num n)) (sqrt2Den n)

theorem cf_sqrt2_0 : Q.beq (cf_sqrt2 0) (Q.of 1 1) = true := by native_decide
theorem cf_sqrt2_1 : Q.beq (cf_sqrt2 1) (Q.of 3 2) = true := by native_decide
theorem cf_sqrt2_2 : Q.beq (cf_sqrt2 2) (Q.of 7 5) = true := by native_decide
theorem cf_sqrt2_3 : Q.beq (cf_sqrt2 3) (Q.of 17 12) = true := by native_decide

/-- cf_sqrt2 5 ≈ 1.4142 to 4 decimals (true √2 = 1.41421356...). -/
theorem cf_sqrt2_5_bracket :
    qlt (Q.of 14142 10000) (cf_sqrt2 5) = true
  ∧ qlt (cf_sqrt2 5) (Q.of 14143 10000) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- cf_sqrt2 10 squared lies in [1.999, 2.001] — quadratic accuracy. -/
theorem cf_sqrt2_squared_bracket :
    let s := cf_sqrt2 10
    qlt (Q.of 1999 1000) (Q.mul s s) = true
  ∧ qlt (Q.mul s s) (Q.of 2001 1000) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- The CReal corresponding to √2. -/
def cSqrt2 : CReal :=
  { approx  := cf_sqrt2
    modulus := fun k => k + 1 }

theorem cSqrt2_sample :
    qlt (Q.of 14142 10000) (cSqrt2.approx 6) = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- 9. MASTER DASHBOARD
-- ══════════════════════════════════════════════════════════

/-- Real-shadow dashboard:  e, π, √2, log 2 all sit in their
    expected rational brackets at the verified approximation depth. -/
theorem real_shadow_dashboard :
    qlt (Q.of 27182818 10000000) (e_approx 10)
  ∧ qlt (e_approx 10) (Q.of 271828183 100000000)
  ∧ qlt (Q.of 3140 1000) (pi_approx 100)
  ∧ qlt (pi_approx 100) (Q.of 3142 1000)
  ∧ qlt (Q.of 14142 10000) (cf_sqrt2 5)
  ∧ qlt (cf_sqrt2 5) (Q.of 14143 10000)
  ∧ qlt (Q.of 68 100) (log2_approx 200)
  ∧ qlt (log2_approx 200) (Q.of 70 100) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end RealShadow
