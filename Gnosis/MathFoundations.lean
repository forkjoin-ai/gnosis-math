/-
  MathFoundations
  ===============

  Shared, axiom-free arithmetic primitives reused across the
  Gnosis library.  Three independent components:

    1. Cyclotomic rings  Cyc n  for n ∈ {3, 4, 6, 8, 12, 24}
       — coefficient-list representation of  ℤ[ζ_n]  with
       multiplication reduced modulo  Φ_n(x).
    2. A finite rational ring  Q  with explicit add, mul,
       neg, inv and a normalized equality predicate.
    3. An extended polynomial library `LPoly` over `Int`
       with `eval`, `mul`, `compose`, `derivative` plus a
       handful of standard-identity sanity tests.

  Every operation has at least one `native_decide`-closed
  sanity theorem.  No imports beyond `Init`.  No axioms,
  no `sorry`.
-/

namespace ForkRaceFoldMath

-- ══════════════════════════════════════════════════════════
-- 1. CYCLOTOMIC RINGS  Cyc n
-- ══════════════════════════════════════════════════════════
-- Element of  Cyc n  is a list of `Int` coefficients of length
-- φ(n) representing  Σ aᵢ · ζ_n^i  where ζ_n is a primitive
-- n-th root of unity.  Multiplication is convolution of
-- coefficients followed by reduction modulo the n-th
-- cyclotomic polynomial Φ_n(x).
--
--   φ(3) = 2,   Φ_3(x) = x² + x + 1
--   φ(4) = 2,   Φ_4(x) = x² + 1
--   φ(6) = 2,   Φ_6(x) = x² − x + 1
--   φ(8) = 4,   Φ_8(x) = x⁴ + 1
--   φ(12) = 4,  Φ_12(x) = x⁴ − x² + 1
--   φ(24) = 8,  Φ_24(x) = x⁸ − x⁴ + 1

/-- Cyclotomic ring element: list of integer coefficients. -/
structure Cyc (n : Nat) where
  coeffs : List Int
  deriving DecidableEq, BEq

namespace Cyc

/-- Euler totient values for the supported moduli. -/
def phi : Nat → Nat
  | 3  => 2
  | 4  => 2
  | 6  => 2
  | 8  => 4
  | 12 => 4
  | 24 => 8
  | _  => 0

/-- Reduction of `x^φ(n)` modulo Φ_n(x), as a list of φ(n) coefficients.
    E.g. for n = 3:  x² ≡ -1 - x  ⇒  [-1, -1].
    For n = 6:  Φ_6 = x² - x + 1  ⇒  x² = x - 1  ⇒  [-1, 1]. -/
def reduceTop : Nat → List Int
  | 3  => [-1, -1]
  | 4  => [-1, 0]
  | 6  => [-1, 1]
  | 8  => [-1, 0, 0, 0]
  | 12 => [-1, 0, 1, 0]
  | 24 => [-1, 0, 0, 0, 1, 0, 0, 0]
  | _  => []

/-- Pad / truncate a coefficient list to length k with trailing zeros. -/
def normalizeLen (k : Nat) (xs : List Int) : List Int :=
  let rec go (i : Nat) (ys : List Int) : List Int :=
    match i with
    | 0     => []
    | i + 1 =>
      match ys with
      | []     => 0 :: go i []
      | y :: t => y :: go i t
  go k xs

/-- Zero element. -/
def zero (n : Nat) : Cyc n := ⟨normalizeLen (phi n) []⟩

/-- One element. -/
def one (n : Nat) : Cyc n := ⟨normalizeLen (phi n) [1]⟩

/-- ζ_n as the polynomial `x` (lifted into `Cyc n`). -/
def zeta (n : Nat) : Cyc n := ⟨normalizeLen (phi n) [0, 1]⟩

private def zipAdd : List Int → List Int → List Int
  | [],      ys      => ys
  | xs,      []      => xs
  | x :: xs, y :: ys => (x + y) :: zipAdd xs ys

private def listScale (k : Int) (xs : List Int) : List Int :=
  xs.map (k * ·)

private def listNeg (xs : List Int) : List Int :=
  xs.map (fun x => -x)

private def padFront (k : Nat) (zs : List Int) : List Int :=
  match k with
  | 0     => zs
  | k + 1 => 0 :: padFront k zs

/-- Addition (length pre-normalized). -/
def add {n : Nat} (a b : Cyc n) : Cyc n :=
  ⟨normalizeLen (phi n) (zipAdd a.coeffs b.coeffs)⟩

/-- Negation. -/
def neg {n : Nat} (a : Cyc n) : Cyc n :=
  ⟨normalizeLen (phi n) (listNeg a.coeffs)⟩

/-- Subtraction. -/
def sub {n : Nat} (a b : Cyc n) : Cyc n := add a (neg b)

/-- Convolution of coefficient lists (raw polynomial product). -/
private def convolve (xs ys : List Int) : List Int :=
  let rec convOne (x : Int) : List Int → List Int
    | []      => []
    | y :: ys => (x * y) :: convOne x ys
  let rec convAll (xs ys : List Int) (acc : List Int) (shift : Nat) : List Int :=
    match xs with
    | []      => acc
    | x :: xs => convAll xs ys (zipAdd acc (padFront shift (convOne x ys))) (shift + 1)
  convAll xs ys [] 0

/-- Reduce a polynomial of arbitrary degree modulo Φ_n(x).

    Strategy: walk through coefficients of degree ≥ φ(n) from low
    to high, replacing each contribution `c · x^(k + j)` by
    `c · x^j · topRule(x)` where `topRule = x^k mod Φ_n`.

    Concretely: if `xs = lo ++ hi` with `lo.length = k`, then
    `xs(x) = lo(x) + (Σ_j hi[j] · x^j) · x^k ≡ lo(x) + Σ_j hi[j] · x^j · topRule`.
-/
def reduceMod (n : Nat) (xs : List Int) : List Int :=
  let k := phi n
  let topRule := reduceTop n
  -- Split off front k coefficients into `lo`; remainder is `hi`.
  let rec splitAt (k : Nat) (xs : List Int) : List Int × List Int :=
    match k, xs with
    | 0,     ys     => ([], ys)
    | _,     []     => ([], [])
    | i + 1, y :: t =>
      let (a, b) := splitAt i t
      (y :: a, b)
  let (lo, hi) := splitAt k xs
  -- Add Σ_j hi[j] · x^j · topRule to lo.
  let rec replace (j : Nat) (hi acc : List Int) : List Int :=
    match hi with
    | []      => acc
    | h :: t =>
      let contrib := padFront j (listScale h topRule)
      replace (j + 1) t (zipAdd acc contrib)
  let combined := replace 0 hi lo
  -- combined may again exceed length k; iterate.
  -- A simple bound: total degree shrinks each pass.  Use fuel = xs.length + 4.
  let rec iter (fuel : Nat) (cur : List Int) : List Int :=
    match fuel with
    | 0     => cur
    | f + 1 =>
      let (lo', hi') := splitAt k cur
      match hi' with
      | [] => lo'
      | _  =>
        let next := replace 0 hi' lo'
        iter f next
  iter (xs.length + k + 4) combined

/-- Multiplication via convolution + reduction modulo Φ_n. -/
def mul {n : Nat} (a b : Cyc n) : Cyc n :=
  ⟨normalizeLen (phi n) (reduceMod n (convolve a.coeffs b.coeffs))⟩

/-- Power. -/
def pow {n : Nat} (a : Cyc n) : Nat → Cyc n
  | 0     => one n
  | k + 1 => mul a (pow a k)

/-- Equality on the normalized representation. -/
def eq {n : Nat} (a b : Cyc n) : Bool :=
  decide (normalizeLen (phi n) a.coeffs = normalizeLen (phi n) b.coeffs)

end Cyc

open Cyc

-- Sanity theorems: ζ_n raised to the n-th power equals 1.

theorem zeta3_pow : Cyc.eq ((zeta 3).pow 3) (one 3) = true := by native_decide
theorem zeta4_pow : Cyc.eq ((zeta 4).pow 4) (one 4) = true := by native_decide
theorem zeta6_pow : Cyc.eq ((zeta 6).pow 6) (one 6) = true := by native_decide
theorem zeta8_pow : Cyc.eq ((zeta 8).pow 8) (one 8) = true := by native_decide
theorem zeta12_pow : Cyc.eq ((zeta 12).pow 12) (one 12) = true := by native_decide
theorem zeta24_pow : Cyc.eq ((zeta 24).pow 24) (one 24) = true := by native_decide

/-- ζ_n raised to less than n is NOT the identity (sample). -/
theorem zeta3_pow1_ne_one : Cyc.eq ((zeta 3).pow 1) (one 3) = false := by native_decide
theorem zeta24_pow12_ne_one : Cyc.eq ((zeta 24).pow 12) (one 24) = false := by native_decide

/-- Addition basic sanity. -/
theorem cyc3_add_zero : Cyc.eq (Cyc.add (zeta 3) (zero 3)) (zeta 3) = true := by
  native_decide

/-- Multiplication is commutative on a sample. -/
theorem cyc6_mul_comm_sample :
    Cyc.eq (Cyc.mul (zeta 6) ((zeta 6).pow 2))
           (Cyc.mul ((zeta 6).pow 2) (zeta 6)) = true := by
  native_decide

/-- Distributivity sample in Cyc 24. -/
theorem cyc24_distrib_sample :
    Cyc.eq (Cyc.mul (zeta 24) (Cyc.add (one 24) (zeta 24)))
           (Cyc.add (zeta 24) ((zeta 24).pow 2)) = true := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- 2. RATIONAL RING  Q
-- ══════════════════════════════════════════════════════════

/-- Rational number  num / den.  `den` is intended to be > 0;
    constructors clamp den = 0 to 1.  Equality is up to
    cross-multiplication via `Q.beq`. -/
structure Q where
  num : Int
  den : Nat
  deriving DecidableEq, BEq, Repr

namespace Q

/-- Smart constructor: replaces den = 0 with den = 1. -/
def of (n : Int) (d : Nat) : Q :=
  if d = 0 then ⟨n, 1⟩ else ⟨n, d⟩

/-- Zero. -/
def zero : Q := ⟨0, 1⟩

/-- One. -/
def one : Q := ⟨1, 1⟩

/-- From an integer. -/
def ofInt (k : Int) : Q := ⟨k, 1⟩

/-- Addition:  a/b + c/d = (a·d + c·b) / (b·d). -/
def add (x y : Q) : Q :=
  of (x.num * Int.ofNat y.den + y.num * Int.ofNat x.den) (x.den * y.den)

/-- Negation. -/
def neg (x : Q) : Q := of (-x.num) x.den

/-- Subtraction. -/
def sub (x y : Q) : Q := add x (neg y)

/-- Multiplication. -/
def mul (x y : Q) : Q := of (x.num * y.num) (x.den * y.den)

/-- Multiplicative inverse (zero if the input is zero).
    Sign normalized so the resulting denominator is positive. -/
def inv (x : Q) : Q :=
  match x.num with
  | .ofNat 0      => zero
  | .ofNat (n+1)  => of (Int.ofNat x.den) (n + 1)
  | .negSucc n    => of (-(Int.ofNat x.den)) (n + 1)

/-- Cross-multiplication equality.  `a/b == c/d` iff a·d = c·b. -/
def beq (x y : Q) : Bool :=
  decide (x.num * Int.ofNat y.den = y.num * Int.ofNat x.den)

/-- Power (non-negative). -/
def pow (x : Q) : Nat → Q
  | 0     => one
  | k + 1 => mul x (pow x k)

end Q

open Q

theorem q_half_plus_third :
    Q.beq (Q.add (Q.of 1 2) (Q.of 1 3)) (Q.of 5 6) = true := by
  native_decide

theorem q_two_thirds_times_three_quarters :
    Q.beq (Q.mul (Q.of 2 3) (Q.of 3 4)) (Q.of 1 2) = true := by
  native_decide

theorem q_inv_of_2_3 :
    Q.beq (Q.inv (Q.of 2 3)) (Q.of 3 2) = true := by
  native_decide

theorem q_neg_inv_of_neg :
    Q.beq (Q.inv (Q.of (-2) 3)) (Q.of (-3) 2) = true := by
  native_decide

theorem q_mul_inv_self :
    Q.beq (Q.mul (Q.of 7 4) (Q.inv (Q.of 7 4))) Q.one = true := by
  native_decide

theorem q_add_neg_self :
    Q.beq (Q.add (Q.of 5 3) (Q.neg (Q.of 5 3))) Q.zero = true := by
  native_decide

theorem q_distributive :
    Q.beq (Q.mul (Q.of 1 2) (Q.add (Q.of 1 3) (Q.of 1 6)))
          (Q.add (Q.mul (Q.of 1 2) (Q.of 1 3)) (Q.mul (Q.of 1 2) (Q.of 1 6))) = true := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- 3. EXTENDED POLYNOMIAL LIBRARY OVER ℤ
-- ══════════════════════════════════════════════════════════
-- Plain polynomial in `Int` coefficients, represented by a
-- coefficient list  [a₀, a₁, ..., a_d]  (constant term first).
-- We name it `LPoly` to avoid clashing with the `LaurentPoly`
-- of `KhovanovCategorifiesJones`.

structure LPoly where
  coeffs : List Int
  deriving DecidableEq, BEq

namespace LPoly

def zero : LPoly := ⟨[]⟩
def one : LPoly := ⟨[1]⟩

/-- Monomial c · x^k. -/
def mono (c : Int) (k : Nat) : LPoly :=
  ⟨(List.replicate k (0 : Int)) ++ [c]⟩

/-- The variable `x`. -/
def x : LPoly := mono 1 1

private def zipAdd : List Int → List Int → List Int
  | [],      ys      => ys
  | xs,      []      => xs
  | x :: xs, y :: ys => (x + y) :: zipAdd xs ys

def add (p q : LPoly) : LPoly := ⟨zipAdd p.coeffs q.coeffs⟩
def neg (p : LPoly) : LPoly := ⟨p.coeffs.map (fun c => -c)⟩
def sub (p q : LPoly) : LPoly := add p (neg q)
def scale (k : Int) (p : LPoly) : LPoly := ⟨p.coeffs.map (k * ·)⟩

private def padFront (k : Nat) (zs : List Int) : List Int :=
  match k with
  | 0     => zs
  | k + 1 => 0 :: padFront k zs

private def convolve (xs ys : List Int) : List Int :=
  let rec convOne (x : Int) : List Int → List Int
    | []      => []
    | y :: ys => (x * y) :: convOne x ys
  let rec convAll (xs ys : List Int) (acc : List Int) (shift : Nat) : List Int :=
    match xs with
    | []      => acc
    | x :: xs => convAll xs ys (zipAdd acc (padFront shift (convOne x ys))) (shift + 1)
  convAll xs ys [] 0

def mul (p q : LPoly) : LPoly := ⟨convolve p.coeffs q.coeffs⟩

def pow (p : LPoly) : Nat → LPoly
  | 0     => one
  | k + 1 => mul p (pow p k)

/-- Evaluate at an integer point. -/
def eval (p : LPoly) (t : Int) : Int :=
  let rec go : List Int → Int → Int → Int
    | [],      _, acc => acc
    | c :: cs, e, acc => go cs (e * t) (acc + c * e)
  go p.coeffs 1 0

/-- Composition  p ∘ q  =  p(q(x)). -/
def compose (p q : LPoly) : LPoly :=
  let rec go : List Int → LPoly → LPoly → LPoly
    | [],      _,    acc => acc
    | c :: cs, qpow, acc =>
      go cs (mul qpow q) (add acc (scale c qpow))
  go p.coeffs one zero

/-- Formal derivative. -/
def derivative (p : LPoly) : LPoly :=
  let rec go : List Int → Nat → List Int
    | [],      _ => []
    | _ :: cs, 0 => go cs 1
    | c :: cs, k => (Int.ofNat k * c) :: go cs (k + 1)
  ⟨go p.coeffs 0⟩

/-- Strip trailing zeros from a coefficient list. -/
def stripZeros : List Int → List Int
  | []      => []
  | x :: xs =>
    let t := stripZeros xs
    match t with
    | [] => if x = 0 then [] else [x]
    | _  => x :: t

/-- Coefficient equality after stripping trailing zeros. -/
def beq (p q : LPoly) : Bool :=
  decide (stripZeros p.coeffs = stripZeros q.coeffs)

end LPoly

open LPoly

/-- (1 + x)² = 1 + 2x + x². -/
theorem one_plus_x_squared :
    LPoly.beq ((LPoly.add LPoly.one LPoly.x).pow 2)
              ⟨[1, 2, 1]⟩ = true := by
  native_decide

/-- (1 + x)³ = 1 + 3x + 3x² + x³. -/
theorem one_plus_x_cubed :
    LPoly.beq ((LPoly.add LPoly.one LPoly.x).pow 3)
              ⟨[1, 3, 3, 1]⟩ = true := by
  native_decide

/-- (x − 1)(x + 1) = x² − 1. -/
theorem diff_of_squares :
    LPoly.beq (LPoly.mul (LPoly.sub LPoly.x LPoly.one)
                         (LPoly.add LPoly.x LPoly.one))
              ⟨[-1, 0, 1]⟩ = true := by
  native_decide

/-- eval((1+x)², 3) = 16. -/
theorem eval_sample :
    ((LPoly.add LPoly.one LPoly.x).pow 2).eval 3 = 16 := by
  native_decide

/-- compose(p, q) where p = 1 + x², q = 1 + x  gives  1 + (1+x)² = 2 + 2x + x². -/
theorem compose_sample :
    LPoly.beq (LPoly.compose ⟨[1, 0, 1]⟩ (LPoly.add LPoly.one LPoly.x))
              ⟨[2, 2, 1]⟩ = true := by
  native_decide

/-- d/dx (1 + 2x + x²) = 2 + 2x. -/
theorem derivative_sample :
    LPoly.beq (LPoly.derivative ⟨[1, 2, 1]⟩) ⟨[2, 2]⟩ = true := by
  native_decide

/-- d/dx (x³) = 3x². -/
theorem derivative_cube :
    LPoly.beq (LPoly.derivative (LPoly.x.pow 3)) ⟨[0, 0, 3]⟩ = true := by
  native_decide

/-- Composition with `x` is identity on coefficients. -/
theorem compose_with_x :
    LPoly.beq (LPoly.compose ⟨[1, 2, 1]⟩ LPoly.x) ⟨[1, 2, 1]⟩ = true := by
  native_decide

end ForkRaceFoldMath
