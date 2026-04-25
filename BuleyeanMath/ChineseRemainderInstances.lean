import Init

/-!
# Chinese Remainder Theorem on Small Coprime Moduli

The Chinese Remainder Theorem (CRT): if `gcd(m, n) = 1`, then for any
residues `a` and `b` there exists a unique `x` in `[0, m * n)` with

    x ≡ a  (mod m)   and   x ≡ b  (mod n).

More generally, for pairwise coprime `m, n, k, ...`, residues combine
uniquely modulo the product.

This module witnesses concrete numerical instances for small coprime
pairs and one coprime triple. For each instance we

1. exhibit an explicit `x` and prove both (or all three) congruences
   by kernel `decide`;
2. witness uniqueness in the range `[0, m * n)` by exhaustive search:
   no other residue in the range satisfies both congruences;
3. verify that a brute-force solver `crtSolve` computes the same `x`.

The general theorem (a ring isomorphism `ℤ/(mn) ≃ ℤ/m × ℤ/n` when
`gcd(m, n) = 1`, proved via Bezout) is not formalised here. What we
provide is a finite table of computed coincidences that the general
theorem implies, together with a brute-force decision procedure that
computes a witness on each case.

All proofs close by kernel `decide` after a pure `Nat` or `Nat %`
computation. No `sorry`, no new `axiom`, `Init`-only.
-/

namespace BuleyeanMath
namespace ChineseRemainderInstances

/-! ## Brute-force CRT solver

We define `crtSolve m n a b` by naive search over `[0, m * n)`: return
the first `x` with `x % m = a` and `x % n = b`, or `0` as a safe
default if the range is exhausted (which does not happen when
`gcd(m, n) = 1` and `a < m`, `b < n`).

For the triple-modulus case we give a separate `crtSolve3`.
-/

/-- Search upward from `i` to the bound, returning the first `i` with
`i % m = a` and `i % n = b`. The `fuel` parameter drives termination;
passing `m * n` as the call-site fuel exhausts the range. -/
def crtSearch2 : Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | 0,           _, _, _, _, _ => 0
  | Nat.succ f,  i, m, n, a, b =>
      if i % m = a ∧ i % n = b then i
      else crtSearch2 f (Nat.succ i) m n a b

/-- Brute-force solver for two coprime moduli. Returns an `x` in
`[0, m * n)` with `x % m = a` and `x % n = b` whenever the residue
pair is realisable (which it is when `gcd(m, n) = 1`). -/
def crtSolve (m n a b : Nat) : Nat :=
  crtSearch2 (m * n) 0 m n a b

/-- Search upward from `i` for the first `x` with `x % m = a`,
`x % n = b`, and `x % k = c`. -/
def crtSearch3 : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | 0,           _, _, _, _, _, _, _ => 0
  | Nat.succ f,  i, m, n, k, a, b, c =>
      if i % m = a ∧ i % n = b ∧ i % k = c then i
      else crtSearch3 f (Nat.succ i) m n k a b c

/-- Brute-force solver for three pairwise coprime moduli. Returns an
`x` in `[0, m * n * k)` satisfying all three congruences. -/
def crtSolve3 (m n k a b c : Nat) : Nat :=
  crtSearch3 (m * n * k) 0 m n k a b c

/-! ## Uniqueness helper

`uniqueIn2 m n a b x bound` returns `true` iff the only `y < bound`
with `y % m = a` and `y % n = b` is `y = x`. Implemented by a
downward recursion over `bound`. -/

def uniqueIn2Aux : Nat → Nat → Nat → Nat → Nat → Nat → Bool
  | 0,           _, _, _, _, _ => true
  | Nat.succ k,  m, n, a, b, x =>
      let ok := if k = x then true
                else decide (k % m ≠ a ∨ k % n ≠ b)
      ok && uniqueIn2Aux k m n a b x

/-- `true` iff among `y ∈ [0, bound)`, the only witness of `(a, b)`
modulo `(m, n)` is `x`. -/
def uniqueIn2 (m n a b x bound : Nat) : Bool :=
  uniqueIn2Aux bound m n a b x

def uniqueIn3Aux : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool
  | 0,           _, _, _, _, _, _, _ => true
  | Nat.succ k,  m, n, p, a, b, c, x =>
      let ok := if k = x then true
                else decide (k % m ≠ a ∨ k % n ≠ b ∨ k % p ≠ c)
      ok && uniqueIn3Aux k m n p a b c x

/-- Uniqueness certificate for three moduli over `[0, bound)`. -/
def uniqueIn3 (m n p a b c x bound : Nat) : Bool :=
  uniqueIn3Aux bound m n p a b c x

/-! ## Sanity checks on the solver -/

/-- `crtSolve 3 5 2 3 = 8`. -/
theorem crtSolve_3_5_2_3 : crtSolve 3 5 2 3 = 8 := by decide

/-- `crtSolve 3 5 1 4 = 4`. -/
theorem crtSolve_3_5_1_4 : crtSolve 3 5 1 4 = 4 := by decide

/-- `crtSolve 4 7 3 2 = 23`. -/
theorem crtSolve_4_7_3_2 : crtSolve 4 7 3 2 = 23 := by decide

/-- `crtSolve 5 7 4 6 = 34`. -/
theorem crtSolve_5_7_4_6 : crtSolve 5 7 4 6 = 34 := by decide

/-- `crtSolve 5 11 3 8 = 8`. -/
theorem crtSolve_5_11_3_8 : crtSolve 5 11 3 8 = 8 := by decide

/-- `crtSolve3 3 5 7 2 3 2 = 23`. -/
theorem crtSolve3_3_5_7_2_3_2 : crtSolve3 3 5 7 2 3 2 = 23 := by decide

/-! ## Instance 1: `(m, n) = (3, 5)`, `(a, b) = (2, 3)`, `x = 8`

`8 % 3 = 2` and `8 % 5 = 3`. The product `3 * 5 = 15` and `8 < 15`.
-/

/-- Congruence `8 ≡ 2  (mod 3)`. -/
theorem crt_3_5_2_3_mod_m : (8 : Nat) % 3 = 2 := by decide

/-- Congruence `8 ≡ 3  (mod 5)`. -/
theorem crt_3_5_2_3_mod_n : (8 : Nat) % 5 = 3 := by decide

/-- Range witness: `8 < 15`. -/
theorem crt_3_5_2_3_in_range : (8 : Nat) < 3 * 5 := by decide

/-- Uniqueness: `8` is the only `y ∈ [0, 15)` with `y % 3 = 2` and
`y % 5 = 3`. -/
theorem crt_3_5_2_3_unique : uniqueIn2 3 5 2 3 8 15 = true := by decide

/-! ## Instance 2: `(m, n) = (3, 5)`, `(a, b) = (1, 4)`, `x = 4`

`4 % 3 = 1` and `4 % 5 = 4`, `4 < 15`.
-/

theorem crt_3_5_1_4_mod_m : (4 : Nat) % 3 = 1 := by decide
theorem crt_3_5_1_4_mod_n : (4 : Nat) % 5 = 4 := by decide
theorem crt_3_5_1_4_in_range : (4 : Nat) < 3 * 5 := by decide
theorem crt_3_5_1_4_unique : uniqueIn2 3 5 1 4 4 15 = true := by decide

/-! ## Instance 3: `(m, n) = (4, 7)`, `(a, b) = (3, 2)`, `x = 23`

`23 % 4 = 3` and `23 % 7 = 2`, `23 < 28`.
-/

theorem crt_4_7_3_2_mod_m : (23 : Nat) % 4 = 3 := by decide
theorem crt_4_7_3_2_mod_n : (23 : Nat) % 7 = 2 := by decide
theorem crt_4_7_3_2_in_range : (23 : Nat) < 4 * 7 := by decide
theorem crt_4_7_3_2_unique : uniqueIn2 4 7 3 2 23 28 = true := by decide

/-! ## Instance 4: `(m, n) = (5, 7)`, `(a, b) = (4, 6)`, `x = 34`

`34 % 5 = 4` and `34 % 7 = 6`, `34 < 35`.
-/

theorem crt_5_7_4_6_mod_m : (34 : Nat) % 5 = 4 := by decide
theorem crt_5_7_4_6_mod_n : (34 : Nat) % 7 = 6 := by decide
theorem crt_5_7_4_6_in_range : (34 : Nat) < 5 * 7 := by decide
theorem crt_5_7_4_6_unique : uniqueIn2 5 7 4 6 34 35 = true := by decide

/-! ## Instance 5: `(m, n) = (5, 11)`, `(a, b) = (3, 8)`, `x = 8`

`8 % 5 = 3` and `8 % 11 = 8`, `8 < 55`.
-/

theorem crt_5_11_3_8_mod_m : (8 : Nat) % 5 = 3 := by decide
theorem crt_5_11_3_8_mod_n : (8 : Nat) % 11 = 8 := by decide
theorem crt_5_11_3_8_in_range : (8 : Nat) < 5 * 11 := by decide
theorem crt_5_11_3_8_unique : uniqueIn2 5 11 3 8 8 55 = true := by decide

/-! ## Instance 6 (three moduli): `(m, n, k) = (3, 5, 7)`,
`(a, b, c) = (2, 3, 2)`, `x = 23`

`23 % 3 = 2`, `23 % 5 = 3`, `23 % 7 = 2`, `23 < 105`.
-/

theorem crt_3_5_7_2_3_2_mod_m : (23 : Nat) % 3 = 2 := by decide
theorem crt_3_5_7_2_3_2_mod_n : (23 : Nat) % 5 = 3 := by decide
theorem crt_3_5_7_2_3_2_mod_k : (23 : Nat) % 7 = 2 := by decide
theorem crt_3_5_7_2_3_2_in_range : (23 : Nat) < 3 * 5 * 7 := by decide

/-- Uniqueness: `23` is the only `y ∈ [0, 105)` with `y % 3 = 2`,
`y % 5 = 3`, and `y % 7 = 2`. -/
theorem crt_3_5_7_2_3_2_unique :
    uniqueIn3 3 5 7 2 3 2 23 105 = true := by decide

end ChineseRemainderInstances
end BuleyeanMath
