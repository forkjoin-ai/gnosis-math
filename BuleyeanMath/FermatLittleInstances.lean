import Init

/-!
# Fermat's Little Theorem on Small Prime Instances

Fermat's little theorem states that for a prime `p` and any natural
number `a`,

    a ^ p ≡ a  (mod p).

Equivalently, when `gcd(a, p) = 1`,

    a ^ (p - 1) ≡ 1  (mod p).

This module witnesses concrete numerical instances for small primes
`p ∈ {3, 5, 7, 11, 13}` and small bases `a`. The general theorem
(over all primes and bases, proved by Lagrange's theorem on the
multiplicative group `(ℤ/pℤ)^×` or by induction via the binomial
expansion) is not proved here. What we provide is a finite list of
computed coincidences that the general theorem implies.

We also include two related numerical witnesses:

- **Wilson's theorem** instances `(p - 1)! ≡ -1  (mod p)`, rendered
  as `((p - 1)! + 1) % p = 0` to stay inside `Nat`.
- **Euler's totient** variant `a ^ φ(n) ≡ 1  (mod n)` for small
  coprime pairs `(a, n)`, using a brute-force `phi` that counts
  integers in `[1, n)` coprime to `n`.

All proofs close by kernel `decide` after a pure `Nat` or `Nat %`
computation. No `sorry`, no new `axiom`, `Init`-only.
-/

namespace BuleyeanMath
namespace FermatLittleInstances

/-! ## Natural-number exponentiation -/

/-- Natural-number power `a ^ n`, defined by recursion on `n`. -/
def natPow (a : Nat) : Nat → Nat
  | 0 => 1
  | Nat.succ k => a * natPow a k

/-- Modular exponentiation `(a ^ n) mod m`, computed by reducing at
every multiplication to keep intermediate values small. -/
def powMod (a : Nat) : Nat → Nat → Nat
  | 0, m => 1 % m
  | Nat.succ k, m => (a * powMod a k m) % m

/-! ## Sanity checks on the power function -/

/-- `2 ^ 10 = 1024`. -/
theorem natPow_2_10 : natPow 2 10 = 1024 := by decide

/-- `3 ^ 5 = 243`. -/
theorem natPow_3_5 : natPow 3 5 = 243 := by decide

/-- `powMod` and `natPow` agree mod `m` on a witnessed small case. -/
theorem powMod_matches_natPow_2_7_5 :
    powMod 2 7 5 = natPow 2 7 % 5 := by decide

/-- `powMod` and `natPow` agree mod `m` on a second small case. -/
theorem powMod_matches_natPow_3_6_7 :
    powMod 3 6 7 = natPow 3 6 % 7 := by decide

/-! ## Fermat's little theorem, full form `a ^ p ≡ a (mod p)`

For each small prime `p` and base `a`, `powMod a p p = a % p`.
-/

/-! ### `p = 3`: bases `0, 1, 2, 3, 4, 5` -/

theorem fermat_3_0 : powMod 0 3 3 = 0 % 3 := by decide
theorem fermat_3_1 : powMod 1 3 3 = 1 % 3 := by decide
theorem fermat_3_2 : powMod 2 3 3 = 2 % 3 := by decide
theorem fermat_3_3 : powMod 3 3 3 = 3 % 3 := by decide
theorem fermat_3_4 : powMod 4 3 3 = 4 % 3 := by decide
theorem fermat_3_5 : powMod 5 3 3 = 5 % 3 := by decide

/-! ### `p = 5`: bases `0..7` -/

theorem fermat_5_0 : powMod 0 5 5 = 0 % 5 := by decide
theorem fermat_5_1 : powMod 1 5 5 = 1 % 5 := by decide
theorem fermat_5_2 : powMod 2 5 5 = 2 % 5 := by decide
theorem fermat_5_3 : powMod 3 5 5 = 3 % 5 := by decide
theorem fermat_5_4 : powMod 4 5 5 = 4 % 5 := by decide
theorem fermat_5_5 : powMod 5 5 5 = 5 % 5 := by decide
theorem fermat_5_6 : powMod 6 5 5 = 6 % 5 := by decide
theorem fermat_5_7 : powMod 7 5 5 = 7 % 5 := by decide

/-! ### `p = 7`: bases `0..8` -/

theorem fermat_7_0 : powMod 0 7 7 = 0 % 7 := by decide
theorem fermat_7_1 : powMod 1 7 7 = 1 % 7 := by decide
theorem fermat_7_2 : powMod 2 7 7 = 2 % 7 := by decide
theorem fermat_7_3 : powMod 3 7 7 = 3 % 7 := by decide
theorem fermat_7_4 : powMod 4 7 7 = 4 % 7 := by decide
theorem fermat_7_5 : powMod 5 7 7 = 5 % 7 := by decide
theorem fermat_7_6 : powMod 6 7 7 = 6 % 7 := by decide
theorem fermat_7_7 : powMod 7 7 7 = 7 % 7 := by decide
theorem fermat_7_8 : powMod 8 7 7 = 8 % 7 := by decide

/-! ### `p = 11`: bases `0..5` -/

theorem fermat_11_0 : powMod 0 11 11 = 0 % 11 := by decide
theorem fermat_11_1 : powMod 1 11 11 = 1 % 11 := by decide
theorem fermat_11_2 : powMod 2 11 11 = 2 % 11 := by decide
theorem fermat_11_3 : powMod 3 11 11 = 3 % 11 := by decide
theorem fermat_11_4 : powMod 4 11 11 = 4 % 11 := by decide
theorem fermat_11_5 : powMod 5 11 11 = 5 % 11 := by decide

/-! ### `p = 13`: two instances -/

theorem fermat_13_2 : powMod 2 13 13 = 2 % 13 := by decide
theorem fermat_13_3 : powMod 3 13 13 = 3 % 13 := by decide

/-! ## Coprime form `a ^ (p - 1) ≡ 1 (mod p)`

For `gcd(a, p) = 1` (automatic when `p` is prime and `a` is not a
multiple of `p`), `a ^ (p - 1) ≡ 1 (mod p)`.
-/

/-! ### Base `a = 2`: primes `3, 5, 7, 11, 13` -/

theorem fermat_coprime_2_3  : powMod 2  (3  - 1) 3  = 1 := by decide
theorem fermat_coprime_2_5  : powMod 2  (5  - 1) 5  = 1 := by decide
theorem fermat_coprime_2_7  : powMod 2  (7  - 1) 7  = 1 := by decide
theorem fermat_coprime_2_11 : powMod 2  (11 - 1) 11 = 1 := by decide
theorem fermat_coprime_2_13 : powMod 2  (13 - 1) 13 = 1 := by decide

/-! ### Base `a = 3`: primes `5, 7, 11, 13` -/

theorem fermat_coprime_3_5  : powMod 3  (5  - 1) 5  = 1 := by decide
theorem fermat_coprime_3_7  : powMod 3  (7  - 1) 7  = 1 := by decide
theorem fermat_coprime_3_11 : powMod 3  (11 - 1) 11 = 1 := by decide
theorem fermat_coprime_3_13 : powMod 3  (13 - 1) 13 = 1 := by decide

/-! ## Wilson's theorem instances

Wilson: for prime `p`, `(p - 1)! ≡ -1  (mod p)`, equivalently
`((p - 1)! + 1) % p = 0`. We encode `-1` this way to stay inside
`Nat`. These are numerical witnesses, not a proof of Wilson's
general theorem.
-/

/-- Factorial on `Nat`. -/
def factorial : Nat → Nat
  | 0 => 1
  | Nat.succ k => (Nat.succ k) * factorial k

/-- Sanity: `5! = 120`. -/
theorem factorial_5 : factorial 5 = 120 := by decide

/-- Sanity: `10! = 3628800`. -/
theorem factorial_10 : factorial 10 = 3628800 := by decide

/-- Wilson at `p = 3`: `2! + 1 = 3`, divisible by 3. -/
theorem wilson_3 : (factorial (3 - 1) + 1) % 3 = 0 := by decide

/-- Wilson at `p = 5`: `4! + 1 = 25`, divisible by 5. -/
theorem wilson_5 : (factorial (5 - 1) + 1) % 5 = 0 := by decide

/-- Wilson at `p = 7`: `6! + 1 = 721`, divisible by 7. -/
theorem wilson_7 : (factorial (7 - 1) + 1) % 7 = 0 := by decide

/-- Wilson at `p = 11`: `10! + 1 = 3628801`, divisible by 11. -/
theorem wilson_11 : (factorial (11 - 1) + 1) % 11 = 0 := by decide

/-! ## Euler's totient instances

Euler: for `gcd(a, n) = 1`, `a ^ φ(n) ≡ 1  (mod n)`. We compute
`φ(n)` by brute enumeration of `{k ∈ [1, n) : gcd(k, n) = 1}` and
witness a few small coprime cases. These are numerical witnesses.
-/

/-- Euclidean `gcd` on `Nat` with an explicit fuel parameter to keep
termination and kernel reduction straightforward. The fuel is taken
as `a + b` at the call site, which is always an upper bound on the
number of Euclidean steps required. -/
def gcdFuel : Nat → Nat → Nat → Nat
  | 0,           a, _ => a
  | Nat.succ _,  a, 0 => a
  | Nat.succ f,  a, Nat.succ b => gcdFuel f (Nat.succ b) (a % Nat.succ b)

/-- Euclidean `gcd` on `Nat`. -/
def gcdNat (a b : Nat) : Nat := gcdFuel (a + b + 1) a b

/-- Count `k ∈ [1, n)` with `gcd(k, n) = 1`, iterated downward. -/
def phiAux : Nat → Nat → Nat
  | 0, _ => 0
  | Nat.succ k, n =>
      let rest := phiAux k n
      if gcdNat (Nat.succ k) n = 1 then Nat.succ rest else rest

/-- Euler's totient `φ(n)`. For `n = 0` we return `0`; for `n ≥ 1`
this counts the integers in `[1, n)` coprime to `n` (which, for
`n = 1`, gives `0`; the usual convention `φ(1) = 1` is not needed
for our instances since we keep `n ≥ 3`). -/
def phi : Nat → Nat
  | 0 => 0
  | Nat.succ m => phiAux m (Nat.succ m)

/-- Sanity: `φ(5) = 4`. -/
theorem phi_5 : phi 5 = 4 := by decide

/-- Sanity: `φ(9) = 6`. -/
theorem phi_9 : phi 9 = 6 := by decide

/-- Sanity: `φ(15) = 8`. -/
theorem phi_15 : phi 15 = 8 := by decide

/-- Euler for `(a, n) = (2, 9)`: `gcd = 1`, `φ(9) = 6`,
`2 ^ 6 = 64 ≡ 1  (mod 9)`. -/
theorem euler_2_9 : powMod 2 (phi 9) 9 = 1 := by decide

/-- Euler for `(a, n) = (4, 9)`: `gcd = 1`, `4 ^ 6 = 4096 ≡ 1  (mod 9)`. -/
theorem euler_4_9 : powMod 4 (phi 9) 9 = 1 := by decide

/-- Euler for `(a, n) = (2, 15)`: `gcd = 1`, `φ(15) = 8`,
`2 ^ 8 = 256 ≡ 1  (mod 15)`. -/
theorem euler_2_15 : powMod 2 (phi 15) 15 = 1 := by decide

/-- Euler for `(a, n) = (7, 15)`: `gcd = 1`, `7 ^ 8 ≡ 1  (mod 15)`. -/
theorem euler_7_15 : powMod 7 (phi 15) 15 = 1 := by decide

end FermatLittleInstances
end BuleyeanMath
