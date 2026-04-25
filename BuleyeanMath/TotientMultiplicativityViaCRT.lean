import Init

/-!
# Totient Multiplicativity via the Chinese Remainder Theorem

This module bridges three peer modules:

- `ChineseRemainderInstances` (CRT witnesses on small coprime pairs),
- `EulerTotientMobiusInversion` (brute-force `φ` and divisor sums),
- `FermatLittleInstances` (`powMod` and small-prime `a^(p-1) ≡ 1`).

The mathematical bridge is the ring isomorphism

    ℤ/(mn) ≃ ℤ/m × ℤ/n   (when `gcd(m, n) = 1`),

which restricts to a group isomorphism on units

    (ℤ/mn)^× ≃ (ℤ/m)^× × (ℤ/n)^×.

Cardinalities of the two sides coincide, giving multiplicativity of
Euler's totient on coprime arguments: `φ(mn) = φ(m) · φ(n)`. Fermat's
little theorem `a^(p-1) ≡ 1 (mod p)` then realizes the `n = p` case
of Euler's theorem `a^φ(n) ≡ 1 (mod n)` for `gcd(a, n) = 1`, since
`φ(p) = p - 1` for prime `p`.

This module does not formalize the abstract isomorphism. It witnesses
the bridge numerically at small inputs:

1. Totient multiplicativity at coprime pairs `(3,5), (4,7), (5,7)`
   and triple `(3,5,7)`, and the failure of the identity at the
   non-coprime pair `(4, 6)`.
2. Equality of the brute-force count `#{k ∈ [0, mn) : gcd(k, mn) = 1}`
   with the pair-count `#{(a,b) ∈ [0,m) × [0,n) : gcd(a,m) = 1 ∧
   gcd(b,n) = 1}` at `(3, 5)`.
3. Fermat `2^(p-1) mod p = 1` and Euler `2^φ(p) mod p = 1` agree
   pointwise at `p ∈ {3, 5, 7, 11, 13}` because `φ(p) = p - 1`.
4. Euler `a^φ(n) ≡ 1 (mod n)` at composite moduli `n ∈ {9, 15, 21}`
   where Fermat's small-prime statement does not directly apply.
5. CRT order bound: for coprime `(m, n)`, the order of `a` modulo `mn`
   divides `lcm(ord(a, m), ord(a, n))`. Witnessed at `a = 2`,
   `(m, n) = (3, 5)`.
6. The prime-power formula `φ(p^k) = p^(k-1) · (p - 1)` at small
   `(p, k)`.

All proofs close by kernel `decide`. `import Init` only; peer-module
definitions are inlined rather than imported. No `sorry`, no new
`axiom`.

Caveats. These are finite coincidences realized by the bridge, not a
general multiplicativity theorem. Fermat-from-Euler is witnessed
pointwise via the numerical equality `φ(p) = p - 1` on a list of
primes; no abstract group isomorphism is constructed. The order
bound from CRT is verified on one pair, not proved in general.
-/

namespace BuleyeanMath
namespace TotientMultiplicativityViaCRT

/-! ## Inlined primitives (peer-module shapes, kept local)

The peer modules define their own `gcdNat`, `phi`, and `powMod`. To
keep this file `Init`-only we inline compatible versions here.
-/

/-- Euclidean `gcd` with explicit fuel. -/
def gcdFuel : Nat → Nat → Nat → Nat
  | 0,           a, _ => a
  | Nat.succ _,  a, 0 => a
  | Nat.succ f,  a, Nat.succ b => gcdFuel f (Nat.succ b) (a % Nat.succ b)

/-- Euclidean `gcd` on `Nat`. -/
def gcdNat (a b : Nat) : Nat := gcdFuel (a + b + 1) a b

/-- Natural-number exponentiation `a ^ n`. -/
def natPow (a : Nat) : Nat → Nat
  | 0 => 1
  | Nat.succ k => a * natPow a k

/-- Modular exponentiation `(a ^ n) mod m`. Matches the peer-module
`powMod` in `FermatLittleInstances`. -/
def powMod (a : Nat) : Nat → Nat → Nat
  | 0,           m => 1 % m
  | Nat.succ k,  m => (a * powMod a k m) % m

/-- Count `k ∈ {1, ..., bound}` with `gcd(k, n) = 1`. -/
def phiAux : Nat → Nat → Nat
  | 0,          _ => 0
  | Nat.succ k, n =>
      let rest := phiAux k n
      if gcdNat (Nat.succ k) n = 1 then Nat.succ rest else rest

/-- Euler's totient `φ(n)` using the `{1, ..., n}` convention so
`φ(1) = 1`. Matches `EulerTotientMobiusInversion.phi`. -/
def phi : Nat → Nat
  | 0 => 0
  | Nat.succ m => phiAux (Nat.succ m) (Nat.succ m)

/-! ## Sanity checks on inlined `phi`

These re-witness values used below; they also cross-check the inline
definition against the peer module.
-/

theorem phi_1  : phi 1  = 1 := by decide
theorem phi_3  : phi 3  = 2 := by decide
theorem phi_4  : phi 4  = 2 := by decide
theorem phi_5  : phi 5  = 4 := by decide
theorem phi_6  : phi 6  = 2 := by decide
theorem phi_7  : phi 7  = 6 := by decide
theorem phi_8  : phi 8  = 4 := by decide
theorem phi_9  : phi 9  = 6 := by decide
theorem phi_11 : phi 11 = 10 := by decide
theorem phi_13 : phi 13 = 12 := by decide
theorem phi_15 : phi 15 = 8 := by decide
theorem phi_21 : phi 21 = 12 := by decide
theorem phi_24 : phi 24 = 8 := by decide
theorem phi_25 : phi 25 = 20 := by decide
theorem phi_27 : phi 27 = 18 := by decide
theorem phi_28 : phi 28 = 12 := by decide
theorem phi_35 : phi 35 = 24 := by decide
theorem phi_105 : phi 105 = 48 := by decide

/-! ## Item 1: Multiplicativity of `φ` on coprime pairs

`φ(m · n) = φ(m) · φ(n)` whenever `gcd(m, n) = 1`. Witnessed at
`(3,5), (4,7), (5,7)` and the triple `(3,5,7)`. For the non-coprime
pair `(4, 6)` (with `gcd(4, 6) = 2`) the identity fails, and we
witness the failure as a `Decidable` inequality.
-/

/-- Coprimality check at `(3, 5)`. -/
theorem gcd_3_5 : gcdNat 3 5 = 1 := by decide

/-- `φ(3 · 5) = φ(3) · φ(5)`: `8 = 2 · 4`. -/
theorem phi_mul_3_5 : phi (3 * 5) = phi 3 * phi 5 := by decide

/-- Coprimality check at `(4, 7)`. -/
theorem gcd_4_7 : gcdNat 4 7 = 1 := by decide

/-- `φ(4 · 7) = φ(4) · φ(7)`: `12 = 2 · 6`. -/
theorem phi_mul_4_7 : phi (4 * 7) = phi 4 * phi 7 := by decide

/-- Coprimality check at `(5, 7)`. -/
theorem gcd_5_7 : gcdNat 5 7 = 1 := by decide

/-- `φ(5 · 7) = φ(5) · φ(7)`: `24 = 4 · 6`. -/
theorem phi_mul_5_7 : phi (5 * 7) = phi 5 * phi 7 := by decide

/-- Triple `(3, 5, 7)`: pairwise coprime, and
`φ(3 · 5 · 7) = φ(3) · φ(5) · φ(7) = 2 · 4 · 6 = 48`. -/
theorem phi_mul_3_5_7 :
    phi (3 * 5 * 7) = phi 3 * phi 5 * phi 7 := by decide

/-- Counter-example: `gcd(4, 6) = 2 ≠ 1`, so multiplicativity fails. -/
theorem gcd_4_6_ne_one : gcdNat 4 6 ≠ 1 := by decide

/-- Failure of multiplicativity at the non-coprime pair `(4, 6)`:
`φ(24) = 8` but `φ(4) · φ(6) = 2 · 2 = 4`. -/
theorem phi_mul_4_6_fails : phi (4 * 6) ≠ phi 4 * phi 6 := by decide

/-- Explicit values of the counter-example. -/
theorem phi_24_explicit : phi (4 * 6) = 8 := by decide
theorem phi_4_times_phi_6 : phi 4 * phi 6 = 4 := by decide

/-! ## Item 2: CRT-compatible counting

For coprime `(m, n)`, the number of `k ∈ [0, mn)` with `gcd(k, mn) = 1`
equals the number of pairs `(a, b) ∈ [0, m) × [0, n)` with
`gcd(a, m) = 1` and `gcd(b, n) = 1`. The CRT isomorphism witnesses
the bijection; we witness the cardinality equality numerically.

We deliberately count over `[0, bound)` (rather than `[1, bound]`) to
match the CRT-index convention. When `bound > 1`, `0` is never
coprime to `bound` (since `gcd(0, bound) = bound`), so this agrees
with the standard `φ` value; for `bound = 1` the sole residue `0`
is coprime to `1`.
-/

/-- Count `k ∈ [0, bound)` with `gcd(k, n) = 1`. -/
def coprimeCountAux : Nat → Nat → Nat
  | 0,          _ => 0
  | Nat.succ k, n =>
      let rest := coprimeCountAux k n
      if gcdNat k n = 1 then Nat.succ rest else rest

/-- `#{k ∈ [0, n) : gcd(k, n) = 1}`. -/
def coprimeCount (n : Nat) : Nat := coprimeCountAux n n

/-- Double-loop pair count
`#{(a, b) ∈ [0, m) × [0, n) : gcd(a, m) = 1 ∧ gcd(b, n) = 1}`. -/
def coprimePairCountInner : Nat → Nat → Nat → Nat → Nat
  | 0,          _, _, _ => 0
  | Nat.succ j, a, m, n =>
      let rest := coprimePairCountInner j a m n
      if gcdNat a m = 1 ∧ gcdNat j n = 1 then Nat.succ rest else rest

def coprimePairCountOuter : Nat → Nat → Nat → Nat
  | 0,          _, _ => 0
  | Nat.succ i, m, n =>
      coprimePairCountInner n i m n + coprimePairCountOuter i m n

/-- `Σ_{a < m} Σ_{b < n} [gcd(a,m)=1 ∧ gcd(b,n)=1]`. -/
def coprimePairCount (m n : Nat) : Nat := coprimePairCountOuter m m n

/-- Sanity: at `(3, 5)`, the single-modulus count and pair count both
equal `8`. -/
theorem coprimeCount_15 : coprimeCount 15 = 8 := by decide

theorem coprimePairCount_3_5 : coprimePairCount 3 5 = 8 := by decide

/-- CRT cardinality bridge at `(3, 5)`: the two counts agree. -/
theorem crt_count_bridge_3_5 :
    coprimeCount (3 * 5) = coprimePairCount 3 5 := by decide

/-- Both sides also agree with the product `φ(3) · φ(5) = 8`. -/
theorem crt_count_matches_phi_product_3_5 :
    coprimeCount (3 * 5) = phi 3 * phi 5 := by decide

/-! ## Item 3: Fermat as a corollary of Euler, pointwise

For prime `p`, `φ(p) = p - 1`, so Euler's `a^φ(p) ≡ 1 (mod p)`
specializes to Fermat's `a^(p-1) ≡ 1 (mod p)`. We witness the
equality `φ(p) = p - 1` and the agreement of the two `powMod`
computations at `p ∈ {3, 5, 7, 11, 13}` with `a = 2`.
-/

/-- `φ(p) = p - 1` on small primes. -/
theorem phi_eq_pred_3  : phi 3  = 3  - 1 := by decide
theorem phi_eq_pred_5  : phi 5  = 5  - 1 := by decide
theorem phi_eq_pred_7  : phi 7  = 7  - 1 := by decide
theorem phi_eq_pred_11 : phi 11 = 11 - 1 := by decide
theorem phi_eq_pred_13 : phi 13 = 13 - 1 := by decide

/-- Fermat form `2^(p-1) mod p = 1`. -/
theorem fermat_2_3  : powMod 2 (3  - 1) 3  = 1 := by decide
theorem fermat_2_5  : powMod 2 (5  - 1) 5  = 1 := by decide
theorem fermat_2_7  : powMod 2 (7  - 1) 7  = 1 := by decide
theorem fermat_2_11 : powMod 2 (11 - 1) 11 = 1 := by decide
theorem fermat_2_13 : powMod 2 (13 - 1) 13 = 1 := by decide

/-- Euler form `2^φ(p) mod p = 1`. -/
theorem euler_2_3  : powMod 2 (phi 3)  3  = 1 := by decide
theorem euler_2_5  : powMod 2 (phi 5)  5  = 1 := by decide
theorem euler_2_7  : powMod 2 (phi 7)  7  = 1 := by decide
theorem euler_2_11 : powMod 2 (phi 11) 11 = 1 := by decide
theorem euler_2_13 : powMod 2 (phi 13) 13 = 1 := by decide

/-- Pointwise agreement `2^φ(p) mod p = 2^(p-1) mod p`. -/
theorem fermat_euler_agree_2_3 :
    powMod 2 (phi 3)  3  = powMod 2 (3  - 1) 3  := by decide
theorem fermat_euler_agree_2_5 :
    powMod 2 (phi 5)  5  = powMod 2 (5  - 1) 5  := by decide
theorem fermat_euler_agree_2_7 :
    powMod 2 (phi 7)  7  = powMod 2 (7  - 1) 7  := by decide
theorem fermat_euler_agree_2_11 :
    powMod 2 (phi 11) 11 = powMod 2 (11 - 1) 11 := by decide
theorem fermat_euler_agree_2_13 :
    powMod 2 (phi 13) 13 = powMod 2 (13 - 1) 13 := by decide

/-! ## Item 4: Euler at composite moduli

At composite `n`, Fermat's small-prime statement does not directly
apply, but Euler `a^φ(n) ≡ 1 (mod n)` holds whenever `gcd(a, n) = 1`.
Witnessed at `n ∈ {9, 15, 21}` with coprime bases.
-/

/-- Coprimality preconditions. -/
theorem gcd_2_9  : gcdNat 2 9  = 1 := by decide
theorem gcd_4_15 : gcdNat 4 15 = 1 := by decide
theorem gcd_2_15 : gcdNat 2 15 = 1 := by decide
theorem gcd_2_21 : gcdNat 2 21 = 1 := by decide

/-- `2^φ(9) mod 9 = 1`. -/
theorem euler_composite_2_9 : powMod 2 (phi 9) 9 = 1 := by decide

/-- `4^φ(15) mod 15 = 1`. -/
theorem euler_composite_4_15 : powMod 4 (phi 15) 15 = 1 := by decide

/-- `2^φ(15) mod 15 = 1`. -/
theorem euler_composite_2_15 : powMod 2 (phi 15) 15 = 1 := by decide

/-- `2^φ(21) mod 21 = 1`. -/
theorem euler_composite_2_21 : powMod 2 (phi 21) 21 = 1 := by decide

/-! ## Item 5: CRT order bound

The multiplicative order `ord(a, m)` is the least `k ≥ 1` with
`a^k ≡ 1 (mod m)`. For coprime `(m, n)` and `gcd(a, mn) = 1`, the
CRT isomorphism gives

    ord(a, mn)  divides  lcm(ord(a, m), ord(a, n)).

We witness this at `(m, n) = (3, 5)`, `a = 2`:
`ord(2, 3) = 2`, `ord(2, 5) = 4`, `lcm = 4`, and `2^4 mod 15 = 1`. -/

/-- Search upward from `k = 1` for the least `k ≤ bound` with
`a^k ≡ 1 (mod m)`. Returns `0` if no such `k` is found (cannot
happen when `gcd(a, m) = 1` and `bound ≥ m`). -/
def ordSearch : Nat → Nat → Nat → Nat → Nat → Nat
  | 0,          _, _, _, _ => 0
  | Nat.succ f, k, a, m, bound =>
      if k > bound then 0
      else if powMod a k m = 1 % m then k
      else ordSearch f (Nat.succ k) a m bound

/-- Multiplicative order of `a` modulo `m`. Search bound `m` is
always an upper bound when `gcd(a, m) = 1` (by Euler). -/
def ord (a m : Nat) : Nat := ordSearch (m + 1) 1 a m m

/-- Standard `Nat` lcm via the `gcd` identity `lcm a b = a * b / gcd a b`
(with `lcm a 0 = lcm 0 a = 0`). -/
def lcmNat (a b : Nat) : Nat :=
  if a = 0 ∨ b = 0 then 0 else a * b / gcdNat a b

/-- Divisibility predicate used below. -/
def divides (d n : Nat) : Bool :=
  if d = 0 then decide (n = 0) else decide (n % d = 0)

/-- Orders of `2` modulo `3` and `5`. -/
theorem ord_2_3 : ord 2 3 = 2 := by decide
theorem ord_2_5 : ord 2 5 = 4 := by decide

/-- `lcm(ord(2,3), ord(2,5)) = lcm(2, 4) = 4`. -/
theorem lcm_ord_2_3_5 : lcmNat (ord 2 3) (ord 2 5) = 4 := by decide

/-- `2 ^ lcm(ord(2,3), ord(2,5)) ≡ 1 (mod 15)`: the CRT-lifted exponent
works. -/
theorem crt_lifted_order_3_5_base_2 :
    powMod 2 (lcmNat (ord 2 3) (ord 2 5)) 15 = 1 := by decide

/-- Order of `2` modulo `15` is `4`. -/
theorem ord_2_15 : ord 2 15 = 4 := by decide

/-- Order divisibility: `ord(2, 15)` divides `lcm(ord(2,3), ord(2,5))`.
Here both are `4`. -/
theorem ord_divides_lcm_3_5_base_2 :
    divides (ord 2 15) (lcmNat (ord 2 3) (ord 2 5)) = true := by decide

/-! ## Item 6: Prime-power totient formula

`φ(p^k) = p^(k-1) · (p - 1)` on small `(p, k)`:
`φ(4) = 2, φ(8) = 4, φ(9) = 6, φ(25) = 20, φ(27) = 18`.
-/

/-- `φ(p^k)` with `(p, k) = (2, 2)`: `φ(4) = 2^1 · 1 = 2`. -/
theorem phi_pow_2_2 : phi (natPow 2 2) = natPow 2 (2 - 1) * (2 - 1) := by decide

/-- `φ(p^k)` with `(p, k) = (2, 3)`: `φ(8) = 2^2 · 1 = 4`. -/
theorem phi_pow_2_3 : phi (natPow 2 3) = natPow 2 (3 - 1) * (2 - 1) := by decide

/-- `φ(p^k)` with `(p, k) = (3, 2)`: `φ(9) = 3^1 · 2 = 6`. -/
theorem phi_pow_3_2 : phi (natPow 3 2) = natPow 3 (2 - 1) * (3 - 1) := by decide

/-- `φ(p^k)` with `(p, k) = (3, 3)`: `φ(27) = 3^2 · 2 = 18`. -/
theorem phi_pow_3_3 : phi (natPow 3 3) = natPow 3 (3 - 1) * (3 - 1) := by decide

/-- `φ(p^k)` with `(p, k) = (5, 2)`: `φ(25) = 5 · 4 = 20`. -/
theorem phi_pow_5_2 : phi (natPow 5 2) = natPow 5 (2 - 1) * (5 - 1) := by decide

end TotientMultiplicativityViaCRT
end BuleyeanMath
