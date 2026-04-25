import Init

/-!
# Euler's Totient `φ(n)` and Möbius Function `μ(n)`

This module witnesses three classical number-theoretic identities at
concrete small inputs:

1. **Euler's totient `φ(n)`**, defined by brute enumeration as
   `#{k ∈ {1, ..., n} : gcd(k, n) = 1}` (so `φ(1) = 1`).
2. **Divisor-sum identity**
   `Σ_{d ∣ n} φ(d) = n`, verified for
   `n ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 20}`.
3. **Möbius function `μ : ℕ → ℤ`**, defined via trial-division
   factorization: `μ(1) = 1`; `μ(n) = 0` if any prime factor appears
   with multiplicity ≥ 2; otherwise `μ(n) = (-1)^k` where `k` is the
   number of distinct prime factors.
4. **Möbius inversion** on the pair `f(n) = n`, `g(n) = φ(n)`:
   `φ(n) = Σ_{d ∣ n} μ(n/d) · d`, witnessed at
   `n ∈ {6, 10, 12, 15, 30}`.
5. **Dirichlet convolution `μ * 1 = δ`**:
   `Σ_{d ∣ n} μ(d) = [n = 1]`, witnessed at
   `n ∈ {1, 2, 6, 12, 30}`.

All `Nat`-side arithmetic uses fuel-parameter recursion so the kernel
can `decide` each instance. No `sorry`, no new `axiom`, `Init`-only.

Caveats. These are finite coincidences, not general theorems. We do
not prove `φ` is multiplicative, do not develop Dirichlet series, and
do not prove the divisor-sum identity or Möbius inversion for all
`n`. The factorization is brute trial division up to `n`.
-/

namespace Gnosis
namespace EulerTotientMobiusInversion

/-! ## Euclidean gcd on `Nat` -/

/-- Euclidean `gcd` with explicit fuel to keep termination obvious
and kernel reduction direct. -/
def gcdFuel : Nat → Nat → Nat → Nat
  | 0,           a, _ => a
  | Nat.succ _,  a, 0 => a
  | Nat.succ f,  a, Nat.succ b => gcdFuel f (Nat.succ b) (a % Nat.succ b)

/-- Euclidean `gcd` on `Nat`. -/
def gcdNat (a b : Nat) : Nat := gcdFuel (a + b + 1) a b

/-! ## Euler's totient `φ(n)` by brute enumeration -/

/-- Count `k ∈ {1, ..., bound}` with `gcd(k, n) = 1`. -/
def phiAux : Nat → Nat → Nat
  | 0,          _ => 0
  | Nat.succ k, n =>
      let rest := phiAux k n
      if gcdNat (Nat.succ k) n = 1 then Nat.succ rest else rest

/-- Euler's totient `φ(n)`. We use the `{1, ..., n}` convention so
that `φ(1) = 1` (since `gcd(1, 1) = 1`). For `n = 0` we return `0`. -/
def phi : Nat → Nat
  | 0 => 0
  | Nat.succ m => phiAux (Nat.succ m) (Nat.succ m)

/-! ### Totient values at small `n` -/

theorem phi_1  : phi 1  = 1 := by decide
theorem phi_2  : phi 2  = 1 := by decide
theorem phi_3  : phi 3  = 2 := by decide
theorem phi_4  : phi 4  = 2 := by decide
theorem phi_5  : phi 5  = 4 := by decide
theorem phi_6  : phi 6  = 2 := by decide
theorem phi_7  : phi 7  = 6 := by decide
theorem phi_8  : phi 8  = 4 := by decide
theorem phi_9  : phi 9  = 6 := by decide
theorem phi_10 : phi 10 = 4 := by decide
theorem phi_12 : phi 12 = 4 := by decide
theorem phi_15 : phi 15 = 8 := by decide
theorem phi_16 : phi 16 = 8 := by decide
theorem phi_20 : phi 20 = 8 := by decide

/-! ## Divisors and the divisor-sum identity `Σ_{d ∣ n} φ(d) = n` -/

/-- Collect `d ∈ {1, ..., bound}` with `n % d = 0`, iterating down. -/
def divisorsAux : Nat → Nat → List Nat
  | 0,          _ => []
  | Nat.succ k, n =>
      let rest := divisorsAux k n
      if n % (Nat.succ k) = 0 then (Nat.succ k) :: rest else rest

/-- Divisors of `n` in `{1, ..., n}`. For `n = 0` we return `[]`. -/
def divisors : Nat → List Nat
  | 0 => []
  | Nat.succ m => divisorsAux (Nat.succ m) (Nat.succ m)

/-- Sum `phi d` over a list of divisors. -/
def sumPhiList : List Nat → Nat
  | []      => 0
  | d :: ds => phi d + sumPhiList ds

/-- `Σ_{d ∣ n} φ(d)`. -/
def sumPhi (n : Nat) : Nat := sumPhiList (divisors n)

/-! ### Divisor-sum identity at small `n` -/

theorem sumPhi_1  : sumPhi 1  = 1  := by decide
theorem sumPhi_2  : sumPhi 2  = 2  := by decide
theorem sumPhi_3  : sumPhi 3  = 3  := by decide
theorem sumPhi_4  : sumPhi 4  = 4  := by decide
theorem sumPhi_5  : sumPhi 5  = 5  := by decide
theorem sumPhi_6  : sumPhi 6  = 6  := by decide
theorem sumPhi_7  : sumPhi 7  = 7  := by decide
theorem sumPhi_8  : sumPhi 8  = 8  := by decide
theorem sumPhi_9  : sumPhi 9  = 9  := by decide
theorem sumPhi_10 : sumPhi 10 = 10 := by decide
theorem sumPhi_12 : sumPhi 12 = 12 := by decide
theorem sumPhi_15 : sumPhi 15 = 15 := by decide
theorem sumPhi_20 : sumPhi 20 = 20 := by decide

/-! ## Möbius function `μ : ℕ → ℤ` via trial-division factorization -/

/-- Strip as many factors of `p` from `n` as possible, returning the
multiplicity and the residual. Fuel bounds the loop. -/
def stripFactor : Nat → Nat → Nat → Nat × Nat
  | 0,          _, n => (0, n)
  | Nat.succ f, p, n =>
      if p ≥ 2 ∧ n % p = 0 then
        let (m, r) := stripFactor f p (n / p)
        (Nat.succ m, r)
      else
        (0, n)

/-- Trial-divide `n` by candidate primes `2, 3, ..., bound`, building
a list of `(prime, multiplicity)` pairs for those that actually
divide. Any final residual `> 1` is appended as a single factor of
multiplicity `1`. Fuel `f` caps the outer loop; we pass `bound + 1`. -/
def factorAux : Nat → Nat → Nat → List (Nat × Nat)
  | 0,          _, n => if n > 1 then [(n, 1)] else []
  | Nat.succ f, p, n =>
      if n ≤ 1 then []
      else if p < 2 then factorAux f (Nat.succ p) n
      else if p * p > n then
        if n > 1 then [(n, 1)] else []
      else
        let (m, r) := stripFactor (n + 1) p n
        if m = 0 then
          factorAux f (Nat.succ p) n
        else
          (p, m) :: factorAux f (Nat.succ p) r

/-- Prime factorization with multiplicity. The outer fuel is `n + 1`
so the trial-division loop always has enough steps. -/
def primeFactorsWithMultiplicity (n : Nat) : List (Nat × Nat) :=
  factorAux (n + 1) 2 n

/-- Check whether every multiplicity in a factor list equals `1`. -/
def allMultOne : List (Nat × Nat) → Bool
  | []             => true
  | (_, m) :: rest => decide (m = 1) && allMultOne rest

/-- Möbius function on `Nat`, returning `Int`.
- `μ(0) := 0` as a convention (not mathematically meaningful).
- `μ(1) = 1` (empty factor list).
- If any prime factor has multiplicity `> 1`, return `0`.
- Otherwise return `(-1)^(# distinct primes)`. -/
def mobius : Nat → Int
  | 0 => 0
  | Nat.succ m =>
      let facs := primeFactorsWithMultiplicity (Nat.succ m)
      if allMultOne facs then
        if facs.length % 2 = 0 then (1 : Int) else (-1 : Int)
      else
        (0 : Int)

/-! ### Möbius values at small `n` -/

theorem mobius_1  : mobius 1  = 1  := by decide
theorem mobius_2  : mobius 2  = -1 := by decide
theorem mobius_3  : mobius 3  = -1 := by decide
theorem mobius_4  : mobius 4  = 0  := by decide
theorem mobius_5  : mobius 5  = -1 := by decide
theorem mobius_6  : mobius 6  = 1  := by decide
theorem mobius_7  : mobius 7  = -1 := by decide
theorem mobius_8  : mobius 8  = 0  := by decide
theorem mobius_9  : mobius 9  = 0  := by decide
theorem mobius_10 : mobius 10 = 1  := by decide
theorem mobius_12 : mobius 12 = 0  := by decide
theorem mobius_15 : mobius 15 = 1  := by decide
theorem mobius_30 : mobius 30 = -1 := by decide

/-! ## Möbius inversion on `f(n) = n`, `g(n) = φ(n)`

Since `Σ_{d ∣ n} φ(d) = n`, Möbius inversion gives
`φ(n) = Σ_{d ∣ n} μ(n/d) · d`. We witness this at
`n ∈ {6, 10, 12, 15, 30}`. -/

/-- Inner sum `Σ_{d ∈ ds} μ(n/d) · d` (as `Int`). -/
def mobiusInvSumList (n : Nat) : List Nat → Int
  | []      => 0
  | d :: ds => mobius (n / d) * (d : Int) + mobiusInvSumList n ds

/-- `Σ_{d ∣ n} μ(n/d) · d`. -/
def mobiusInvSum (n : Nat) : Int := mobiusInvSumList n (divisors n)

/-! ### Möbius inversion at small `n` -/

theorem mobiusInv_6  : mobiusInvSum 6  = (phi 6  : Int) := by decide
theorem mobiusInv_10 : mobiusInvSum 10 = (phi 10 : Int) := by decide
theorem mobiusInv_12 : mobiusInvSum 12 = (phi 12 : Int) := by decide
theorem mobiusInv_15 : mobiusInvSum 15 = (phi 15 : Int) := by decide
theorem mobiusInv_30 : mobiusInvSum 30 = (phi 30 : Int) := by decide

/-! ## Dirichlet convolution `μ * 1 = δ`: `Σ_{d ∣ n} μ(d) = [n = 1]` -/

/-- Sum `μ d` over a list of divisors, in `Int`. -/
def sumMobiusList : List Nat → Int
  | []      => 0
  | d :: ds => mobius d + sumMobiusList ds

/-- `Σ_{d ∣ n} μ(d)`. -/
def sumMobius (n : Nat) : Int := sumMobiusList (divisors n)

/-! ### Kronecker delta witness `Σ_{d ∣ n} μ(d) = [n = 1]` -/

theorem sumMobius_1  : sumMobius 1  = 1 := by decide
theorem sumMobius_2  : sumMobius 2  = 0 := by decide
theorem sumMobius_6  : sumMobius 6  = 0 := by decide
theorem sumMobius_12 : sumMobius 12 = 0 := by decide
theorem sumMobius_30 : sumMobius 30 = 0 := by decide

end EulerTotientMobiusInversion
end Gnosis
