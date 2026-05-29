import Init
import Gnosis.KnotRopelengthComplexity

/-
  KnotRopelengthSuperpolynomial.lean
  ==================================

  Strengthens `KnotRopelengthComplexity`: that module proved the ropelength gap
  `npRopelength n > n^k` only for bounded degree (`betti_lattice_gap` carries
  `hk : k ≤ 10`). Here we prove it for EVERY `k`, discharging
  `inNPStratum npRopelength` in full — i.e. `npRopelength = 1 + 2^n` genuinely
  grows faster than every fixed polynomial.

  HONEST SCOPE. This is the elementary fact "`2^n` eventually exceeds `n^k`"
  (`exp_beats_poly`), made fully general. It is NOT a proof of P ≠ NP: the
  P/NP reading rests on the *definitions* `npRopelength := 1 + 2^n` and
  `polynomialBudget := n^k` (the posited identification of complexity classes
  with topological charge), which this module — like the rope module — does not
  derive from the Turing-machine definitions of P and NP. Such an arithmetic
  gap relativizes, so by Baker–Gill–Solovay it cannot separate P from NP. What
  we prove here is exactly the true content: the exponential outruns every
  polynomial.

  Init + the rope module. Zero `sorry`, zero new `axiom`.
-/

namespace KnotRopelengthSuperpolynomial

open KnotRopelengthComplexity

/-! ## Polynomial expansions (Init-only, no `ring`) -/

theorem expand_sq3 (j : Nat) : (j + 3) * (j + 3) = j * j + 6 * j + 9 := by
  simp only [Nat.add_mul, Nat.mul_add]; omega

theorem expand_sq2 (j : Nat) : (j + 2) * (j + 2) = j * j + 4 * j + 4 := by
  simp only [Nat.add_mul, Nat.mul_add]; omega

/-! ## The exponential outruns every polynomial -/

/-- `k·k + k < 2^(k+1)` for all `k`. The `k = 0, 1` burn-in is handled directly;
    for `k ≥ 2` the inductive step closes with slack `(j+1)(j+2) > 0`. -/
theorem poly_lt_exp_aux (k : Nat) : k * k + k < 2 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rcases k with _ | _ | j
    · decide
    · decide
    · -- k = j + 2; goal is about j + 3
      have hih : (j + 2) * (j + 2) + (j + 2) < 2 ^ (j + 3) := ih
      show (j + 3) * (j + 3) + (j + 3) < 2 ^ (j + 3 + 1)
      rw [expand_sq3, Nat.pow_succ]
      rw [expand_sq2] at hih
      omega

/-- `2^n` is positive (`Classical`-free, unlike some core `pow` lemmas). -/
theorem two_pow_pos (n : Nat) : 0 < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- `2^·` is strictly monotone (`Classical`-free; the core
    `Nat.pow_lt_pow_right` carries `Classical.choice`). -/
theorem two_pow_lt (m n : Nat) (h : m < n) : 2 ^ m < 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hpos : 0 < 2 ^ n := two_pow_pos n
    rcases Nat.lt_or_ge m n with hmn | hmn
    · have h1 : 2 ^ m < 2 ^ n := ih hmn
      have h2 : 2 ^ n < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
      omega
    · have hmn' : m = n := by omega
      subst hmn'
      rw [Nat.pow_succ]; omega

/-- **The exponential outruns every polynomial.** For every degree `k` there is
    an `n` with `n^k < 2^n`. Witness: `n = 2^(k+1)`, using `(k+1)·k < 2^(k+1)`. -/
theorem exp_beats_poly (k : Nat) : ∃ n, n ^ k < 2 ^ n := by
  refine ⟨2 ^ (k + 1), ?_⟩
  rw [← Nat.pow_mul]
  apply two_pow_lt
  have e : (k + 1) * k = k * k + k := by rw [Nat.add_mul, Nat.one_mul]
  rw [e]
  exact poly_lt_exp_aux k

/-! ## Discharging `inNPStratum npRopelength` for ALL k -/

/-- The NP ropelength exceeds every fixed polynomial degree — for ALL `k`
    (not just `k ≤ 10`). -/
theorem npRopelength_superpolynomial (k : Nat) :
    ∃ n, npRopelength n > n ^ k := by
  obtain ⟨n, hn⟩ := exp_beats_poly k
  refine ⟨n, ?_⟩
  rw [npRopelengthValue]
  omega

/-- **`npRopelength` is in the NP-stratum, in full.** This discharges the rope
    module's `inNPStratum` for every degree — the bounded `k ≤ 10` ceiling of
    `betti_lattice_gap` is removed. The exponential ropelength is genuinely
    superpolynomial. (Still a statement about `1 + 2^n`, not a P ≠ NP proof —
    see the module header.) -/
theorem npRopelength_inNPStratum : inNPStratum npRopelength :=
  npRopelength_superpolynomial

end KnotRopelengthSuperpolynomial
