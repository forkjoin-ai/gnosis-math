import Init
import Gnosis.AckermannFunction
import Gnosis.AckermannUniversality
import Gnosis.AckermannMonotone
import Gnosis.KnotRopelengthComplexity
import Gnosis.SuperpolynomialFront

/-
  FrontHierarchy.lean
  ===================

  The three superpolynomial fronts are ORDERED, and "outpaces every polynomial"
  is monotone up the order. So the smallest front carries the whole result: once
  `2^n` outpaces, every taller front does too — the cleanest "strengthen by
  weakening" (prove the weakest front, lift to the rest).

    * `exp_le_rope`           : `2^n ≤ npRopelength n`   (the `+1 = β₀` only adds).
    * `ackermann_dominates_exp`: `2^n ≤ A(n)` for `n ≥ 3` (via `A(n) ≥ n^n ≥ 2^n`).
    * `OutpacesPolys_mono`    : domination lifts `OutpacesPolys` upward.
    * `rope_outpaces'`        : the rope front outpaces — re-derived from the
                                exponential by monotonicity alone.

  The Ackermann luminal ceiling is the tallest of the three fronts; the
  exponential is the floor.

  HONEST SCOPE (unchanged): structure of true superpolynomial fronts; NOT a
  P ≠ NP proof (the class↔front identification relativizes, BGS).

  Init + the program. Zero `sorry`, zero new `axiom`.
-/

namespace FrontHierarchy

open AckermannFunction
open KnotRopelengthComplexity
open SuperpolynomialFront

/-- "Outpaces every polynomial" is monotone: a pointwise-taller front also
    outpaces. -/
theorem OutpacesPolys_mono {S S' : Nat → Nat} (hle : ∀ n, S n ≤ S' n)
    (h : OutpacesPolys S) : OutpacesPolys S' := by
  intro k
  obtain ⟨n, hn⟩ := h k
  exact ⟨n, Nat.lt_of_lt_of_le hn (hle n)⟩

/-- The exponential is below the NP ropelength (`2^n ≤ 1 + 2^n`). -/
theorem exp_le_rope (n : Nat) : 2 ^ n ≤ npRopelength n := by
  rw [npRopelengthValue]; omega

/-- **The Ackermann ceiling dominates the exponential.** For `n ≥ 3`,
    `2^n ≤ A(n)`, since `A(n) = hyperop n n n ≥ hyperop 3 n n = n^n ≥ 2^n`. The
    luminal ceiling is the tallest front. -/
theorem ackermann_dominates_exp (n : Nat) (hn : 3 ≤ n) : 2 ^ n ≤ ackermannDiag n := by
  have h1 : hyperop 3 n n ≤ hyperop n n n :=
    AckermannMonotone.level_mono 3 n n n (by omega) (by omega) hn
  have h2 : hyperop 3 n n = n ^ n := AckermannUniversality.hyperop_three n n
  have h3 : 2 ^ n ≤ n ^ n := Nat.pow_le_pow_left (by omega) n
  show 2 ^ n ≤ hyperop n n n
  omega

/-- The rope front outpaces every polynomial — re-derived from the exponential
    by monotonicity alone (no fresh arithmetic). -/
theorem rope_outpaces' : OutpacesPolys npRopelength :=
  OutpacesPolys_mono exp_le_rope exp_outpaces

/-- **The front hierarchy.** At every `n ≥ 3`, the exponential floor sits below
    both the NP ropelength and the Ackermann luminal ceiling. -/
theorem front_hierarchy (n : Nat) (hn : 3 ≤ n) :
    2 ^ n ≤ npRopelength n ∧ 2 ^ n ≤ ackermannDiag n :=
  ⟨exp_le_rope n, ackermann_dominates_exp n hn⟩

end FrontHierarchy
