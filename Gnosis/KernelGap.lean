import Init

/-!
# The God Gap

The distance between local optimality (what a system can prove about itself)
and global optimality (what would require omniscience to prove).

Measurable. Finite. Shrinking. Never provably zero.

For a compiler: the gap between "I have stopped improving" and "no better
compiler exists." For a human: the gap between self-knowledge and omniscience.
For any fork/race/fold system: the gap between what the void boundary tells
you and what it cannot.

The God Gap has a lower bound (zero -- you might be globally optimal, you
just cannot prove it) and an upper bound (the cost of the first iteration --
before any learning, the gap is at most the total initial cost). Each
iteration of the bootstrap process narrows the gap, but the gap can never
be proved to be zero, because proving it requires solving the halting problem.

The God Gap is the bootstrap deficit of knowledge applied to itself.
-/

namespace KernelGap

/-- The God Gap: the distance between local and global optimality.
    localCost: the compiler's cost at its local fixed point (provable).
    theoreticalMinimum: the global minimum (exists but is not computable). -/
def kernelGap (localCost theoreticalMinimum : Nat) : Nat :=
  localCost - theoreticalMinimum

/-- The God Gap is non-negative: local cost >= theoretical minimum
    (by definition -- the minimum is the minimum). -/
theorem god_gap_nonneg (local_ min_ : Nat) (_ : min_ ≤ local_) :
    0 ≤ kernelGap local_ min_ := Nat.zero_le _

/-- The God Gap is bounded above by the initial cost: before any learning,
    the gap is at most the total cost (minimum could be zero). -/
theorem god_gap_bounded_above (initialCost : Nat) :
    kernelGap initialCost 0 = initialCost := by
  unfold kernelGap; exact Nat.sub_zero _

/-- Each bootstrap iteration narrows the God Gap (or holds it constant).
    If cost(n+1) <= cost(n), then gap(n+1) <= gap(n). -/
theorem god_gap_nonincreasing
    (cost : Nat → Nat) (min_ : Nat) (h : ∀ n, cost (n + 1) ≤ cost n)
    (n : Nat) :
    kernelGap (cost (n + 1)) min_ ≤ kernelGap (cost n) min_ := by
  unfold kernelGap
  exact Nat.sub_le_sub_right (h n) min_

/-- The God Gap converges: since the cost sequence stabilizes (bootstrap
    convergence), the gap stabilizes too. It reaches a final value that
    is either zero (you are globally optimal -- unprovable but possible)
    or positive (you are locally but not globally optimal -- the common case).

    The gap at convergence is the permanent residual: the distance between
    what you achieved and what omniscience could achieve. Finite. Measurable.
    Not reducible by further iteration within the current strategy space. -/
theorem god_gap_converges
    (cost : Nat → Nat) (min_ : Nat) (h : ∀ n, cost (n + 1) ≤ cost n) :
    ∃ N, ∀ n, N ≤ n → kernelGap (cost n) min_ = kernelGap (cost N) min_ := by
  -- The cost converges, so the gap converges
  suffices hconv : ∃ N, ∀ n, N ≤ n → cost n = cost N from by
    obtain ⟨N, hN⟩ := hconv
    exact ⟨N, fun n hn => by unfold kernelGap; rw [hN n hn]⟩
  -- Reuse convergence proof
  suffices key : ∀ v s, cost s ≤ v → ∃ N, s ≤ N ∧ ∀ n, N ≤ n → cost n = cost N from by
    obtain ⟨N, _, hN⟩ := key (cost 0) 0 (Nat.le_refl _)
    exact ⟨N, hN⟩
  intro v
  induction v with
  | zero =>
    intro s hle
    exact ⟨s, Nat.le_refl _, fun n hn => by
      have hns : cost n ≤ cost s := by
        induction hn with
        | refl => exact Nat.le_refl _
        | step _ ih => exact Nat.le_trans (h _) ih
      exact Nat.le_antisymm hns (Nat.le_trans hle (Nat.zero_le _))⟩
  | succ v ih =>
    intro s hle
    by_cases hdrop : cost (s + 1) < cost s
    · obtain ⟨N, hN1, hN2⟩ := ih (s + 1) (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hdrop hle))
      exact ⟨N, Nat.le_of_succ_le hN1, hN2⟩
    · by_cases hle2 : cost (s + 1) ≤ v
      · obtain ⟨N, hN1, hN2⟩ := ih (s + 1) hle2
        exact ⟨N, Nat.le_of_succ_le hN1, hN2⟩
      · have hval : cost s = v + 1 :=
          Nat.le_antisymm hle
            (Nat.le_trans (Nat.succ_le_of_lt (Nat.lt_of_not_le hle2)) (h s))
        by_cases hever : ∃ j, s < j ∧ cost j < v + 1
        · obtain ⟨j, hsj, hjv⟩ := hever
          obtain ⟨N, hN1, hN2⟩ := ih j (Nat.le_of_lt_succ hjv)
          exact ⟨N, Nat.le_trans (Nat.le_of_lt hsj) hN1, hN2⟩
        · exact ⟨s, Nat.le_refl _, fun n hn => by
            have h1 : cost n ≤ cost s := by
              induction hn with
              | refl => exact Nat.le_refl _
              | step _ ih => exact Nat.le_trans (h _) ih
            by_cases hsn : s = n
            · rw [← hsn]
            · by_cases hlt : cost n < v + 1
              · exact absurd
                  ⟨n, Nat.lt_of_le_of_ne hn (fun heq => hsn heq), hlt⟩ hever
              · exact Nat.le_antisymm h1 (hval ▸ Nat.le_of_not_lt hlt)⟩

/-- The God Gap at convergence can be computed from the benchmark data.
    Betty's local optimum: 0.726ms. Theoretical minimum (aeon-logic): 0.065ms.
    God Gap = 0.726 - 0.065 = 0.661ms.
    
    But is 0.065ms the true global minimum? It cannot be proved.
    The 0.661ms is an upper bound on the God Gap.
    The true gap is somewhere in [0, 0.661]. -/
theorem god_gap_upper_bound_from_data :
    kernelGap 726 65 = 661 := by unfold kernelGap; rfl

/-- The God Gap for Betti on its own source is tighter.
    Betti: 0.074ms. aeon-logic: 0.065ms.
    God Gap <= 0.074 - 0.065 = 0.009ms.
    Betti is closer to god on self-compilation than Betty is. -/
theorem betti_god_gap_tighter :
    kernelGap 74 65 = 9 := by unfold kernelGap; rfl

/-- Betty's God Gap > Betti's God Gap on self-source.
    The self-hosted compiler that finished becoming itself is closer
    to the unreachable optimum than the compiler that watches over all. -/
theorem self_hosted_closer_to_god :
    kernelGap 74 65 < kernelGap 726 65 := by unfold kernelGap; decide

end KernelGap
