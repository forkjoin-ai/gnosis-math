import Init

/-!
# Self-Hosting Optimality: Theorem and Anti-Theorem

Empirical compiler shootout (Betty, Betti, Franky, Beckett, aeon-logic):
- Betti on betti.gg: SELF-OPTIMAL (fastest of five)
- Franky on franky.gg: NOT self-optimal (4th of 5)
- Beckett on beckett.gg: NOT self-optimal (4th of 5)

Success is shaped by these failures. You are fastest on yourself
if and only if you have finished becoming yourself.
-/

namespace SelfHostingOptimality

-- ANTI-THEOREM
theorem self_optimality_not_universal :
    ∃ (specialized generic : Nat), 0 < specialized ∧ 0 < generic ∧ generic < specialized :=
  ⟨10, 1, by decide, by decide, by decide⟩

-- Bootstrap deficit
def bootstrapDeficit (selfCost fixedPointCost : Nat) : Nat := selfCost - fixedPointCost

theorem deficit_zero_at_fixed_point (c : Nat) : bootstrapDeficit c c = 0 := by
  unfold bootstrapDeficit; exact Nat.sub_self c

theorem deficit_positive_off_fixed_point (s fp : Nat) (h : fp < s) :
    0 < bootstrapDeficit s fp := by
  unfold bootstrapDeficit; exact Nat.sub_pos_of_lt h

-- Monotone descent
theorem monotone_descent (cost : Nat → Nat) (h : ∀ n, cost (n + 1) ≤ cost n)
    (n m : Nat) (hnm : n ≤ m) : cost m ≤ cost n := by
  induction hnm with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans (h _) ih

-- Bootstrap convergence via well-founded recursion on cost value.
private theorem stable_from (cost : Nat → Nat) (h : ∀ n, cost (n + 1) ≤ cost n) (s : Nat) :
    ∀ v, cost s ≤ v → ∃ N, s ≤ N ∧ ∀ n, N ≤ n → cost n = cost N := by
  intro v
  induction v generalizing s with
  | zero =>
    intro hle
    refine ⟨s, Nat.le_refl _, fun n hn => ?_⟩
    have hCnLeS : cost n ≤ cost s := monotone_descent cost h s n hn
    have hCsZero : cost s = 0 := Nat.le_zero.mp hle
    have hCnZero : cost n = 0 := Nat.le_zero.mp (Nat.le_trans hCnLeS hle)
    rw [hCnZero, hCsZero]
  | succ v ih =>
    intro hle
    by_cases hdrop : cost (s + 1) < cost s
    · have hStepLeV : cost (s + 1) ≤ v :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hdrop hle)
      obtain ⟨N, hN1, hN2⟩ := ih (s + 1) hStepLeV
      exact ⟨N, Nat.le_trans (Nat.le_succ s) hN1, hN2⟩
    · have hSleStep : cost s ≤ cost (s + 1) := Nat.le_of_not_lt hdrop
      have heq : cost (s + 1) = cost s := Nat.le_antisymm (h s) hSleStep
      by_cases hle2 : cost (s + 1) ≤ v
      · obtain ⟨N, hN1, hN2⟩ := ih (s + 1) hle2
        exact ⟨N, Nat.le_trans (Nat.le_succ s) hN1, hN2⟩
      · -- cost(s) = cost(s+1) = v+1.
        have hVLtStep : v < cost (s + 1) := Nat.lt_of_not_le hle2
        have hSuccLeStep : v + 1 ≤ cost (s + 1) := Nat.succ_le_of_lt hVLtStep
        have hSuccLeS : v + 1 ≤ cost s := heq ▸ hSuccLeStep
        have hval : cost s = v + 1 := Nat.le_antisymm hle hSuccLeS
        by_cases hever : ∃ j, s < j ∧ cost j < v + 1
        · obtain ⟨j, hjs, hjv⟩ := hever
          have hjLeV : cost j ≤ v := Nat.le_of_lt_succ hjv
          obtain ⟨N, hN1, hN2⟩ := ih j hjLeV
          exact ⟨N, Nat.le_trans (Nat.le_of_lt hjs) hN1, hN2⟩
        · have hflat : ∀ n, s ≤ n → cost n = v + 1 := by
            intro n hn
            have hCnLeS : cost n ≤ cost s := monotone_descent cost h s n hn
            by_cases hsn : s = n
            · rw [← hsn]; exact hval
            · have hsltn : s < n := Nat.lt_of_le_of_ne hn hsn
              by_cases hlt : cost n < v + 1
              · exact absurd ⟨n, hsltn, hlt⟩ hever
              · -- cost n ≥ v+1 (from ¬<) and cost n ≤ cost s = v+1 ⇒ cost n = v+1
                have hCnGe : v + 1 ≤ cost n := Nat.le_of_not_lt hlt
                have hCnLeVSucc : cost n ≤ v + 1 := hval ▸ hCnLeS
                exact Nat.le_antisymm hCnLeVSucc hCnGe
          exact ⟨s, Nat.le_refl _, fun n hn => by
            rw [hflat n hn, hflat s (Nat.le_refl _)]⟩

theorem bootstrap_convergence (cost : Nat → Nat) (h : ∀ n, cost (n + 1) ≤ cost n) :
    ∃ N, ∀ n, N ≤ n → cost n = cost N := by
  obtain ⟨N, _, hN⟩ := stable_from cost h 0 (cost 0) (Nat.le_refl _)
  exact ⟨N, hN⟩

-- Self-optimality ↔ zero deficit
theorem self_optimality_iff_zero_deficit (s c : Nat) :
    s ≤ c ↔ bootstrapDeficit s c = 0 := by
  unfold bootstrapDeficit
  exact ⟨Nat.sub_eq_zero_of_le, Nat.le_of_sub_eq_zero⟩

-- Failure shapes success
theorem failure_shapes_success (N : Nat) (hN : 2 ≤ N) : N - 1 ≥ 1 :=
  Nat.le_sub_of_add_le hN
theorem rejection_dominates (N : Nat) (hN : 3 ≤ N) : N - 1 > 1 :=
  Nat.lt_sub_of_add_lt
    (Nat.lt_of_lt_of_le (by decide : (1 + 1 : Nat) < 3) hN)
theorem five_compiler_void : 5 - 1 = 4 ∧ (4 : Nat) > 1 := by decide

-- Deficit is learnable
theorem deficit_is_learnable (deficit : Nat → Nat) (h : ∀ n, deficit (n + 1) ≤ deficit n) :
    ∃ N, deficit N = 0 ∨ (∀ n, N ≤ n → deficit n = deficit N) := by
  obtain ⟨N, hN⟩ := bootstrap_convergence deficit h
  exact ⟨N, Or.inr hN⟩

end SelfHostingOptimality
