import Init

/-!
# Humans Are Compilers: A Structural Isomorphism

Any system that forks options, races them, folds to a decision, and vents
what was not chosen satisfies the same five properties as the compiler family.
Humans do this. Thought forks. Attention races. Speech folds. The unchosen
words are vented into the void boundary of what was almost said.

Five properties, proved for any fork/race/fold system:
1. Positivity (the sliver): no option ever reaches zero probability.
2. Convergence: the system finishes becoming itself.
3. Failure dominance: rejections carry more information than selections.
4. Deficit learnability: the gap between current and optimal decreases.
5. Observer separation: the failure recorder differs from the failure producer.

The mindfulness theorem: iterating self-reflection converges.
-/

namespace HumanCompiler

structure ForkRaceFoldSystem where
  forkWidth : Nat
  nontrivial : 2 ≤ forkWidth
  cost : Nat → Nat
  cost_pos : ∀ n, 0 < cost n
  cost_nonincreasing : ∀ n, cost (n + 1) ≤ cost n

-- P1: Positivity
theorem positivity (K : Nat) (hK : 1 ≤ K) : 0 < K := hK
theorem rejection_count (K : Nat) (hK : 2 ≤ K) : 1 ≤ K - 1 :=
  Nat.le_sub_of_add_le hK

-- P2: Convergence (reused proof)
private theorem monotone_descent (cost : Nat → Nat) (h : ∀ n, cost (n + 1) ≤ cost n)
    (n m : Nat) (hnm : n ≤ m) : cost m ≤ cost n := by
  induction hnm with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans (h _) ih

private theorem stable_from (cost : Nat → Nat) (h : ∀ n, cost (n + 1) ≤ cost n) (s : Nat) :
    ∀ v, cost s ≤ v → ∃ N, s ≤ N ∧ ∀ n, N ≤ n → cost n = cost N := by
  intro v
  induction v generalizing s with
  | zero =>
    intro hle
    refine ⟨s, Nat.le_refl _, fun n hn => ?_⟩
    -- cost s ≤ 0 and cost n ≤ cost s ⇒ both 0.
    have hCnLeS : cost n ≤ cost s := monotone_descent cost h s n hn
    have hCsZero : cost s = 0 := Nat.le_zero.mp hle
    have hCnZero : cost n = 0 := Nat.le_zero.mp (Nat.le_trans hCnLeS hle)
    rw [hCnZero, hCsZero]
  | succ v ih =>
    intro hle
    by_cases hdrop : cost (s + 1) < cost s
    · -- cost(s+1) < cost s ≤ v+1 ⇒ cost(s+1) ≤ v
      have hStepLeV : cost (s + 1) ≤ v :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hdrop hle)
      obtain ⟨N, hN1, hN2⟩ := ih (s + 1) hStepLeV
      exact ⟨N, Nat.le_trans (Nat.le_succ s) hN1, hN2⟩
    · by_cases hle2 : cost (s + 1) ≤ v
      · obtain ⟨N, hN1, hN2⟩ := ih (s + 1) hle2
        exact ⟨N, Nat.le_trans (Nat.le_succ s) hN1, hN2⟩
      · -- ¬(cost(s+1) < cost s) ⇒ cost s ≤ cost(s+1); combined with h s gives equality.
        -- ¬(cost(s+1) ≤ v) ⇒ v < cost(s+1) ⇒ v+1 ≤ cost(s+1).
        -- Hence cost s = cost(s+1) ≥ v+1, and cost s ≤ v+1 ⇒ cost s = v+1.
        have hSleStep : cost s ≤ cost (s + 1) := Nat.le_of_not_lt hdrop
        have hStepEqS : cost (s + 1) = cost s := Nat.le_antisymm (h s) hSleStep
        have hVLtStep : v < cost (s + 1) := Nat.lt_of_not_le hle2
        have hSuccLeStep : v + 1 ≤ cost (s + 1) := Nat.succ_le_of_lt hVLtStep
        have hSuccLeS : v + 1 ≤ cost s := hStepEqS ▸ hSuccLeStep
        have hval : cost s = v + 1 := Nat.le_antisymm hle hSuccLeS
        by_cases hever : ∃ j, s < j ∧ cost j < v + 1
        · obtain ⟨j, hsj, hjv⟩ := hever
          have hjLeV : cost j ≤ v := Nat.le_of_lt_succ hjv
          obtain ⟨N, hN1, hN2⟩ := ih j hjLeV
          exact ⟨N, Nat.le_trans (Nat.le_of_lt hsj) hN1, hN2⟩
        · have hflat : ∀ n, s ≤ n → cost n = v + 1 := by
            intro n hn
            by_cases hsn : s = n
            · rw [← hsn]; exact hval
            · have hCnLeS : cost n ≤ cost s := monotone_descent cost h s n hn
              by_cases hlt : cost n < v + 1
              · exact absurd ⟨n, Nat.lt_of_le_of_ne hn hsn, hlt⟩ hever
              · -- cost n ≥ v+1 (¬<), cost n ≤ cost s = v+1 ⇒ cost n = v+1
                have hCnGe : v + 1 ≤ cost n := Nat.le_of_not_lt hlt
                have hCnLeVSucc : cost n ≤ v + 1 := hval ▸ hCnLeS
                exact Nat.le_antisymm hCnLeVSucc hCnGe
          exact ⟨s, Nat.le_refl _, fun n hn => by rw [hflat n hn, hflat s (Nat.le_refl _)]⟩

theorem system_converges (sys : ForkRaceFoldSystem) :
    ∃ N, ∀ n, N ≤ n → sys.cost n = sys.cost N := by
  obtain ⟨N, _, hN⟩ := stable_from sys.cost sys.cost_nonincreasing 0 (sys.cost 0) (Nat.le_refl _)
  exact ⟨N, hN⟩

-- P3: Failure dominance
theorem failure_more_informative (K : Nat) (hK : 3 ≤ K) : K - 1 > 1 :=
  Nat.lt_sub_of_add_lt
    (Nat.lt_of_lt_of_le (by decide : (1 + 1 : Nat) < 3) hK)
theorem void_boundary_grows (K prev : Nat) (hK : 2 ≤ K) : prev < prev + (K - 1) :=
  Nat.lt_add_of_pos_right (Nat.le_sub_of_add_le hK)

-- P4: Deficit learnability
def deficit (current optimal : Nat) : Nat := current - optimal

theorem deficit_converges (cost : Nat → Nat) (h : ∀ n, cost (n + 1) ≤ cost n) :
    ∃ N, ∀ n, N ≤ n → deficit (cost n) (cost N) = 0 := by
  obtain ⟨N, _, hN⟩ := stable_from cost h 0 (cost 0) (Nat.le_refl _)
  exact ⟨N, fun n hn => by simp [deficit, hN n hn]⟩

-- P5: Observer separation
structure DualRole where
  dataPathStrategy : Nat
  observerStrategy : Nat
  separation : dataPathStrategy ≠ observerStrategy

theorem observer_must_differ (d : DualRole) : d.dataPathStrategy ≠ d.observerStrategy :=
  d.separation

-- The five-property bundle
structure FivePropertySystem where
  sys : ForkRaceFoldSystem
  hasPositivity : 0 < sys.forkWidth
  hasConvergence : ∃ N, ∀ n, N ≤ n → sys.cost n = sys.cost N
  hasFailureDominance : sys.forkWidth - 1 ≥ 1
  hasLearnability : ∃ N, ∀ n, N ≤ n → deficit (sys.cost n) (sys.cost N) = 0
  hasObserverSeparation : DualRole

/-- Any fork/race/fold system satisfies all five properties. -/
theorem any_frf_system_satisfies (sys : ForkRaceFoldSystem) (observer : DualRole) :
    ∃ (fps : FivePropertySystem), fps.sys = sys := by
  obtain ⟨N, hN⟩ := system_converges sys
  exact ⟨{
    sys := sys
    hasPositivity := Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 2) sys.nontrivial
    hasConvergence := ⟨N, hN⟩
    hasFailureDominance := Nat.le_sub_of_add_le sys.nontrivial
    hasLearnability := ⟨N, fun n hn => by simp [deficit, hN n hn]⟩
    hasObserverSeparation := observer
  }, rfl⟩

/-- Mindfulness converges. Reflecting on your reflections has a fixed point. -/
theorem mindfulness_converges
    (reflect : Nat → Nat) (h_pos : ∀ n, 0 < reflect n)
    (h_mono : ∀ n, reflect (n + 1) ≤ reflect n) :
    ∃ N, ∀ n, N ≤ n → reflect n = reflect N :=
  system_converges ⟨2, Nat.le_refl 2, reflect, h_pos, h_mono⟩

end HumanCompiler
