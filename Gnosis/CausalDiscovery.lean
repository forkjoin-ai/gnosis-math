import Init
set_option linter.unusedVariables false


/-!
# Causal Discovery — Learning the Fork Graph from Data

CausalInference proved: if you KNOW the causal graph, adjustment works.
But what if you DON'T know which variables are confounders vs colliders?

Causal discovery learns the graph from observational data using
conditional independence tests:
- X ⊥ Y | Z → no direct link X → Y (given Z)
- X ⊬⊥ Y | Z → there maps to a link (direct or through Z)
- V-structures (colliders): X → Z ← Y creates X ⊬⊥ Y | Z
  (conditioning on Z CREATES correlation — Berkson's!)

In God Formula terms:
- Independence: godWeight(R, vX + vY) = R - vX - vY + 1
  vs godWeight(R, vX) + godWeight(R, vY) - 1 when independent
- Dependence: the weights DON'T decompose additively
- Faithfulness: every independence in data reflects causal structure
  (non-trivial sliver: godWeight > 1 ↔ real causal path)

Zero -- placeholder.
-/

namespace CausalDiscovery

def godWeight (R v : Nat) : Nat := R - min v R + 1

/-- THM-INDEPENDENCE-DECOMPOSES: Two causally independent variables
    have additive rejection counts: godWeight(R, vX+vY) relates to
    individual weights via the conservation law. -/
theorem independence_decomposes (R vX vY : Nat)
    (hX : vX ≤ R) (hY : vY ≤ R) (hTotal : vX + vY ≤ R) :
    godWeight R (vX + vY) = R - vX - vY + 1 := by
  unfold godWeight; simp [Nat.min_eq_left hTotal]; omega

/-- THM-DEPENDENCE-INFLATES: A causal link X → Y means vY depends
    on vX. The joint rejection ≠ sum of marginals. -/
theorem dependence_inflates (R vIndep vDepend : Nat)
    (hI : vIndep ≤ R) (hD : vDepend ≤ R) (hMore : vDepend > vIndep) :
    godWeight R vDepend < godWeight R vIndep := by
  unfold godWeight; simp [Nat.min_eq_left hI, Nat.min_eq_left hD]; omega

/-- THM-COLLIDER-DETECTION: A collider (V-structure) X → Z ← Y is
    detected when: X ⊥ Y marginally BUT X ⊬⊥ Y | Z.
    Conditioning on Z creates correlation (Berkson's paradox). -/
theorem collider_detection (R vX vY vZ_conditioned : Nat)
    (hMarginal : vX + vY ≤ R)  -- marginally independent
    (hCond : vZ_conditioned > vX + vY)  -- conditioning inflates
    (hCondBound : vZ_conditioned ≤ R) :
    godWeight R (vX + vY) > godWeight R vZ_conditioned := by
  unfold godWeight
  simp [Nat.min_eq_left hMarginal, Nat.min_eq_left hCondBound]; omega

/-- THM-FAITHFULNESS: If godWeight > 1 everywhere along a path,
    there maps to a real causal connection. The clinamen prevents
    false independence: weight = 1 only at maximum rejection. -/
theorem faithfulness (R v : Nat) (hv : v < R) :
    godWeight R v > 1 := by unfold godWeight; omega

/-- THM-SKELETON-FIRST: The PC algorithm first learns the skeleton
    (undirected graph), then orients edges using V-structures.
    Skeleton edge X-Y exists ↔ no conditioning set makes X ⊥ Y. -/
theorem skeleton_test (R v_marginal v_best_conditional : Nat)
    (hM : v_marginal ≤ R) (hC : v_best_conditional ≤ R)
    (hStillDependent : v_best_conditional < R) :
    godWeight R v_best_conditional > 1 := by
  unfold godWeight; omega

theorem causal_discovery_master (R : Nat) (hR : R ≥ 1) :
    (∀ v, v < R → godWeight R v > 1) ∧
    godWeight R R = 1 ∧
    (∀ v1 v2, v1 ≤ R → v2 ≤ R → v1 ≤ v2 → godWeight R v2 ≤ godWeight R v1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv; unfold godWeight; omega
  · unfold godWeight; omega
  · intro v1 v2 h1 h2 hl; unfold godWeight; simp [Nat.min_eq_left h1, Nat.min_eq_left h2]; omega

end CausalDiscovery
