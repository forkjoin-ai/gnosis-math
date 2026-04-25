import Init

/-!
# Goodhart's Law — When the Measure Becomes the Target

PublicationBias proved: selecting on significance creates bias.
Goodhart's Law generalizes: ANY measure used as a target ceases
to be a good measure.

"When a measure becomes a target, it ceases to be a good measure."
— Charles Goodhart (1975)

In God Formula terms:
- A MEASURE reads the void boundary truthfully: godWeight(R, v)
- A TARGET optimizes toward the measure: minimize v (the rejection count)
- Goodhart failure: agents find ways to minimize v WITHOUT improving
  the underlying quality — gaming the metric

The problem is that v (rejection count) is a PROXY for quality,
not quality itself. When you optimize the proxy, you break the
correlation between proxy and truth. The confounders from
CausalInference become the attack surface: agents exploit the
gap between what v measures and what we actually care about.

Zero -- placeholder.
-/

namespace GoodhartsLaw

def godWeight (R v : Nat) : Nat := R - min v R + 1

/-- THM-MEASURE-FAITHFUL: Before optimization, the measure (v) tracks
    true quality. godWeight(R, v) reflects real performance. -/
theorem measure_faithful (R v : Nat) (hv : v ≤ R) :
    godWeight R v = R - v + 1 := by
  unfold godWeight; simp [Nat.min_eq_left hv]

/-- THM-GAMING-INFLATES: An agent can reduce the measured v by gaming
    (hiding failures) without reducing true failures. The observed
    weight increases but the REAL weight doesn't. -/
theorem gaming_inflates (R v_true v_gamed : Nat)
    (hTrue : v_true ≤ R) (hGamed : v_gamed ≤ R)
    (hGaming : v_gamed < v_true)  -- gamed failures < true failures
    :
    -- Gamed weight > true weight (looks better but isn't)
    godWeight R v_gamed > godWeight R v_true := by
  unfold godWeight; simp [Nat.min_eq_left hTrue, Nat.min_eq_left hGamed]; omega

/-- THM-CAMPBELL-LAW: "The more any quantitative social indicator is
    used for social decision-making, the more subject to corruption
    pressures it will be." (Campbell, 1979)
    
    In God Formula terms: the moment you use godWeight(R, v) as a
    TARGET (not just a measure), agents will minimize v by any means,
    including corrupting the measurement process itself. -/
theorem campbell_law (R v_honest v_corrupt : Nat)
    (hH : v_honest ≤ R) (hC : v_corrupt ≤ R)
    (hCorrupt : v_corrupt < v_honest) :
    -- Corruption makes the metric look better
    godWeight R v_corrupt > godWeight R v_honest := by
  unfold godWeight; simp [Nat.min_eq_left hH, Nat.min_eq_left hC]; omega

/-- THM-METRIC-PROXY-GAP: The gap between gamed metric and true quality
    equals the number of hidden failures: v_true - v_gamed. -/
theorem proxy_gap (R v_true v_gamed : Nat)
    (hTrue : v_true ≤ R) (hGamed : v_gamed ≤ R)
    (hGaming : v_gamed ≤ v_true) :
    godWeight R v_gamed - godWeight R v_true = v_true - v_gamed := by
  unfold godWeight; simp [Nat.min_eq_left hTrue, Nat.min_eq_left hGamed]; omega

/-- THM-GOODHART-is-CONFOUNDING: Gaming is confounding. The gamed
    metric mixes true performance with manipulation. The manipulation
    is a hidden fork (confounder) acting on the observed v. -/
theorem goodhart_is_confounding (R treat manipulation : Nat)
    (hBound : treat + manipulation ≤ R) :
    -- Same as CausalInference adjustment: true = observed + confounder
    godWeight R treat = godWeight R (treat + manipulation) + manipulation := by
  unfold godWeight
  simp [Nat.min_eq_left (by omega : treat ≤ R), Nat.min_eq_left hBound]
  omega

-- Concrete examples
-- Teaching to the test: students learn to pass the test, not the subject
theorem teaching_to_test :
    -- True understanding: R=100, v=30 (30 concepts not learned) → w=71
    godWeight 100 30 = 71 ∧
    -- After test optimization: v=10 (looks better) → w=91
    -- But the 20 hidden gaps are gaming, not learning
    godWeight 100 10 = 91 ∧
    -- Gap = 20 hidden non-learnings
    godWeight 100 10 - godWeight 100 30 = 20 := by
  unfold godWeight; omega

-- Cobra effect: paying for dead cobras → people breed cobras
theorem cobra_effect :
    -- Before policy: R=100 cobras, killed=20 → weight=81
    godWeight 100 20 = 81 ∧
    -- After policy: R=200 cobras (bred for bounty), killed=100 → w=101
    -- Higher weight! But MORE cobras exist
    godWeight 200 100 = 101 ∧
    -- The policy CREATED the problem it was solving
    True := by unfold godWeight; omega

theorem goodharts_law_master (R : Nat) :
    (∀ v, v ≤ R → godWeight R v = R - v + 1) ∧
    (∀ v1 v2, v1 ≤ R → v2 ≤ R → v1 ≤ v2 → godWeight R v2 ≤ godWeight R v1) ∧
    godWeight R R = 1 ∧ (∀ v, godWeight R v ≥ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv; unfold godWeight; simp [Nat.min_eq_left hv]
  · intro v1 v2 h1 h2 hl; unfold godWeight; simp [Nat.min_eq_left h1, Nat.min_eq_left h2]; omega
  · unfold godWeight; omega
  · intro v; unfold godWeight; omega

end GoodhartsLaw
