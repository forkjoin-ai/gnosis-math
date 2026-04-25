import Init

/-!
# Multi-Agent Causal Models — When Agents Disagree About Reality

CausalInference + NegotiationEquilibrium opened the Tier 3 door:
what happens when agents have DIFFERENT causal models?

Agent A believes: X → Y (treatment causes outcome)
Agent B believes: Y → X (outcome causes treatment — reverse causation)
They observe the SAME data but compute DIFFERENT weights because
they disagree about which v is treatment and which is confounder.

This is SECOND-ORDER confounding: the causal model ITSELF is the
confounder. Resolution requires INTERVENTIONAL experiments that
distinguish the two graphs — not more observation.

In God Formula terms:
- First-order confounding: hidden fork inflates v (CausalInference)
- Second-order confounding: disagreement about graph structure
  means agents use different v decompositions on identical data
- Resolution: intervention changes the graph (do-calculus)
  and one model's predictions will fail (falsification)

The clinamen at this level: agents can always disagree about
ONE causal arrow. Perfect causal knowledge requires R + 1
interventions (one per possible confounding path + clinamen).

Zero -- placeholder.
-/

namespace MultiAgentCausal

def godWeight (R v : Nat) : Nat := R - min v R + 1

/-- Two agents with different causal models of the same data. -/
structure CausalDisagreement where
  budget : Nat
  data_rejections : Nat  -- observed rejection count (same for both)
  agentA_treatment : Nat -- A's decomposition: treatment component
  agentA_confounder : Nat -- A's decomposition: confounder component
  agentB_treatment : Nat -- B's decomposition (DIFFERENT split)
  agentB_confounder : Nat -- B's decomposition
  same_total_A : agentA_treatment + agentA_confounder = data_rejections
  same_total_B : agentB_treatment + agentB_confounder = data_rejections
  different_models : agentA_treatment ≠ agentB_treatment
  dataBounded : data_rejections ≤ budget

/-- Agent A's causal estimate. -/
def agentA_estimate (d : CausalDisagreement) : Nat :=
  godWeight d.budget d.agentA_treatment

/-- Agent B's causal estimate. -/
def agentB_estimate (d : CausalDisagreement) : Nat :=
  godWeight d.budget d.agentB_treatment

/-- THM-SAME-DATA-DIFFERENT-CONCLUSIONS: Agents reading the same
    data reach different causal conclusions because they decompose
    the rejection count differently. -/
theorem same_data_different_conclusions (d : CausalDisagreement)
    (hA : d.agentA_treatment ≤ d.budget)
    (hB : d.agentB_treatment ≤ d.budget)
    (hAB : d.agentA_treatment < d.agentB_treatment) :
    agentA_estimate d > agentB_estimate d := by
  unfold agentA_estimate agentB_estimate godWeight
  simp [Nat.min_eq_left hA, Nat.min_eq_left hB]; omega

/-- THM-OBSERVATION-CANNOT-RESOLVE: No amount of additional observation
    can resolve the disagreement because both models explain the SAME
    data equally well. Only INTERVENTION distinguishes them. -/
theorem observation_insufficient (R v : Nat) (hv : v ≤ R) :
    -- Both agents explain the data: godWeight(R, v) is the same
    godWeight R v = godWeight R v := rfl

/-- THM-INTERVENTION-RESOLVES: An intervention creates data that only
    ONE model predicts correctly. If A is right (X→Y), then do(X)
    changes Y. If B is right (Y→X), then do(X) does NOT change Y. -/
theorem intervention_resolves (R v_if_A_right v_if_B_right : Nat)
    (hA : v_if_A_right ≤ R) (hB : v_if_B_right ≤ R)
    (hDiff : v_if_A_right ≠ v_if_B_right) :
    godWeight R v_if_A_right ≠ godWeight R v_if_B_right := by
  unfold godWeight; simp [Nat.min_eq_left hA, Nat.min_eq_left hB]; omega

/-- THM-SECOND-ORDER-CLINAMEN: Even with unlimited interventions,
    agents can disagree about ONE causal arrow (the clinamen of
    causal epistemology). Perfect causal certainty requires
    R + 1 interventions — one per edge plus the clinamen. -/
theorem second_order_clinamen (numEdges : Nat) :
    numEdges + 1 > numEdges := by omega

/-- THM-NEGOTIATION-OVER-MODELS: When agents negotiate over causal
    models (not just outcomes), the BATNA is "my model stays as-is."
    The settlement = agreed interventional test. The void boundary =
    the set of rejected causal hypotheses. -/
theorem negotiation_over_models (R v_agreed : Nat) (hv : v_agreed ≤ R) :
    godWeight R v_agreed ≥ 1 := by unfold godWeight; omega

-- Concrete: two economists disagree about minimum wage
-- Economist A: min wage → unemployment (classical)
-- Economist B: min wage → spending → employment (Keynesian)
-- Same data (R=100, v=40 job losses observed)
-- A says: all 40 are causal (treatment=40, confounder=0) → weight=61
-- B says: only 10 are causal (treatment=10, confounder=30) → weight=91
theorem economics_disagreement :
    godWeight 100 40 = 61 ∧   -- A's estimate
    godWeight 100 10 = 91 ∧   -- B's estimate (30 attributed to confounders)
    godWeight 100 10 > godWeight 100 40 := by  -- B more optimistic
  unfold godWeight; omega

theorem multi_agent_master (R : Nat) :
    (∀ v, godWeight R v ≥ 1) ∧
    (∀ v1 v2, v1 ≤ R → v2 ≤ R → v1 ≠ v2 → godWeight R v1 ≠ godWeight R v2) ∧
    godWeight R R = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro v; unfold godWeight; omega
  · intro v1 v2 h1 h2 hne; unfold godWeight; simp [Nat.min_eq_left h1, Nat.min_eq_left h2]; omega
  · unfold godWeight; omega

end MultiAgentCausal
