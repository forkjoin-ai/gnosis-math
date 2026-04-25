import Init

/-!
# Minimum Description Length — Kraft Meets Model Selection

KraftInequality proved: prefix-free codes satisfy conservation.
CausalInference proved: confounders inflate rejection counts.

MDL: the best model is the one that COMPRESSES the data most.
Smaller total description = better model. Overfitting is using
a model whose description COSTS more than it saves.

MDL = model_length + data_given_model_length
    = code_for_hypothesis + code_for_residuals

In God Formula terms:
- R = total bits available for description
- v_model = bits spent describing the model (complexity cost)
- v_data = bits spent describing the data given the model (fit cost)
- Total: v_model + v_data ≤ R
- Quality: godWeight(R, v_model + v_data) = R - v_total + 1

Overfitting: v_model is large (complex model), v_data is small
  (fits training data perfectly), but total is LARGER than simpler model.
  The model memorized the training data instead of compressing it.

Underfitting: v_model is small (simple model), v_data is large
  (poor fit), total is suboptimal.

The optimal model minimizes v_model + v_data. This formalizes the God Formula:
find the v that maximizes godWeight(R, v) when v = complexity + residual.

Zero -- placeholder.
-/

namespace MinimumDescriptionLength

def godWeight (R v : Nat) : Nat := R - min v R + 1

/-- A model candidate: costs some bits to describe, explains some data. -/
structure ModelCandidate where
  budget : Nat           -- R: total bits available
  modelCost : Nat        -- bits to describe the model itself
  residualCost : Nat     -- bits to describe what the model doesn't explain
  totalBounded : modelCost + residualCost ≤ budget

def ModelCandidate.totalCost (m : ModelCandidate) : Nat := m.modelCost + m.residualCost
def ModelCandidate.quality (m : ModelCandidate) : Nat := godWeight m.budget m.totalCost

/-- THM-MDL-is-GODWEIGHT: The MDL quality of a model is its God Formula weight. -/
theorem mdl_is_godweight (m : ModelCandidate) :
    m.quality = m.budget - (m.modelCost + m.residualCost) + 1 := by
  unfold ModelCandidate.quality ModelCandidate.totalCost godWeight
  simp [Nat.min_eq_left m.totalBounded]; omega

/-- THM-OVERFITTING: A complex model (high modelCost) that memorizes
    training data (low residualCost) can have WORSE total cost than
    a simpler model. Concrete example: -/
theorem overfitting_example :
    -- Simple model: 5-bit description, 20-bit residual → total=25
    godWeight 100 25 = 76 ∧
    -- Complex model: 40-bit description, 10-bit residual → total=50
    godWeight 100 50 = 51 ∧
    -- Simple wins despite worse per-datum fit
    godWeight 100 25 > godWeight 100 50 := by
  unfold godWeight; omega

/-- THM-UNDERFITTING: A too-simple model has high residual cost. -/
theorem underfitting_example :
    -- Trivial model: 1-bit description, 80-bit residual → total=81
    godWeight 100 81 = 20 ∧
    -- Moderate model: 10-bit description, 30-bit residual → total=40
    godWeight 100 40 = 61 ∧
    -- Moderate wins
    godWeight 100 40 > godWeight 100 81 := by
  unfold godWeight; omega

/-- THM-OPTIMAL-MDL-TRADEOFF: The optimal model minimizes total cost.
    Lower total → higher weight. -/
theorem optimal_mdl (R total1 total2 : Nat) (h1 : total1 ≤ R) (h2 : total2 ≤ R)
    (hBetter : total1 ≤ total2) :
    godWeight R total2 ≤ godWeight R total1 := by
  unfold godWeight; simp [Nat.min_eq_left h1, Nat.min_eq_left h2]; omega

/-- THM-NULL-MODEL-CLINAMEN: The null model (0-bit description, R-bit
    residual) has quality 1. It explains nothing but always exists.
    The clinamen is the null model. -/
theorem null_model_clinamen (R : Nat) :
    godWeight R R = 1 := by unfold godWeight; omega

/-- THM-PERFECT-MODEL: A perfect model (total cost 0) has quality R+1.
    This is achievable only if the data formalizes the model (compression to
    a single description with zero residual). -/
theorem perfect_model (R : Nat) :
    godWeight R 0 = R + 1 := by unfold godWeight; omega

/-- THM-MDL-CONSERVATION: model_cost + residual_cost + quality - 1 = R.
    What you spend describing + what you gain understanding = budget. -/
theorem mdl_conservation (m : ModelCandidate) :
    m.quality + m.totalCost = m.budget + 1 := by
  unfold ModelCandidate.quality ModelCandidate.totalCost godWeight
  simp [Nat.min_eq_left m.totalBounded]; omega

/-- THM-OCCAMS-RAZOR: Among models that explain the data EQUALLY well
    (same residualCost), the simpler one (lower modelCost) is preferred.
    Occam's razor is a THEOREM, not a heuristic. -/
theorem occams_razor (R resid mc1 mc2 : Nat)
    (h1 : mc1 + resid ≤ R) (h2 : mc2 + resid ≤ R)
    (hSimpler : mc1 ≤ mc2) :
    godWeight R (mc2 + resid) ≤ godWeight R (mc1 + resid) := by
  unfold godWeight; simp [Nat.min_eq_left h1, Nat.min_eq_left h2]; omega

theorem mdl_master (R : Nat) :
    godWeight R 0 = R + 1 ∧ godWeight R R = 1 ∧
    (∀ v, godWeight R v ≥ 1) ∧
    (∀ v, v ≤ R → godWeight R v + v = R + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold godWeight; omega
  · unfold godWeight; omega
  · intro v; unfold godWeight; omega
  · intro v hv; unfold godWeight; simp [Nat.min_eq_left hv]; omega

end MinimumDescriptionLength
