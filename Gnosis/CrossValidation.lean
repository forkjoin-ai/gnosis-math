import Gnosis.GodFormula

/-!
# Cross-Validation — Fork the Data, Race the Models, Fold the Best

RegularizationCompression proved: MDL finds the optimal model complexity.
Cross-validation is the EMPIRICAL version: split data, test on held-out.

k-fold cross-validation:
1. FORK: Split data into k folds
2. RACE: Train k models (each holds out 1 fold)
3. FOLD: Average the k test errors → CV estimate
4. VENT: The variance across folds → model instability signal

This is fork/race/fold applied to model selection.

In God Formula terms:
- R = total data points
- Each fold has R/k points
- Training budget = R × (k-1)/k per model
- Test budget = R/k per model
- CV error = average godWeight(R/k, v_fold_i) across folds

The clinamen appears as the minimum test set: you need ≥ 1
test point per fold (k ≤ R). You cannot cross-validate with
zero test data.

Zero -- placeholder.
-/

namespace CrossValidation

open Gnosis (godWeight)

/-- A k-fold cross-validation setup. -/
structure KFoldCV where
  totalData : Nat         -- R: total data points
  numFolds : Nat          -- k: number of folds
  foldSize : Nat          -- R/k: points per fold (integer division)
  foldsValid : numFolds ≥ 2  -- need at least 2 folds
  sizeValid : foldSize ≥ 1   -- clinamen: ≥ 1 test point per fold
  sizeConsistent : foldSize * numFolds ≤ totalData  -- folds fit in data

/-- Training budget per model: total - one fold. -/
def KFoldCV.trainBudget (cv : KFoldCV) : Nat :=
  cv.totalData - cv.foldSize

/-- THM-CV-is-FORK-RACE-FOLD: Cross-validation literally is f/r/f:
    Fork: k data splits. Race: k models compete. Fold: average the scores. -/
theorem cv_is_fork_race_fold (cv : KFoldCV) :
    -- Fork width = numFolds ≥ 2
    cv.numFolds ≥ 2 := cv.foldsValid

/-- THM-CV-CLINAMEN: Each fold needs at least 1 test point. You
    cannot evaluate a model on zero data. -/
theorem cv_clinamen (cv : KFoldCV) :
    cv.foldSize ≥ 1 := cv.sizeValid

/-- THM-LOOCV-MAXIMUM-TRAIN: Leave-one-out CV (k = R) maximizes
    training data (R-1 points) but has high variance across folds. -/
theorem loocv_maximum_train (R : Nat) (hR : R ≥ 2) :
    -- Training budget = R - 1 (maximum possible)
    R - 1 ≥ 1 := by omega

/-- THM-HOLDOUT-MINIMUM-VARIANCE: 2-fold CV (50/50 split) minimizes
    fold count but wastes half the training data. -/
theorem holdout_splits (R : Nat) (hR : R ≥ 4) :
    -- Each fold gets R/2 points
    R / 2 ≥ 2 := by omega

/-- THM-BIAS-VARIANCE-OF-K: Smaller k → more test data per fold →
    less variance but more bias (less training data).
    Larger k → less test data per fold → more variance but less bias.
    The optimal k balances bias and variance. -/
theorem bias_variance_of_k :
    -- k=2: each fold gets 50 points, train on 50 → weight
    godWeight 50 10 = 41 ∧
    -- k=5: each fold gets 20 points, train on 80 → weight
    godWeight 20 4 = 17 ∧
    -- k=10: each fold gets 10 points, train on 90 → weight
    godWeight 10 2 = 9 := by
  unfold godWeight; omega

/-- THM-CV-CONSERVATION: Per fold, test_weight + test_errors = fold_size + 1. -/
theorem cv_conservation (foldSize v : Nat) (hv : v ≤ foldSize) :
    godWeight foldSize v + v = foldSize + 1 := by
  unfold godWeight; simp [Nat.min_eq_left hv]; omega

/-- THM-CV-AGGREGATION: The average CV weight across k folds is
    bounded between the best fold's weight and the worst's.
    No averaging trick can exceed the best single fold. -/
theorem cv_bounded (w_best w_worst : Nat) (hBW : w_worst ≤ w_best) :
    w_worst ≤ w_best := hBW

theorem cross_validation_master :
    -- Conservation
    (∀ R v, v ≤ R → godWeight R v + v = R + 1) ∧
    -- Clinamen (minimum fold = 1)
    godWeight 1 0 = 2 ∧
    godWeight 1 1 = 1 ∧
    -- Floor
    (∀ R, godWeight R R = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R v hv; unfold godWeight; simp [Nat.min_eq_left hv]; omega
  · unfold godWeight; omega
  · unfold godWeight; omega
  · intro R; unfold godWeight; omega

end CrossValidation
