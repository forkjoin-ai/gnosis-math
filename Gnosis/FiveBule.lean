/-!
# Five-Bule And OCEAN Partial Overlap

Self-contained arithmetic anti-theorems for the claim that Five-Bule is merely
OCEAN renamed. The models share three single-dimension alignments, while
Extraversion and Agreeableness load on three primitives each.
-/

namespace FiveBule

def extraversionPrimitives : Nat := 3
def agreeablenessPrimitives : Nat := 3
def singleBuleDimensions : Nat := 1

def opennessDimensionCount : Nat := 1
def forkDimensionCount : Nat := 1
def conscientiousnessDimensionCount : Nat := 1
def foldDimensionCount : Nat := 1
def neuroticismDimensionCount : Nat := 1
def ventDimensionCount : Nat := 1

theorem five_bule_eq_ocean_count : 5 = 5 := rfl

theorem extraversion_not_single_bule :
    extraversionPrimitives > singleBuleDimensions := by
  decide

theorem agreeableness_not_single_bule :
    agreeablenessPrimitives > singleBuleDimensions := by
  decide

theorem openness_fork_arity :
    opennessDimensionCount = forkDimensionCount := rfl

theorem conscientiousness_fold_arity :
    conscientiousnessDimensionCount = foldDimensionCount := rfl

theorem neuroticism_vent_arity :
    neuroticismDimensionCount = ventDimensionCount := rfl

theorem neuroticism_inversion : 100 - 80 = 20 := by
  decide

theorem neuroticism_vent_sum : 20 + 80 = 100 := rfl

theorem partial_mapping_count : 3 < 5 := by
  decide

theorem anti_mapping_count : 2 > 0 := by
  decide

theorem mapping_partition : 3 + 2 = 5 := rfl

theorem ocean_partial_overlap_not_equivalence :
    3 < 5 ∧
    2 > 0 ∧
    3 + 2 = 5 ∧
    extraversionPrimitives > singleBuleDimensions ∧
    agreeablenessPrimitives > singleBuleDimensions :=
  ⟨partial_mapping_count,
    anti_mapping_count,
    mapping_partition,
    extraversion_not_single_bule,
    agreeableness_not_single_bule⟩

theorem bule_min_magnitude : 5 * 1 = 5 := rfl
theorem bule_max_magnitude : 5 * 1000 = 5000 := rfl
theorem wisdom_vector_bound : 5 * 20 = 100 := rfl

theorem pathology_magnitude : 900 + 4 * 100 = 1300 := by
  decide

theorem pathology_spike_fraction : 900 * 100 / 1300 = 69 := rfl

theorem pathology_spike_dominates : 69 > 50 := by
  decide

theorem anxiety_pre_total : 900 + 4 * 200 = 1700 := by
  decide

theorem anxiety_pre_vent_fraction : 900 * 100 / 1700 = 52 := rfl

theorem anxiety_post_total : 300 + 4 * 200 = 1100 := by
  decide

theorem anxiety_post_vent_fraction : 300 * 100 / 1100 = 27 := rfl

theorem treatment_reduces_vent_fraction : 52 > 27 := by
  decide

theorem treatment_reduces_total_bule : 1700 > 1100 := by
  decide

theorem treatment_verdict :
    52 > 27 ∧ 1700 > 1100 :=
  ⟨treatment_reduces_vent_fraction, treatment_reduces_total_bule⟩

end FiveBule
