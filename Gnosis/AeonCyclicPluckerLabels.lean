import Init
import Gnosis.CircadianGnosisAlignment
import Gnosis.DiscreteClosedTimelikeStep
import Gnosis.AmplituhedronGrassmannian

namespace Gnosis.AeonCyclicPluckerLabels

/-!
# Cyclic column action on aeon Plücker labels

The **ambient** index line is **`Circadian.aeon = 12`**.  A **clock step** on column
indices is **`cyclicSucc`** from `DiscreteClosedTimelikeStep` — a generator of **C₁₂**
acting on **`Fin 12`**.

Iteration and **`n`‑fold period** reuse the closed-timelike-step lemmas (`iteratedCyclicSucc`),
not continuum geometry.

This module ties that dynamics to **ordered 2-subsets** `kSubsets 2 12` — the **66** Plücker
labels aligned with `vertexCount 2 12` / `AeonStandingWaveCoordinateBridge`.
-/

open AmplituhedronAttention.Grassmannian
open Gnosis.DiscreteClosedTimelikeStep

/-- Match circadian aeon (`AeonStandingWaveCoordinateBridge.ambientDim`). -/
def ambientDim : Nat :=
  Circadian.aeon

theorem ambientDim_pos : 0 < ambientDim :=
  Nat.succ_pos _

abbrev aeonCyclicSucc : Fin ambientDim → Fin ambientDim :=
  cyclicSucc ambientDim_pos

/-- **12** ticks close the discrete column clock (`DiscreteClosedTimelikeStep`). -/
theorem aeonCyclicSucc_period (x : Fin ambientDim) :
    iteratedCyclicSucc ambientDim_pos ambientDim x = x :=
  iteratedCyclicSucc_period ambientDim_pos x

/-- Raw mod step on **`Nat`** column indices (reduced mod **12**). -/
def rotateIndex (j : Nat) : Nat :=
  (j + 1) % ambientDim

/-- Act on one **ordered Plücker label** (list of column indices). -/
def rotatePluckerLabel (s : List Nat) : List Nat :=
  s.map rotateIndex

theorem rotatePluckerLabel_length (s : List Nat) :
    (rotatePluckerLabel s).length = s.length := by
  unfold rotatePluckerLabel
  rw [List.length_map]

/-- Ordered **2**-subsets of **`[0..12)`** from `kSubsets`. -/
def pluckerTwoSubsetsAeon : List (List Nat) :=
  kSubsets 2 ambientDim

theorem pluckerTwoSubsetsAeon_length_sixty_six : pluckerTwoSubsetsAeon.length = 66 := by
  native_decide

theorem kSubsets_2_twelve_length : (kSubsets 2 12).length = 66 := by
  native_decide

theorem pluckerTwoSubsets_eq_kSubsets_twelve : pluckerTwoSubsetsAeon = kSubsets 2 12 := by
  unfold pluckerTwoSubsetsAeon ambientDim Circadian.aeon
  rfl

/-- Rotate every label row in a stack (global column clock). -/
def rotateAllPluckerLabels (ss : List (List Nat)) : List (List Nat) :=
  ss.map rotatePluckerLabel

theorem rotateAll_length (ss : List (List Nat)) :
    (rotateAllPluckerLabels ss).length = ss.length := by
  unfold rotateAllPluckerLabels
  rw [List.length_map]

theorem rotateAll_plucker_two_preserves_count :
    (rotateAllPluckerLabels pluckerTwoSubsetsAeon).length = 66 := by
  rw [rotateAll_length, pluckerTwoSubsetsAeon_length_sixty_six]

/-- **Bundle:** **C₁₂** period on **`Fin 12`**, **66** labels, same count after list rotation. -/
theorem aeon_cyclic_plucker_label_bundle :
    (∀ x : Fin ambientDim, iteratedCyclicSucc ambientDim_pos ambientDim x = x)
    ∧ pluckerTwoSubsetsAeon.length = 66
    ∧ (rotateAllPluckerLabels pluckerTwoSubsetsAeon).length = 66 :=
  ⟨fun x => iteratedCyclicSucc_period ambientDim_pos x, pluckerTwoSubsetsAeon_length_sixty_six,
    rotateAll_plucker_two_preserves_count⟩

end Gnosis.AeonCyclicPluckerLabels
