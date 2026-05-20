import Init
import Gnosis.FanoIncidence
import Gnosis.AmplituhedronGrassmannian
import Gnosis.AeonStandingWaveCoordinateBridge

/-!
# Fano incidence inside the `Gr(2,12)` mesh

This module embeds the seven Fano points into the first seven columns of the
Aeon-12 carrier and reads every distinct Fano pair as a valid `Gr(2,12)`
Plucker gate. The incidence completion theorem then gives the structured third
point associated with a pair collision.
-/

namespace Gnosis
namespace FanoGrassmannianMesh

open Gnosis.FanoIncidence
open AmplituhedronAttention.Grassmannian

/-- Embed the seven Fano points into the first seven Aeon-12 columns. -/
def fanoColumn (p : FanoPoint) : Nat :=
  pointIndex p

theorem fanoColumn_lt_twelve (p : FanoPoint) : fanoColumn p < 12 := by
  have h7 : fanoColumn p < 7 := pointIndex_lt_seven p
  exact Nat.lt_trans h7 (by decide)

/-- Sorted two-column Plucker gate associated with a Fano pair. -/
def fanoPairGate (a b : FanoPoint) : List Nat :=
  let i := fanoColumn a
  let j := fanoColumn b
  if i < j then [i, j] else [j, i]

theorem fanoPairGate_length (a b : FanoPoint) :
    (fanoPairGate a b).length = 2 := by
  unfold fanoPairGate
  by_cases h : fanoColumn a < fanoColumn b <;> simp [h]

theorem fanoPairGate_mem_gr_2_12 (a b : FanoPoint) (hab : a ≠ b) :
    fanoPairGate a b ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim := by
  cases a <;> cases b <;>
    simp [fanoPairGate, fanoColumn, pointIndex, Gnosis.AeonStandingWaveCoordinateBridge.ambientDim,
      Gnosis.Circadian.aeon, kSubsets] at hab ⊢

/-- Pair-collision bridge: a distinct Fano pair gives a valid `Gr(2,12)`
pair gate plus the unique Fano incidence completion. -/
theorem fano_collision_has_grassmannian_gate_and_completion
    (a b : FanoPoint) (hab : a ≠ b) :
    fanoPairGate a b ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim ∧
    ∃ c,
      c ≠ a ∧ c ≠ b ∧ fanoLine a b c ∧
        ∀ d, d ≠ a → d ≠ b → fanoLine a b d → d = c := by
  exact ⟨fanoPairGate_mem_gr_2_12 a b hab, distinct_pair_has_unique_completion a b hab⟩

/-- The concrete birthday-problem-sized Fano atlas has `C(7,2) = 21` distinct
pair gates before embedding into the 66-gate Aeon-12 Plucker stack. -/
theorem fano_pair_gate_budget_twenty_one :
    (kSubsets 2 7).length = 21 := by
  native_decide

/-- The ambient Aeon mesh still exposes the existing 66 `Gr(2,12)` pair labels. -/
theorem aeon_pair_gate_budget_sixty_six :
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 := by
  exact Gnosis.AeonStandingWaveCoordinateBridge.vertexCount_2_ambientDim_eq_sixty_six

end FanoGrassmannianMesh
end Gnosis
