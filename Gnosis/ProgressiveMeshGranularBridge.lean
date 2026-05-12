import Init

/-!
# Progressive Mesh / Granular Bridge

Finite contracts for the progressive mesh orchestrator rows that used to live
under the historical `ForkRaceFoldTheorems.ProgressiveMeshGranularBridge`
namespace.
-/

namespace ForkRaceFoldTheorems
namespace ProgressiveMeshGranularBridge

inductive MeshBranchDim where
  | trunk
  | branchD1
  | branchD2
  | branchD3
deriving DecidableEq, Repr

def meshBranchDimToFin4 : MeshBranchDim → Fin 4
  | MeshBranchDim.trunk => ⟨0, by decide⟩
  | MeshBranchDim.branchD1 => ⟨1, by decide⟩
  | MeshBranchDim.branchD2 => ⟨2, by decide⟩
  | MeshBranchDim.branchD3 => ⟨3, by decide⟩

def fin4ToMeshBranchDim : Fin 4 → MeshBranchDim
  | ⟨0, _⟩ => MeshBranchDim.trunk
  | ⟨1, _⟩ => MeshBranchDim.branchD1
  | ⟨2, _⟩ => MeshBranchDim.branchD2
  | _ => MeshBranchDim.branchD3

theorem meshBranchDimEquivFin4_left_inverse
    (dim : MeshBranchDim) :
    fin4ToMeshBranchDim (meshBranchDimToFin4 dim) = dim := by
  cases dim <;> rfl

theorem meshBranchDimEquivFin4
    (dim : MeshBranchDim) :
    fin4ToMeshBranchDim (meshBranchDimToFin4 dim) = dim :=
  meshBranchDimEquivFin4_left_inverse dim

structure MeshThresholdConfig where
  d1 : Nat
  d2 : Nat
  d3 : Nat
deriving Repr

structure MeshBranchAvailability where
  d1 : Bool
  d2 : Bool
  d3 : Bool
deriving Repr

def activeFlag (rev threshold : Nat) (available : Bool) : Nat :=
  if available then
    if threshold ≤ rev then 1 else 0
  else
    0

def meshChooseActiveLength
    (thresholds : MeshThresholdConfig) (availability : MeshBranchAvailability)
    (rev : Nat) : Nat :=
  1
    + activeFlag rev thresholds.d1 availability.d1
    + activeFlag rev thresholds.d2 availability.d2
    + activeFlag rev thresholds.d3 availability.d3

theorem active_flag_monotone
    (rev rev' threshold : Nat) (available : Bool)
    (hRev : rev ≤ rev') :
    activeFlag rev threshold available ≤ activeFlag rev' threshold available := by
  unfold activeFlag
  cases available <;> simp
  by_cases h : threshold ≤ rev
  · have h' : threshold ≤ rev' := Nat.le_trans h hRev
    simp [h, h']
  · by_cases h' : threshold ≤ rev'
    · simp [h, h']
    · simp [h, h']

theorem mesh_choose_active_length_monotone
    (thresholds : MeshThresholdConfig) (availability : MeshBranchAvailability)
    (rev rev' : Nat)
    (hRev : rev ≤ rev') :
    meshChooseActiveLength thresholds availability rev ≤
      meshChooseActiveLength thresholds availability rev' := by
  unfold meshChooseActiveLength
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add (Nat.le_refl 1)
        (active_flag_monotone rev rev' thresholds.d1 availability.d1 hRev))
      (active_flag_monotone rev rev' thresholds.d2 availability.d2 hRev))
    (active_flag_monotone rev rev' thresholds.d3 availability.d3 hRev)

theorem mesh_choose_active_length_eq
    (thresholds : MeshThresholdConfig) (availability : MeshBranchAvailability)
    (rev : Nat) :
    meshChooseActiveLength thresholds availability rev =
      1
        + activeFlag rev thresholds.d1 availability.d1
        + activeFlag rev thresholds.d2 availability.d2
        + activeFlag rev thresholds.d3 availability.d3 := by
  rfl

def branchLogit (prior penalty cost : Nat) : Nat :=
  prior - penalty * cost

theorem mesh_orchestrator_logit_antitone_in_cost
    (prior penalty cost₁ cost₂ : Nat)
    (hCost : cost₁ ≤ cost₂) :
    branchLogit prior penalty cost₂ ≤ branchLogit prior penalty cost₁ := by
  unfold branchLogit
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_left penalty hCost) prior

structure Column4 where
  marshmallows : Nat
  stratScore : Nat
  hCap : stratScore ≤ 4 * marshmallows
deriving Repr

structure ShakeStep where
  before : Nat
  after : Nat
  hMonotone : before ≤ after
deriving Repr

theorem granular_stratScore_monotone_along_shake
    (step : ShakeStep) :
    step.before ≤ step.after :=
  step.hMonotone

theorem granular_stratScore_le_combinatorial_cap
    (column : Column4) :
    column.stratScore ≤ 4 * column.marshmallows :=
  column.hCap

end ProgressiveMeshGranularBridge
end ForkRaceFoldTheorems
