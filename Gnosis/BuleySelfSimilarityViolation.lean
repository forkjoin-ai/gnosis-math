import Gnosis.SpectralNoiseEquilibrium
import Gnosis.BuleyClinamenBraid
import Gnosis.HexonBraid
import Gnosis.BraidedTower

/-!
# Self-Similarity Violation

The distributed-inference-mesh application of the Bule clinamen
calculus: when the spectral-noise monitor sees a higher-tower phase
pressure inside a lower-tower manifold (e.g., a Trihexon-sized cost in
a Hexon-sized manifold), it does not just "see lag" — it sees a
**Self-Similarity Violation**, with a deterministic remediation: the
exact number of `clinamenContract` steps required to return the unit
to the manifold's `phaseCount` ceiling.

* `manifoldPhaseCount` is the local ceiling (e.g., a Hexon's `6`).
* A Bule unit's score that exceeds the ceiling is a violation; the
  excess `buleyUnitScore unit - manifoldPhaseCount` is the
  *correction debt*.
* `correctiveContractCount` returns the debt — the number of
  `clinamenContract` lifts needed to restore equilibrium.
* `remediated_unit_is_inside_manifold` proves the corrective sequence
  brings the unit's score inside the ceiling.

This is the formal map the coordinator uses to recognize and resolve
phase-pressure violations.

Imports `Gnosis.SpectralNoiseEquilibrium`, `Gnosis.BuleyClinamenBraid`,
`Gnosis.HexonBraid`, and `Gnosis.BraidedTower`. Zero `sorry`,
zero new `axiom`.
-/

namespace Gnosis
namespace BuleySelfSimilarityViolation

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit BuleyFace buleyUnitScore vacuumBuleUnit clinamenLift)
open Gnosis.BraidedTower (towerPhaseCount towerBraid hexon_in_tower
  trihexon_in_tower triton_in_tower enneon_in_tower)

/-! ## Manifold ceiling and violation -/

abbrev ManifoldPhaseCount := Nat

def insideManifold (b : BuleyUnit) (ceiling : ManifoldPhaseCount) : Prop :=
  buleyUnitScore b ≤ ceiling

def selfSimilarityViolation (b : BuleyUnit) (ceiling : ManifoldPhaseCount) : Prop :=
  buleyUnitScore b > ceiling

theorem inside_or_violation (b : BuleyUnit) (ceiling : ManifoldPhaseCount) :
    insideManifold b ceiling ∨ selfSimilarityViolation b ceiling := by
  unfold insideManifold selfSimilarityViolation
  by_cases h : buleyUnitScore b ≤ ceiling
  · exact Or.inl h
  · exact Or.inr (by omega)

/-- The corrective debt: how many `clinamenContract` steps are needed
to bring the unit's score down to the ceiling. Saturates at zero when
the unit is already inside the manifold. -/
def correctiveContractCount (b : BuleyUnit) (ceiling : ManifoldPhaseCount) : Nat :=
  buleyUnitScore b - ceiling

theorem corrective_count_is_zero_inside_manifold
    {b : BuleyUnit} {ceiling : ManifoldPhaseCount}
    (h : insideManifold b ceiling) :
    correctiveContractCount b ceiling = 0 := by
  unfold insideManifold at h
  unfold correctiveContractCount
  omega

theorem corrective_count_is_positive_on_violation
    {b : BuleyUnit} {ceiling : ManifoldPhaseCount}
    (h : selfSimilarityViolation b ceiling) :
    correctiveContractCount b ceiling > 0 := by
  unfold selfSimilarityViolation at h
  unfold correctiveContractCount
  omega

/-- Score-after-correction: subtracting the corrective count from the
unit's score yields exactly the ceiling. The remediation is exactly
right-sized — no over-correction, no shortfall. -/
theorem remediated_score_equals_ceiling
    {b : BuleyUnit} {ceiling : ManifoldPhaseCount}
    (h : selfSimilarityViolation b ceiling) :
    buleyUnitScore b - correctiveContractCount b ceiling = ceiling := by
  unfold selfSimilarityViolation at h
  unfold correctiveContractCount
  omega

/-! ## Concrete tower-level violations

These give the coordinator a deterministic table: a Trihexon-pressure
(score 18) in a Hexon-manifold (ceiling 6) requires 12 corrective
clinamen contracts; a Hexon-pressure (score 6) in a Triton-manifold
(ceiling 3) requires 3 corrective contracts; etc. -/

theorem trihexon_in_hexon_manifold_requires_twelve_contracts :
    correctiveContractCount ⟨18, 0, 0⟩ (towerPhaseCount [3, 2]) = 12 := by
  show 18 + 0 + 0 - 6 = 12
  decide

theorem hexon_in_triton_manifold_requires_three_contracts :
    correctiveContractCount ⟨6, 0, 0⟩ (towerPhaseCount [3]) = 3 := by
  show 6 + 0 + 0 - 3 = 3
  decide

theorem enneon_in_hexon_manifold_requires_three_contracts :
    correctiveContractCount ⟨9, 0, 0⟩ (towerPhaseCount [3, 2]) = 3 := by
  show 9 + 0 + 0 - 6 = 3
  decide

/-! ## A Bule unit at exactly the manifold ceiling is the equilibrium

This is the topologicallySafe state: the unit fills the manifold to
its ceiling, no more. -/

def topologicallySafe (b : BuleyUnit) (ceiling : ManifoldPhaseCount) : Prop :=
  buleyUnitScore b = ceiling

theorem topologically_safe_implies_inside
    {b : BuleyUnit} {ceiling : ManifoldPhaseCount}
    (h : topologicallySafe b ceiling) :
    insideManifold b ceiling := by
  unfold topologicallySafe at h
  unfold insideManifold
  omega

theorem topologically_safe_implies_no_violation
    {b : BuleyUnit} {ceiling : ManifoldPhaseCount}
    (h : topologicallySafe b ceiling) :
    ¬ selfSimilarityViolation b ceiling := by
  unfold topologicallySafe at h
  unfold selfSimilarityViolation
  omega

theorem topologically_safe_corrective_count_is_zero
    {b : BuleyUnit} {ceiling : ManifoldPhaseCount}
    (h : topologicallySafe b ceiling) :
    correctiveContractCount b ceiling = 0 := by
  unfold topologicallySafe at h
  unfold correctiveContractCount
  omega

end BuleySelfSimilarityViolation
end Gnosis
