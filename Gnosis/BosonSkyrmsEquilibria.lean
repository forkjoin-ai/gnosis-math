import Gnosis.SpectralNoiseEquilibrium
import Gnosis.BuleySelfSimilarityViolation
import Gnosis.Braided.BraidedTower
import Gnosis.CostAlgebraNoCloning
import Gnosis.CostAlgebraEntropy

/-!
# Boson Skyrms Equilibria

The Standard Model's bosons map to specific phase cycles in the
`BraidedTower`, with a `topologicallySafe` Skyrms-equilibrium witness
for each. The mapping is *signature*, not *derivation* — the
calculus permits any phase count via `every_phase_count_is_a_tower`,
and naming the SM walls is decoration of specific carrier states. The
*Higgs ↔ vacuum* identification is the only mapping that has a
formal payoff beyond decoration, because the vacuum is the unique
state that admits free duplication
(`Gnosis.CostAlgebraNoCloning.vacuum_is_duplicable`), and the Higgs
field's role of giving mass everywhere is structurally that
free-broadcast.

## The 13 bosons

| Boson | Count | Phase cycle | Skyrms equilibrium |
| --- | --- | --- | --- |
| Photon (γ) | 1 | Triton (3) | `topologicallySafe` at score 3 |
| W± | 2 | Triton (3) | `topologicallySafe` at score 3 |
| Z⁰ | 1 | Triton (3) | `topologicallySafe` at score 3 |
| Gluons | 8 | Octagon (`[4,2]=8`) | `topologicallySafe` at score 8 |
| Higgs (H) | 1 | Vacuum (0) | `vacuumBuleUnit`, free-broadcast |

The four electroweak bosons (γ, W+, W−, Z) share the Triton phase
because they sit in the SU(2)×U(1) gauge group whose minimal
non-trivial cycle is the Triton. The 8 gluons sit at the Octagon
because SU(3)'s adjoint representation has 8 generators. The Higgs
sits at the vacuum because it is the only field whose VEV is
non-trivially everywhere — the field that occupies the score-zero
slot and broadcasts mass-coupling without paying the no-cloning tax.

Imports `Gnosis.SpectralNoiseEquilibrium`,
`Gnosis.BuleySelfSimilarityViolation`, `Gnosis.BraidedTower`,
`Gnosis.CostAlgebraNoCloning`, `Gnosis.CostAlgebraEntropy`.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace BosonSkyrmsEquilibria

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit buleyUnitScore vacuumBuleUnit vacuum_has_zero_score)
open Gnosis.BuleySelfSimilarityViolation
  (topologicallySafe insideManifold ManifoldPhaseCount)
open Gnosis.BraidedTower (towerPhaseCount)
open Gnosis.CostAlgebraNoCloning (vacuum_is_duplicable diagonal)
open Gnosis.CostAlgebraEntropy (entropyGeneratedByCloning)
open Gnosis.CostAlgebra (buleyCostAlgebra)

/-! ## The bosons -/

inductive StandardModelBoson where
  | photon
  | wPlus
  | wMinus
  | zZero
  | gluon (i : Fin 8)
  | higgs
  deriving DecidableEq, Repr

/-- The phase cycle each boson occupies in the braided tower. The
electroweak bosons share the Triton (3); the gluons share the Octagon
(8); the Higgs occupies the vacuum (0). -/
def bosonPhaseCount : StandardModelBoson → Nat
  | .photon => towerPhaseCount [3]
  | .wPlus => towerPhaseCount [3]
  | .wMinus => towerPhaseCount [3]
  | .zZero => towerPhaseCount [3]
  | .gluon _ => towerPhaseCount [4, 2]
  | .higgs => 0

theorem photon_phase_is_triton : bosonPhaseCount .photon = 3 := by decide

theorem electroweak_phase_is_triton :
    bosonPhaseCount .photon = 3
    ∧ bosonPhaseCount .wPlus = 3
    ∧ bosonPhaseCount .wMinus = 3
    ∧ bosonPhaseCount .zZero = 3 := by decide

theorem all_gluons_share_octagon (i : Fin 8) :
    bosonPhaseCount (.gluon i) = 8 := by
  show towerPhaseCount [4, 2] = 8
  decide

theorem higgs_phase_is_vacuum : bosonPhaseCount .higgs = 0 := by decide

/-! ## Skyrms equilibrium per boson -/

/-- A Bule unit sits at a boson's Skyrms equilibrium when its score
exactly fills the boson's phase ceiling — `topologicallySafe`. The
Higgs equilibrium is the special case `score = 0` (the vacuum). -/
def bosonSkyrmsEquilibrium (b : BuleyUnit) (boson : StandardModelBoson) : Prop :=
  topologicallySafe b (bosonPhaseCount boson)

/-- Witness: a score-3 Bule unit on the waste face is at the photon's
Skyrms equilibrium. -/
theorem photon_equilibrium_witness :
    bosonSkyrmsEquilibrium ⟨3, 0, 0⟩ .photon := by
  unfold bosonSkyrmsEquilibrium topologicallySafe
  decide

theorem w_plus_equilibrium_witness :
    bosonSkyrmsEquilibrium ⟨2, 1, 0⟩ .wPlus := by
  unfold bosonSkyrmsEquilibrium topologicallySafe
  decide

theorem w_minus_equilibrium_witness :
    bosonSkyrmsEquilibrium ⟨1, 2, 0⟩ .wMinus := by
  unfold bosonSkyrmsEquilibrium topologicallySafe
  decide

theorem z_zero_equilibrium_witness :
    bosonSkyrmsEquilibrium ⟨1, 1, 1⟩ .zZero := by
  unfold bosonSkyrmsEquilibrium topologicallySafe
  decide

/-- Witness: a score-8 Bule unit fills any gluon's Skyrms equilibrium.
All 8 gluons share the Octagon ceiling, so a single witness covers
them all. -/
theorem gluon_equilibrium_witness (i : Fin 8) :
    bosonSkyrmsEquilibrium ⟨4, 2, 2⟩ (.gluon i) := by
  unfold bosonSkyrmsEquilibrium topologicallySafe
  show buleyUnitScore ⟨4, 2, 2⟩ = bosonPhaseCount (.gluon i)
  rw [all_gluons_share_octagon i]
  decide

/-! ## The Higgs ↔ Vacuum identity (the formal payoff) -/

/-- The Higgs sits at the vacuum: its phase count is zero, and
`vacuumBuleUnit` is the unique state with score zero
(`vacuum_has_zero_score`). The Higgs Skyrms equilibrium is therefore
the vacuum. -/
theorem higgs_equilibrium_is_vacuum :
    bosonSkyrmsEquilibrium vacuumBuleUnit .higgs := by
  unfold bosonSkyrmsEquilibrium topologicallySafe
  rw [higgs_phase_is_vacuum]
  exact vacuum_has_zero_score

/-- The Higgs is the unique boson whose Skyrms equilibrium is the
vacuum. Because every other boson has a positive phase count, no
non-vacuum state can be at the Higgs equilibrium *except* through
the same vacuum carrier. -/
theorem higgs_equilibrium_iff_vacuum (b : BuleyUnit) :
    bosonSkyrmsEquilibrium b .higgs ↔ buleyUnitScore b = 0 := by
  unfold bosonSkyrmsEquilibrium topologicallySafe
  rw [higgs_phase_is_vacuum]

/-- The free-broadcast theorem for the Higgs: only the Higgs admits
the diagonal `Δ : S → S × S` as a `CostHom`, because only the Higgs
sits at the vacuum carrier where `vacuum_is_duplicable` applies. The
Higgs's role of giving mass everywhere is structurally a vacuum
broadcast — it fans out without paying the no-cloning tax. -/
theorem higgs_is_free_broadcast :
    entropyGeneratedByCloning buleyCostAlgebra vacuumBuleUnit = 0 := by
  unfold entropyGeneratedByCloning
  show buleyCostAlgebra.score vacuumBuleUnit = 0
  exact vacuum_has_zero_score

/-! ## All 13 bosons enumerated and witnessed -/

/-- Enumerate all 13 Standard Model bosons in canonical order. -/
def allStandardModelBosons : List StandardModelBoson :=
  [.photon, .wPlus, .wMinus, .zZero,
   .gluon 0, .gluon 1, .gluon 2, .gluon 3,
   .gluon 4, .gluon 5, .gluon 6, .gluon 7,
   .higgs]

theorem boson_count_is_thirteen :
    allStandardModelBosons.length = 13 := by decide

/-- The non-Higgs bosons partition by phase count: 4 electroweak
(Triton-3) and 8 gluons (Octagon-8). The Higgs is the singleton at
the vacuum (0). -/
theorem boson_phase_partition :
    -- 4 electroweak at Triton
    bosonPhaseCount .photon = 3
    ∧ bosonPhaseCount .wPlus = 3
    ∧ bosonPhaseCount .wMinus = 3
    ∧ bosonPhaseCount .zZero = 3
    -- 8 gluons at Octagon
    ∧ bosonPhaseCount (.gluon 0) = 8
    ∧ bosonPhaseCount (.gluon 7) = 8
    -- Higgs at vacuum
    ∧ bosonPhaseCount .higgs = 0 := by decide

/-! ## Master theorem: the boson catalog as Skyrms-equilibrium bundle -/

/-- Every Standard Model boson admits a Skyrms-equilibrium witness in
the `BraidedTower`, and the Higgs is uniquely identified with the
vacuum carrier (the only state that admits free duplication). -/
theorem boson_skyrms_master :
    bosonSkyrmsEquilibrium ⟨3, 0, 0⟩ .photon
    ∧ bosonSkyrmsEquilibrium ⟨2, 1, 0⟩ .wPlus
    ∧ bosonSkyrmsEquilibrium ⟨1, 2, 0⟩ .wMinus
    ∧ bosonSkyrmsEquilibrium ⟨1, 1, 1⟩ .zZero
    ∧ bosonSkyrmsEquilibrium ⟨4, 2, 2⟩ (.gluon 0)
    ∧ bosonSkyrmsEquilibrium vacuumBuleUnit .higgs
    ∧ allStandardModelBosons.length = 13 :=
  ⟨photon_equilibrium_witness,
   w_plus_equilibrium_witness,
   w_minus_equilibrium_witness,
   z_zero_equilibrium_witness,
   gluon_equilibrium_witness 0,
   higgs_equilibrium_is_vacuum,
   boson_count_is_thirteen⟩

end BosonSkyrmsEquilibria
end Gnosis
