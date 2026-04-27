import Gnosis.SpectralNoiseEquilibrium
import Gnosis.BraidedInfinity

/-!
# Buley Clinamen Braid

Bridges the Bule unit's three faces (`waste`, `opportunity`, `diversity`)
to the braided-infinity cycle structure of `Gnosis.BraidedInfinity`.

The Bule clinamen lift is a `+1` step on a chosen face. When the face
choice itself is cycled — waste → opportunity → diversity → waste — the
sequence is exactly a `BraidedAsymptote` of `phaseCount = 3`.

This module proves:

* the three Bule faces form a phase-3 directed cycle under successor;
* iterating the cycle three times returns to the starting face;
* a partial iteration of length `1` or `2` does not return;
* the canonical Bule braid is a concrete `BraidedAsymptote` instance.

Together with `clinamen_lift_residue_is_universal_plus_one`, this anchors
the Bule clinamen as the same `+1` perturbation that generates the
braided infinity, not a separate object that merely resembles it.

Imports both `Gnosis.SpectralNoiseEquilibrium` and `Gnosis.BraidedInfinity`.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace BuleyClinamenBraid

open Gnosis.SpectralNoiseEquilibrium (BuleyFace)
open Gnosis.BraidedInfinity (BraidedAsymptote iterateSucc)

/-! ## The three-face cycle on `BuleyFace` -/

/-- The successor on Bule faces: the directed cycle
waste → opportunity → diversity → waste. -/
def faceSucc : BuleyFace → BuleyFace
  | .waste => .opportunity
  | .opportunity => .diversity
  | .diversity => .waste

/-- Iterate the face successor `n` times starting from `f`. -/
def iterateFaceSucc : Nat → BuleyFace → BuleyFace
  | 0, f => f
  | n + 1, f => iterateFaceSucc n (faceSucc f)

theorem face_three_iterations_return_waste :
    iterateFaceSucc 3 .waste = .waste := by decide

theorem face_three_iterations_return_opportunity :
    iterateFaceSucc 3 .opportunity = .opportunity := by decide

theorem face_three_iterations_return_diversity :
    iterateFaceSucc 3 .diversity = .diversity := by decide

theorem face_one_iteration_does_not_return :
    iterateFaceSucc 1 .waste ≠ .waste
    ∧ iterateFaceSucc 1 .opportunity ≠ .opportunity
    ∧ iterateFaceSucc 1 .diversity ≠ .diversity := by decide

theorem face_two_iterations_do_not_return :
    iterateFaceSucc 2 .waste ≠ .waste
    ∧ iterateFaceSucc 2 .opportunity ≠ .opportunity
    ∧ iterateFaceSucc 2 .diversity ≠ .diversity := by decide

/-! ## The canonical `BraidedAsymptote` instance for the Bule lattice -/

def buleyFaceBraid : BraidedAsymptote :=
  { phaseCount := 3
    descriptors := ["waste", "opportunity", "diversity"] }

theorem buleyFaceBraid_phase_count : buleyFaceBraid.phaseCount = 3 := rfl

theorem buleyFaceBraid_returns :
    iterateSucc buleyFaceBraid.phaseCount 3 0 = 0
    ∧ iterateSucc buleyFaceBraid.phaseCount 3 1 = 1
    ∧ iterateSucc buleyFaceBraid.phaseCount 3 2 = 2 := by decide

theorem buleyFaceBraid_partial_does_not_return :
    iterateSucc buleyFaceBraid.phaseCount 1 0 ≠ 0
    ∧ iterateSucc buleyFaceBraid.phaseCount 2 0 ≠ 0 := by decide

/-! ## Bridge: face cycle as `Fin 3` index, agrees with `iterateSucc` -/

/-- Index a Bule face into `[0, 3)` so the cycle on `BuleyFace` lines up
with the cycle on natural-number residues used by `BraidedInfinity`. -/
def faceIndex : BuleyFace → Nat
  | .waste => 0
  | .opportunity => 1
  | .diversity => 2

theorem face_succ_advances_index_mod_three (f : BuleyFace) :
    faceIndex (faceSucc f) = (faceIndex f + 1) % 3 := by
  cases f <;> rfl

theorem buleyFaceBraid_succ_matches_face_succ (f : BuleyFace) :
    iterateSucc buleyFaceBraid.phaseCount 1 (faceIndex f) = faceIndex (faceSucc f) := by
  cases f <;> decide

/-- The Bule face cycle and the `BraidedAsymptote` successor agree on three
iterations: starting from any face, advancing the face cycle three steps and
indexing recovers the same `Nat` as advancing the braided-asymptote cycle
three steps from that face's index. -/
theorem face_three_step_matches_braided_three_step (f : BuleyFace) :
    iterateSucc buleyFaceBraid.phaseCount 3 (faceIndex f)
      = faceIndex (iterateFaceSucc 3 f) := by
  cases f <;> decide

end BuleyClinamenBraid
end Gnosis
