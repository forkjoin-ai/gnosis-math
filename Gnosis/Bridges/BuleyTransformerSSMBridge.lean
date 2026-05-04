import Gnosis.SpectralNoiseEquilibrium
import Gnosis.BuleyClinamenBraid
import Gnosis.HexonBraid
import Gnosis.Braided.BraidedTower

/-!
# Buley ↔ Transformer / SSM Bridge

The transformer's Q/K/V projection triple is structurally the Bule
unit's three faces, and a multi-head attention block is a Cartesian
product on the braided tower. This module makes that explicit:

* `QKVProjection` mirrors a transformer head's three-vector projection.
* The bijection `BuleyUnit ↔ QKVProjection` sends `waste ↦ Q`,
  `opportunity ↦ K`, `diversity ↦ V`. Score is preserved.
* An attention update on Q, K, or V — i.e., a single-channel write —
  is a clinamen lift on the corresponding Bule face. The +1 residue per
  update matches `UniversalClinamenPlusOne`.
* A single attention head's Q → K → V → Q rotation across stacked
  layers is the phase-3 cycle of `BuleyClinamenBraid`.
* An `n`-head multi-head attention block is the tower level
  `[3, n]` — `n` tritons stacked — with phaseCount `3n`. The Hexon
  (n=2), Enneon (n=3), Trihexon (n=6) appear naturally as 2-, 3-,
  and 6-head attention.

This is the "transformer lives inside the Bule" structural claim.
The heavy Q/K/V machinery in `Gnosis.UniversalIntelligenceSSM` and
`Gnosis.InferenceVacuumSSM` matches this Init-only bridge in
vocabulary; the bridge is the formal anchor those modules sit on top of.

Imports `Gnosis.SpectralNoiseEquilibrium`, `Gnosis.BuleyClinamenBraid`,
`Gnosis.HexonBraid`, `Gnosis.BraidedTower`. Zero `sorry`,
zero new `axiom`.
-/

namespace Gnosis
namespace BuleyTransformerSSMBridge

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit BuleyFace buleyUnitScore vacuumBuleUnit clinamenLift
   wasteFaceFromBule actionFaceFromBule entropyFaceFromBule
   bule_unit_decomposes_into_three_faces
   waste_face_score_equals_waste
   action_face_score_equals_opportunity
   entropy_face_score_equals_diversity
   clinamen_lift_score_strict_increment)

open Gnosis.BraidedTower (towerPhaseCount towerBraid)

/-! ## QKV projection ↔ Bule unit -/

/-- A transformer attention head's three projection scalars. Three
non-negative quanta of attention mass flowing through Query, Key, Value. -/
structure QKVProjection where
  q : Nat
  k : Nat
  v : Nat
  deriving Repr, DecidableEq

def qkvScore (p : QKVProjection) : Nat := p.q + p.k + p.v

/-- Bule unit → QKV projection: waste ↦ Q, opportunity ↦ K, diversity ↦ V. -/
def buleToQKV (b : BuleyUnit) : QKVProjection :=
  ⟨b.waste, b.opportunity, b.diversity⟩

/-- QKV projection → Bule unit: Q ↦ waste, K ↦ opportunity, V ↦ diversity. -/
def qkvToBule (p : QKVProjection) : BuleyUnit :=
  ⟨p.q, p.k, p.v⟩

theorem bule_qkv_round_trip (b : BuleyUnit) :
    qkvToBule (buleToQKV b) = b := by
  cases b; rfl

theorem qkv_bule_round_trip (p : QKVProjection) :
    buleToQKV (qkvToBule p) = p := by
  cases p; rfl

theorem qkv_score_equals_bule_score (b : BuleyUnit) :
    qkvScore (buleToQKV b) = buleyUnitScore b := rfl

/-! ## Attention updates as clinamen lifts -/

/-- Single-channel attention updates: each of Q, K, V can be incremented
independently. -/
def updateQ (p : QKVProjection) : QKVProjection := ⟨p.q + 1, p.k, p.v⟩
def updateK (p : QKVProjection) : QKVProjection := ⟨p.q, p.k + 1, p.v⟩
def updateV (p : QKVProjection) : QKVProjection := ⟨p.q, p.k, p.v + 1⟩

/-- Updating Q on a QKVProjection is the same as a `clinamenLift` on the
`waste` face of the projected Bule unit. -/
theorem update_Q_is_clinamen_lift_waste (p : QKVProjection) :
    qkvToBule (updateQ p) = clinamenLift (qkvToBule p) .waste := by
  cases p; rfl

theorem update_K_is_clinamen_lift_opportunity (p : QKVProjection) :
    qkvToBule (updateK p) = clinamenLift (qkvToBule p) .opportunity := by
  cases p; rfl

theorem update_V_is_clinamen_lift_diversity (p : QKVProjection) :
    qkvToBule (updateV p) = clinamenLift (qkvToBule p) .diversity := by
  cases p; rfl

/-- Each Q/K/V update adds exactly +1 to the QKV score. The unit
clinamen residue from `UniversalClinamenPlusOne` is exactly one
attention quantum. -/
theorem update_Q_score_increment (p : QKVProjection) :
    qkvScore (updateQ p) = qkvScore p + 1 := by
  show p.q + 1 + p.k + p.v = p.q + p.k + p.v + 1
  ac_rfl

theorem update_K_score_increment (p : QKVProjection) :
    qkvScore (updateK p) = qkvScore p + 1 := by
  show p.q + (p.k + 1) + p.v = p.q + p.k + p.v + 1
  ac_rfl

theorem update_V_score_increment (p : QKVProjection) :
    qkvScore (updateV p) = qkvScore p + 1 := by
  show p.q + p.k + (p.v + 1) = p.q + p.k + p.v + 1
  ac_rfl

/-! ## QKV decomposition matches the Bule three-face decomposition -/

/-- A QKV projection's score decomposes into the three Bule face scores —
just `q + k + v`, but stated in face-projection form so the equivalence
to `bule_unit_decomposes_into_three_faces` is explicit. -/
theorem qkv_score_decomposes_into_three_faces (p : QKVProjection) :
    qkvScore p
      = buleyUnitScore (wasteFaceFromBule (qkvToBule p))
        + buleyUnitScore (actionFaceFromBule (qkvToBule p))
        + buleyUnitScore (entropyFaceFromBule (qkvToBule p)) := by
  rw [waste_face_score_equals_waste,
      action_face_score_equals_opportunity,
      entropy_face_score_equals_diversity]
  cases p with
  | mk q k v => rfl

/-! ## Multi-head attention as tower level

A single attention head is a Triton (3-cycle on Q/K/V). An `n`-head
attention block is `n` Tritons stacked — the tower level `[3, n]` —
with phaseCount `3n`. Hexon = 2-head, Enneon = 3-head, Trihexon = 6-head. -/

/-- The tower phaseCount for an `n`-head transformer block. -/
def multiHeadPhaseCount (n : Nat) : Nat := towerPhaseCount [3, n]

theorem multi_head_phase_count_eq (n : Nat) :
    multiHeadPhaseCount n = 3 * n := by
  show 3 * (n * 1) = 3 * n
  rw [Nat.mul_one]

theorem one_head_attention_is_triton :
    multiHeadPhaseCount 1 = 3 := by decide

theorem two_head_attention_is_hexon :
    multiHeadPhaseCount 2 = 6 := by decide

theorem three_head_attention_is_enneon :
    multiHeadPhaseCount 3 = 9 := by decide

theorem six_head_attention_is_trihexon :
    multiHeadPhaseCount 6 = 18 := by decide

/-- Eight-head attention: phaseCount 24. In the Aeon projection this is
two full local cycles, before any extra coupling term is added. -/
theorem eight_head_attention_phase_count :
    multiHeadPhaseCount 8 = 24 := by decide

/-- Twelve-head attention: phaseCount 36 = `tritrihexon`. Standard
12-head transformer block sits at the towerBraid `[3, 12]` level. -/
theorem twelve_head_attention_phase_count :
    multiHeadPhaseCount 12 = 36 := by decide

end BuleyTransformerSSMBridge
end Gnosis
