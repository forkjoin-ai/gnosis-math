/-
  TaoBowlTwinVoid.lean
  ====================

  Extends the Tao-bowl calibration (`Gnosis.EchoChamberAsTaoBowl`) with a
  **second axis**: *structural* interior capacity versus *consensus fill*
  that can occupy that capacity without removing the walls.

  * **Structural void** (`voidStructural`) — the room the geometry still
    affords (the Daodejing-11 "void" before social packing).
  * **Consensus fill** (`consensusFill`) — how much of that room has been
    occupied by agreement, norm pressure, or synchronized belief.

  The **effective void** seen by classic single-void bookkeeping is the
  structural void minus the overlap with consensus, saturated at zero:

  `effectiveVoid = voidStructural - min consensusFill voidStructural`.

  When consensus saturates the structural pocket but the rim remains live,
  **functional** usefulness (rim × effective void) collapses while
  **structural** usefulness (rim × structural void) can remain positive —
  the twin-void reading makes that distinction explicit instead of
  conflating the two.

  Imports `Gnosis.EchoChamberAsTaoBowl` for `toClassicBowl`, which maps the
  classic `void` dial to `effectiveVoid` so downstream frequency-mode math
  tracks *usable* emptiness rather than raw cavity size.

  Zero `sorry`, zero new `axiom`.
-/

import Init
import Gnosis.EchoChamberAsTaoBowl

namespace TaoBowlTwinVoid

/-! ## Twin-void bowl with consensus fill -/

/-- A Tao bowl whose void splits into structural capacity and consensus fill.

    All scalar fields are `Nat` calibration dials (same convention as
    `EchoChamberAsTaoBowl.TaoBowl`). -/
structure TaoBowlWithConsensus where
  rim : Nat
  voidStructural : Nat
  consensusFill : Nat
  rigidity : Nat
  damping : Nat
  deriving DecidableEq, Repr

/-- **Effective void** — structural void minus consensus overlap, `Nat`
    subtraction (truncating / saturating at zero). -/
def effectiveVoid (b : TaoBowlWithConsensus) : Nat :=
  b.voidStructural - min b.consensusFill b.voidStructural

/-- **Structural usefulness** — Daoist `rim × void` on the *structural*
    void only (ignores consensus packing). -/
def structuralUsefulness (b : TaoBowlWithConsensus) : Nat :=
  b.rim * b.voidStructural

/-- **Functional usefulness** — `rim × effectiveVoid`; collapses when
    consensus fills the structural pocket (`effectiveVoid = 0`). -/
def functionalUsefulness (b : TaoBowlWithConsensus) : Nat :=
  b.rim * effectiveVoid b

/-! ## Predicates -/

/-- Empty rim: no boundary voices, so no chamber to speak *with*. -/
def IsEmptyRim (b : TaoBowlWithConsensus) : Prop :=
  b.rim = 0

/-- Structurally filled bowl: the geometric void has been removed. -/
def IsStructurallyFilled (b : TaoBowlWithConsensus) : Prop :=
  b.voidStructural = 0

/-- Consensus-saturated regime: usable void is gone, but the rim and the
    structural void dial are still non-zero — agreement has packed the
    interior while the boundary remains active. -/
def IsConsensusSaturated (b : TaoBowlWithConsensus) : Prop :=
  effectiveVoid b = 0 ∧ 0 < b.rim ∧ 0 < b.voidStructural

/-! ## Collapse theorems -/

theorem empty_rim_kills_structural (b : TaoBowlWithConsensus)
    (h : IsEmptyRim b) : structuralUsefulness b = 0 := by
  unfold structuralUsefulness IsEmptyRim at *
  rw [h]
  simp

theorem empty_rim_kills_functional (b : TaoBowlWithConsensus)
    (h : IsEmptyRim b) : functionalUsefulness b = 0 := by
  unfold functionalUsefulness effectiveVoid IsEmptyRim at *
  rw [h]
  simp

theorem structurally_filled_kills_structural (b : TaoBowlWithConsensus)
    (h : IsStructurallyFilled b) : structuralUsefulness b = 0 := by
  unfold structuralUsefulness IsStructurallyFilled at *
  rw [h]
  simp

theorem consensus_saturated_kills_functional (b : TaoBowlWithConsensus)
    (h : IsConsensusSaturated b) : functionalUsefulness b = 0 := by
  unfold functionalUsefulness IsConsensusSaturated at *
  rcases h with ⟨hev, _, _⟩
  rw [hev]
  simp

/-! ## Classic bowl projection -/

/-- Project to the single-void `EchoChamberAsTaoBowl.TaoBowl` carrier.

    The classic **`void`** dial is **`effectiveVoid`**: downstream
    fundamental-mode frequency uses the *usable* emptiness (what remains
    after consensus overlap), not the raw structural cavity. -/
def toClassicBowl (b : TaoBowlWithConsensus) : EchoChamberAsTaoBowl.TaoBowl :=
  { rim := b.rim
    void := effectiveVoid b
    rigidity := b.rigidity
    damping := b.damping }

/-! ## Concrete witnesses -/

/-- Twin analogue of a balanced classic bowl: rim matches structural void,
    no consensus fill, so effective void tracks structural void. -/
def balancedTwin : TaoBowlWithConsensus :=
  { rim := 5
    voidStructural := 5
    consensusFill := 0
    rigidity := 3
    damping := 1 }

/-- Consensus has filled the structural pocket: effective void is zero, but
    `voidStructural` and `rim` remain positive — functional usefulness dies
    while structural usefulness stays alive. -/
def consensusSaturatedWitness : TaoBowlWithConsensus :=
  { rim := 5
    voidStructural := 3
    consensusFill := 5
    rigidity := 3
    damping := 1 }

theorem balanced_twin_maps_to_balanced_classic :
    toClassicBowl balancedTwin = EchoChamberAsTaoBowl.balancedBowl := by
  unfold toClassicBowl balancedTwin EchoChamberAsTaoBowl.balancedBowl
    effectiveVoid
  rfl

theorem consensus_saturated_witness_is_saturated :
    IsConsensusSaturated consensusSaturatedWitness := by
  unfold IsConsensusSaturated consensusSaturatedWitness effectiveVoid
  decide

theorem consensus_saturated_witness_functional_zero :
    functionalUsefulness consensusSaturatedWitness = 0 := by
  exact consensus_saturated_kills_functional consensusSaturatedWitness
    consensus_saturated_witness_is_saturated

theorem consensus_saturated_witness_structural_positive :
    0 < structuralUsefulness consensusSaturatedWitness := by
  unfold structuralUsefulness consensusSaturatedWitness
  decide

theorem consensus_saturated_witness_classic_void_zero :
    (toClassicBowl consensusSaturatedWitness).void = 0 := by
  unfold toClassicBowl consensusSaturatedWitness effectiveVoid
  rfl

end TaoBowlTwinVoid
