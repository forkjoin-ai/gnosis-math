import Init
import Gnosis.TwelveSlotSixtySixPairsCarrier
import Gnosis.AeonTwelveCarrierList

namespace Gnosis
namespace TwelveSlotSixtySixPairsCarrier

/-!
# Cyclic **`+1`** shear pushed from **`TwelveSlot`** to **`StrictAscendingPair`**

Vertex clock **`cyclicSucc`** on **`Fin twelve`** is **`AeonCycleTwelveShadow.rot`**, re-exported here as **`rotateTwelveSlot`**.

On **`pairsIJ`** chords the aligned operation is **`rotPairNatAdd`** / **`rotPairNat`**: **add the same stride mod twelve to both
endpoints, then re-sort** (**`AeonTwelveCarrierList`**). That differs from rotating **`lo`** and **`hi`** separately as **`Fin`**
slots --- wrapping can **swap** the numerical order, so the shear is defined at the **`Nat × Nat`** chord layer first.

**`StrictAscendingPair.rotatePairStep`** applies one **`rotPairNat`** tick; **`rotatePairIterate k`** agrees with
**`rotPairNatAdd k`** on **`toNatChord`** (**`rotatePairIterate_toNatChord`**). After **`twelve`** steps every chord returns
(**`rotatePairIterate_twelve`**), recycling **`rotPairNatAdd_eq_of_twelve_dvd`**.

Finer **minimal-period / gcd-orbit** stratification lives in **`AeonTwelveUnboundedClosure`** and **`AeonTwelveCarrierList`**;
this file only wires the **carrier-facing** API.

**Next exploration.** Relate **`rotatePairIterate`** periods to **`strideTwelvePeriod`** / gcd lemmas already packaged on **`pairsIJ`**,
or restrict **`ForrestWalk`** in **`Gnosis.FoilForrestWalk`** by imposing **`rotatePairStep`**-equivariance predicates stepwise.
-/

open Gnosis.AeonCycleTwelveShadow
open Gnosis.AeonTwelveCarrierList

/-- One **`cyclicSucc`** tick on twelve slots (**alias for **`AeonCycleTwelveShadow.rot`**). -/
abbrev rotateTwelveSlot : TwelveSlot → TwelveSlot :=
  rot

namespace StrictAscendingPair

/-- Sorted **`pairsIJ`** shear: apply **`rotPairNat`** to **`toNatChord`**, repackage as a **`StrictAscendingPair`**. -/
def rotatePairStep (p : StrictAscendingPair) : StrictAscendingPair :=
  let q := rotPairNat p.toNatChord
  have hq : q ∈ pairsIJ :=
    rotPairNatAdd_mem_pairsIJ 1 p.toNatChord (StrictAscendingPair.mem_pairsIJ p)
  ⟨⟨q.1, (pairsIJ_coords_lt_twelve q hq).1⟩, ⟨q.2, (pairsIJ_coords_lt_twelve q hq).2⟩,
    pairsIJ_fst_lt_snd q hq⟩

theorem rotatePairStep_toNatChord (p : StrictAscendingPair) :
    (rotatePairStep p).toNatChord = rotPairNat p.toNatChord :=
  rfl

/-- **`k`** composed shears on **`StrictAscendingPair`** (**`Nat`** recursion --- **`Init`** surface). -/
def rotatePairIterate (k : Nat) (p : StrictAscendingPair) : StrictAscendingPair :=
  match k with
  | 0 => p
  | Nat.succ k' => rotatePairStep (rotatePairIterate k' p)

theorem mem_pairsIJ_rotatePairIterate (p : StrictAscendingPair) (k : Nat) :
    (rotatePairIterate k p).toNatChord ∈ pairsIJ := by
  induction k with
  | zero =>
    simpa [rotatePairIterate] using StrictAscendingPair.mem_pairsIJ p
  | succ k IH =>
    simpa [rotatePairIterate, rotatePairStep, rotPairNat] using
      rotPairNatAdd_mem_pairsIJ 1 (rotatePairIterate k p).toNatChord IH

theorem rotatePairIterate_toNatChord (k : Nat) (p : StrictAscendingPair) :
    (rotatePairIterate k p).toNatChord = rotPairNatAdd k p.toNatChord := by
  induction k with
  | zero =>
    simpa [rotatePairIterate] using
      (rotPairNatAdd_zero_pairsIJ p.toNatChord (StrictAscendingPair.mem_pairsIJ p)).symm
  | succ k IH =>
    rw [rotatePairIterate, rotatePairStep_toNatChord, rotPairNat]
    have hp := StrictAscendingPair.mem_pairsIJ p
    rw [IH, ← rotPairNatAdd_add_eq_rot_comp k 1 p.toNatChord hp]

/-- **`twelve`** ticks restore each **`pairsIJ`** chord label (**global period** for this **`ℤ/12ℤ`** shear). -/
theorem rotatePairIterate_twelve (p : StrictAscendingPair) :
    rotatePairIterate twelve p = p := by
  apply StrictAscendingPair.toNatChord_injective
  rw [rotatePairIterate_toNatChord]
  exact rotPairNatAdd_eq_of_twelve_dvd (StrictAscendingPair.mem_pairsIJ p) (Nat.dvd_refl twelve)

end StrictAscendingPair

end TwelveSlotSixtySixPairsCarrier
end Gnosis
