import Gnosis.Braided.BraidedTower
import Gnosis.GrandUnification

/-!
# Periodic band ↔ braided tower — jugular attempt + anti-theorem

Concrete claims (no narrative pointers):

1. **Positive witness:** **118** IUPAC slots = `towerPhaseCount [2, 59]`.
2. **Anti-theorem family:** for every `k` with `0 < k < 118`, reducing an index
   mod `k` (`Fin 118 → Fin k`) is **not** injective — `{0, k}` is an explicit
   collision. In particular the dodecagon bucket (`k = 12`) cannot label all rows.
3. **Information-carrier shadow:** any `GrandUnificationSimple.InformationCarrier`
   with `0 < capacity < 118` induces the same coarse readout non-injectivity on the
   IUPAC band (e.g. `superstringWitness` uses capacity **10**).

**Extension band:** braided tower products matching selected **Z > 118** research
targets — arithmetic witnesses only; **no synthesis claim**.

Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace PeriodicBraidMatterJugular

open BraidedTower (towerPhaseCount)
open GrandUnificationSimple (InformationCarrier superstringWitness)

/-! ## Positive anchor: 118 as a braided tower product -/

/-- Explicit tower whose phase cardinality is **118** (= IUPAC known-element band). -/
def iupacBraidTowerFactors : List Nat :=
  [2, 59]

theorem iupac_braid_tower_phase_count :
    towerPhaseCount iupacBraidTowerFactors = 118 := by native_decide

/-- Convenient alias for citing the IUPAC cardinality without unfolding `List Nat`. -/
abbrev iupacBraidPhaseCardinality : Nat :=
  towerPhaseCount iupacBraidTowerFactors

theorem iupac_braid_phase_cardinality_eq118 : iupacBraidPhaseCardinality = 118 :=
  iupac_braid_tower_phase_count

/-- Same phase count as `iupac_braid_tower_phase_count`, unpacked one step. -/
theorem iupac_braid_tower_phase_count_unpacked :
    towerPhaseCount iupacBraidTowerFactors = 2 * 59 := by native_decide

/-! ## Extension-band towers (Z > 118; arithmetic only) -/

theorem extension_band_z119_tower : towerPhaseCount [7, 17] = 119 := by native_decide

theorem extension_band_z120_tower : towerPhaseCount [2, 2, 2, 3, 5] = 120 := by native_decide

theorem extension_band_z126_tower : towerPhaseCount [2, 7, 9] = 126 := by native_decide

theorem extension_band_z140_tower : towerPhaseCount [2, 2, 5, 7] = 140 := by native_decide

/-! ## Anti-theorem family: mod-`k` coarse buckets on `Fin 118` -/

/-- Reduce an IUPAC index modulo **`k`** buckets (`0 < k < 118`). -/
def modKBucketReadout (k : Nat) (hk0 : 0 < k) (_hk118 : k < 118) (i : Fin 118) :
    Fin k :=
  ⟨i.val % k, Nat.mod_lt i.val hk0⟩

theorem mod_k_bucket_readout_collides (k : Nat) (hk0 : 0 < k) (hk118 : k < 118) :
    modKBucketReadout k hk0 hk118 ⟨0, by decide⟩ =
      modKBucketReadout k hk0 hk118 ⟨k, hk118⟩ := by
  apply Fin.ext
  simp only [modKBucketReadout, Fin.val_mk]
  rw [Nat.zero_mod, Nat.mod_self]

theorem mod_k_bucket_inputs_distinct (k : Nat) (hk0 : 0 < k) (hk118 : k < 118) :
    (⟨0, by decide⟩ : Fin 118) ≠ ⟨k, hk118⟩ := by
  intro h
  have hk : 0 = k := congrArg Fin.val h
  rw [← hk] at hk0
  exact absurd hk0 (Nat.lt_irrefl 0)

/-- **Anti-theorem.** No injective labeling of all **118** rows inside **`Fin k`**
when **`k < 118`** — pigeonhole with witness **`{0, k}`**. -/
theorem mod_k_bucket_readout_not_injective (k : Nat) (hk0 : 0 < k) (hk118 : k < 118) :
    ¬Function.Injective (modKBucketReadout k hk0 hk118) := by
  intro hInj
  exact mod_k_bucket_inputs_distinct k hk0 hk118 (hInj (mod_k_bucket_readout_collides k hk0 hk118))

/-! ### Dodecagon specialization (`k = 12`) -/

/-- Read only the dodecagon residue of an IUPAC index (0-based `Fin 118`). -/
abbrev twelveBucketReadout (i : Fin 118) : Fin 12 :=
  modKBucketReadout 12 (by decide) (by decide) i

theorem twelve_bucket_readout_collides :
    twelveBucketReadout ⟨0, by decide⟩ =
      twelveBucketReadout ⟨12, by decide⟩ :=
  mod_k_bucket_readout_collides 12 (by decide) (by decide)

theorem twelve_bucket_collision_inputs_distinct :
    (⟨0, by decide⟩ : Fin 118) ≠ ⟨12, by decide⟩ :=
  mod_k_bucket_inputs_distinct 12 (by decide) (by decide)

theorem twelve_bucket_readout_not_injective :
    ¬Function.Injective twelveBucketReadout :=
  mod_k_bucket_readout_not_injective 12 (by decide) (by decide)

/-! ## Grand-unification carrier coarse readout -/

/-- Same mod-`capacity` collapse as `modKBucketReadout`, keyed off an
`InformationCarrier`'s discrete capacity. -/
abbrev informationCarrierBucketReadout (c : InformationCarrier) (hk : 0 < c.capacity)
    (hcap : c.capacity < 118) (i : Fin 118) : Fin c.capacity :=
  modKBucketReadout c.capacity hk hcap i

theorem information_carrier_bucket_readout_not_injective (c : InformationCarrier)
    (hk : 0 < c.capacity) (hcap : c.capacity < 118) :
    ¬Function.Injective (informationCarrierBucketReadout c hk hcap) :=
  mod_k_bucket_readout_not_injective c.capacity hk hcap

/-- Superstring witness carrier (**capacity 10**) cannot injectively encode the full IUPAC band. -/
theorem superstring_information_carrier_bucket_not_injective :
    ¬Function.Injective
      (informationCarrierBucketReadout superstringWitness.informationCarrier
        (by decide : 0 < superstringWitness.informationCarrier.capacity)
        (by decide : superstringWitness.informationCarrier.capacity < 118)) :=
  information_carrier_bucket_readout_not_injective _ _ _

/-! ## Bundled jugular certificate -/

theorem periodic_braid_matter_jugular_certificate :
    towerPhaseCount iupacBraidTowerFactors = 118
    ∧ ¬Function.Injective twelveBucketReadout
    ∧ (∀ (k : Nat) (hk0 : 0 < k) (hk118 : k < 118),
        ¬Function.Injective (modKBucketReadout k hk0 hk118))
    ∧ ¬Function.Injective
        (informationCarrierBucketReadout superstringWitness.informationCarrier
          (by decide : 0 < superstringWitness.informationCarrier.capacity)
          (by decide : superstringWitness.informationCarrier.capacity < 118)) :=
  ⟨iupac_braid_tower_phase_count,
    twelve_bucket_readout_not_injective,
    fun k hk0 hk118 => mod_k_bucket_readout_not_injective k hk0 hk118,
    superstring_information_carrier_bucket_not_injective⟩

end PeriodicBraidMatterJugular
end Gnosis
