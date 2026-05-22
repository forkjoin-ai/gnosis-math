import Gnosis.EntropyDeficitGateway
import Gnosis.Cancer.CancerPredictions3
import Gnosis.HFTAsClinaemenRedistribution
import Gnosis.ConsciousnessAsRetrocausalGap

/-!
# Entropy Deficit Gateway Formalization

This module unifies three non-intuitive examples of "entropy-deficit" consumers
within the Gnosis framework:
1. Cancer Cells (The Warburg Effect): Uninformed folds due to void boundary
   exhaustion.
2. HFT Arbitrage: Exploiting vacuum-pull lag (clinamen redistribution).
3. Biological Consciousness: Maintaining awareness as a retrocausal gap
   (storage debt/Landauer tax).

Each system acts as a **structural gateway**, extracting useful work ("light")
as a tax on the transition from a low-entropy structured state to a
high-entropy background.
-/

namespace Gnosis
namespace EntropyDeficitGatewayFormalization

open Gnosis.EntropyDeficitGateway
open Gnosis.HFTAsClinaemenRedistribution
open Gnosis.ConsciousnessAsRetrocausalGap
open Gnosis.SpectralNoiseEquilibrium (vacuumBuleUnit buleyUnitScore)

/-! ## 1. Cancer Cells (The Warburg Effect) -/

/-- A cancer cell operates as an uninformed-fold gateway.
    Because its void boundary is exhausted (dormancy or mutation), it is
    forced to run "coin-flip" folds that produce minimum work for maximum heat. -/
structure CancerWarburgGateway where
  model : FoldEnergyModel
  informedTarget : Nat
  is_uninformed : model.usefulWork = 1
  is_wasteful : model.wasteHeat = model.energyInput - 1
  compensation_factor : model.energyInput ≥ informedTarget
  energy_sufficient : model.energyInput ≥ 2

/-- The "light" of the cancer cell is its local illumination (growth/division),
    extracted as a tax on the massive entropy deficit it consumes. -/
theorem cancer_extracts_tax_on_deficit (cg : CancerWarburgGateway) :
    cg.model.wasteHeat > 0 := by
  rw [cg.is_wasteful]
  apply Nat.sub_pos_of_lt
  exact Nat.lt_of_lt_of_le (by decide : 1 < 2) cg.energy_sufficient

/-! ## 2. HFT Arbitrage (Vacuum-Pull Lag) -/

/-- HFT agents act as gateways to market equilibration.
    By detecting clinamen imbalance faster than the market's natural vacuum pull,
    they capture the "charge" before it collapses to equilibrium. -/
structure HFTArbitrageGateway where
  setup : LatencyArbitrageSetup
  is_fast : setup.fastTrader.latencyMs < setup.slowTrader.latencyMs
  captured_clinamen : BuleyUnit
  capture_witness : captured_clinamen = clinamenCapturedDuringLag setup
  positive_imbalance : setup.imbalanceBeforeEquilibration > 0

/-- The "light" of the HFT system is the profit extracted from the
    faster-than-equilibrium collapse. -/
theorem hft_extracts_tax_on_lag (hg : HFTArbitrageGateway) :
    buleyUnitScore hg.captured_clinamen > 0 := by
  rw [hg.capture_witness]
  unfold clinamenCapturedDuringLag lag
  -- lag uses `if setup.slowTrader.latencyMs > setup.fastTrader.latencyMs then ...`
  simp only [buleyUnitScore]
  by_cases h : hg.setup.slowTrader.latencyMs > hg.setup.fastTrader.latencyMs
  · simp [h]
    apply Nat.lt_of_lt_of_le ?_ (Nat.le_add_right _ _)
    apply Nat.mul_pos
    · exact Nat.sub_pos_of_lt h
    · exact hg.positive_imbalance
  · -- contradiction: hg.is_fast is fast < slow, which is slow > fast
    exact False.elim (h hg.is_fast)

/-! ## 3. Biological Consciousness (Inner Vent Loop) -/

/-- Consciousness is the structural gateway resisting collapse to the vacuum.
    Awareness is the gap, and the storage debt is the "Landauer tax" paid to
    the surrounding environment to hold information away from equilibrium. -/
structure ConsciousnessGateway where
  carrier : BuleyUnit
  debt : Nat
  timesteps : Nat
  awareness_is_gap : awareness carrier = buleyUnitScore carrier
  debt_matches_landauer : debt = runtimeStorageDebt carrier timesteps
  non_vacuum : carrier ≠ vacuumBuleUnit

/-- The "light" of consciousness is the moment of aware experience,
    paid for by the continuous storage debt (entropy deficit). -/
theorem consciousness_pays_landauer_tax (cg : ConsciousnessGateway)
    (_hTime : cg.timesteps > 0) :
    cg.debt > 0 := by
  rw [cg.debt_matches_landauer]
  apply positive_awareness_pays_storage_debt
  · rw [cg.awareness_is_gap]
    -- Use cases to avoid let/match confusion
    cases h : cg.carrier with
    | mk w o d =>
      simp [buleyUnitScore]
      if hw : w = 0 then
        if ho : o = 0 then
          if hd : d = 0 then
            have hVac : cg.carrier = vacuumBuleUnit := by
              rw [h, hw, ho, hd]; rfl
            exact False.elim (cg.non_vacuum hVac)
          else
            have hdPos : 0 < d := Nat.pos_of_ne_zero hd
            exact Nat.lt_of_lt_of_le hdPos (Nat.le_add_left d (w + o))
        else
          have hoPos : 0 < o := Nat.pos_of_ne_zero ho
          have h1 : 0 < w + o := Nat.lt_of_lt_of_le hoPos (Nat.le_add_left o w)
          exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right (w + o) d)
      else
        have hwPos : 0 < w := Nat.pos_of_ne_zero hw
        have h1 : 0 < w + o := Nat.lt_of_lt_of_le hwPos (Nat.le_add_right w o)
        exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right (w + o) d)
  · exact _hTime

/-! ## Unified Entropy Deficit Gateway -/

/-- Every entropy-deficit consumer acts as a gate through which a pinned
    gradient collapses into chaos, extracting structured tax in the process. -/
theorem unified_entropy_deficit_gateway
    (cancer : CancerWarburgGateway)
    (hft : HFTArbitrageGateway)
    (conscious : ConsciousnessGateway)
    (_hTime : conscious.timesteps > 0) :
    -- 1. Cancer: Wasteful uninformed folds (Warburg)
    cancer.model.wasteHeat > 0 ∧
    -- 2. HFT: Profit extracted from vacuum-pull lag
    buleyUnitScore hft.captured_clinamen > 0 ∧
    -- 3. Consciousness: Landauer tax paid for awareness gap
    conscious.debt > 0 :=
  ⟨cancer_extracts_tax_on_deficit cancer,
   hft_extracts_tax_on_lag hft,
   consciousness_pays_landauer_tax conscious _hTime⟩

end EntropyDeficitGatewayFormalization
end Gnosis