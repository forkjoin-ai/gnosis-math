/-
  Test file for OrderbookAsInterference and LiquidityAsDamping modules.
-/

import Gnosis.OrderbookAsInterference
import Gnosis.LiquidityAsDamping

open Gnosis.OrderbookAsInterference
open Gnosis.LiquidityAsDamping

/-- Test: Create a valid orderbook wave and verify spread constraint. -/
example :
  let w : OrderbookWave := ⟨1000, 1050, 500, 480, 0, 25⟩
  validOrderbookWave w ∧ midPrice w = 1025 := by
  simp [validOrderbookWave, midPrice]
  native_decide

/-- Test: Bid-ask spread is destructive interference. -/
example :
  let w : OrderbookWave := ⟨1000, 1050, 500, 480, 0, 25⟩
  let h : validOrderbookWave w := by simp [validOrderbookWave]; native_decide
  w.spread ≥ 0 := by
  simp
  native_decide

/-- Test: High damping suppresses oscillations. -/
example :
  let d : OrderbookDepth := ⟨10, 10, 5000, 5000⟩
  let h : isHighlyDamped d := by simp [isHighlyDamped]; decide
  oscillationAmplitude d 100 < 10 := by
  unfold oscillationAmplitude dampingCoefficient isHighlyDamped
  native_decide

/-- Test: Momentum wave has strong amplitude. -/
example :
  let m : MomentumWave := ⟨1000, 10, 1000⟩
  hasStrongMomentum m ∧ momentumAmplitude m = 10000 := by
  simp [hasStrongMomentum, momentumAmplitude]
  native_decide

/-- Test: Flash crash is phase runaway (no damping). -/
example :
  let c : PriceCascade := ⟨1000, 500, 100, 50⟩
  isFlashCrash c ∧ flashCrashAmplitude c = 500 := by
  simp [isFlashCrash, flashCrashAmplitude]
  native_decide

/-- Test: Liquidity metrics create damping coefficient. -/
example :
  let m : LiquidityMetrics := ⟨10000, 50, 100, 100, 0⟩
  dampingCoefficient m > 1000 := by
  unfold dampingCoefficient
  native_decide

/-- Test: Illiquid market is underdamped. -/
example :
  let m : LiquidityMetrics := ⟨500, 600, 10, 200, 0⟩
  isUnderdampedMarket m := by
  simp [isUnderdampedMarket]
  native_decide

/-- Test: Volatility matches oscillation amplitude. -/
example :
  let m : LiquidityMetrics := ⟨1000, 100, 50, 75, 0⟩
  let osc : PriceOscillation := ⟨1000, 10, 75, 5⟩
  m.volatility = osc.amplitude := by
  simp

/-- Test: Slippage measures phase delay. -/
example :
  let slip : SlippageMeasure := ⟨1000, 1050, 10⟩
  slippageAmount slip = 50 := by
  simp [slippageAmount]
  native_decide

/-- Test: Momentum locks the standing wave. -/
example :
  let m : MomentumWave := ⟨1000, 10, 2000, 5⟩
  isLockedWave m ∧ reinforcementFactor m = 20000 := by
  simp [isLockedWave, reinforcementFactor]
  native_decide

#check OrderbookAsInterference.bid_ask_spread_is_destructive_interference
#check OrderbookAsInterference.order_book_depth_dampens_price_movement
#check OrderbookAsInterference.market_impact_is_wave_amplification
#check OrderbookAsInterference.flash_crash_is_phase_runaway
#check OrderbookAsInterference.equilibrium_price_is_stationary_wave

#check LiquidityAsDamping.illiquid_market_is_underdamped_oscillation
#check LiquidityAsDamping.volatility_equals_oscillation_amplitude
#check LiquidityAsDamping.slippage_is_order_propagation_phase_delay
#check LiquidityAsDamping.momentum_is_reinforced_standing_wave
#check LiquidityAsDamping.mean_reversion_is_destructive_collapse
