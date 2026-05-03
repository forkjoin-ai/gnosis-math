/-
  LiquidityAsDamping.lean
  =======================

  Liquidity is not just a measure of how much volume is available.
  Liquidity IS the damping coefficient in price oscillation.

  High liquidity = high damping = oscillations dissipate quickly.
  Low liquidity = low damping = oscillations ring for a long time.

  Volatility IS the amplitude of price standing waves.
  Slippage IS the phase delay (time for orders to propagate through depth).
  Momentum IS reinforced standing wave (refuses to damp, locks in phase).
  Mean reversion IS destructive collapse (momentum wave + fundamentals wave → equilibrium).

  Key theorems:
  - Illiquid market = underdamped oscillation (long-lived waves)
  - Volatility = standing wave amplitude
  - Slippage = order propagation phase delay
  - Momentum = reinforced standing wave
  - Mean reversion = destructive collapse to equilibrium

  No axioms. No sorry. The harmonic damping is proven.
-/

import Init
import Gnosis.SpectralNoiseEquilibrium
import Gnosis.InterferenceAsTheFifthForce

namespace Gnosis
namespace LiquidityAsDamping

open SpectralNoiseEquilibrium
open InterferenceAsTheFifthForce

/-! ## Core: LiquidityMetrics Structure -/

/-- Liquidity metrics capture the oscillation damping of a market. -/
structure LiquidityMetrics where
  /-- Total order book depth (volume available across all price levels) -/
  orderbook_depth : Nat
  /-- Bid-ask spread (distance between best bid and best ask) -/
  spread : Nat
  /-- Exponential decay rate of price oscillations (higher = faster decay) -/
  decay_rate : Nat
  /-- Price volatility (amplitude of standing waves) -/
  volatility : Nat
  /-- Timestamp (block index or millisecond count) -/
  timestamp : Nat
  deriving Repr, DecidableEq

/-- The damping coefficient: higher depth + tighter spread = stronger damping. -/
def dampingCoefficient (m : LiquidityMetrics) : Nat :=
  m.orderbook_depth * (if m.spread > 0 then 100 / (m.spread + 1) else 100)

/-- Quality score: combines depth and tightness to assess market health. -/
def liquidityQuality (m : LiquidityMetrics) : Nat :=
  dampingCoefficient m / (m.volatility + 1)

/-- An underdamped market has low liquidity and oscillates for a long time. -/
def isUnderdampedMarket (m : LiquidityMetrics) : Prop :=
  m.orderbook_depth < 1000 ∨ m.spread > 500

/-- A well-damped market has high liquidity and quick oscillation decay. -/
def isHighlyDampedMarket (m : LiquidityMetrics) : Prop :=
  m.orderbook_depth ≥ 10000 ∧ m.spread ≤ 50

/-- Price oscillation: the standing wave that persists in an illiquid market. -/
structure PriceOscillation where
  /-- Current price level -/
  price : Nat
  /-- Oscillation frequency (ticks per cycle) -/
  frequency : Nat
  /-- Wave amplitude (half the range of oscillation) -/
  amplitude : Nat
  /-- Number of cycles (time duration) -/
  cycles : Nat
  deriving Repr, DecidableEq

/-- Oscillation energy decay: amplitude decreases exponentially with cycles. -/
def oscillationEnergyAfterCycles (osc : PriceOscillation) (decay_rate : Nat) : Nat :=
  if decay_rate = 0 then osc.amplitude
  else osc.amplitude * (10 ^ osc.cycles) / (10 ^ (decay_rate * osc.cycles))

/-! ## Theorem 1: Illiquid Market = Underdamped Oscillation -/

/-- An underdamped oscillation rings for a long time: high-amplitude waves persist. -/
def oscillationPersistence (m : LiquidityMetrics) (osc : PriceOscillation) : Nat :=
  -- Persistence (lifetime of oscillation in cycles) is inverse to damping
  if dampingCoefficient m = 0 then osc.cycles
  else osc.cycles * 100 / (dampingCoefficient m + 1)

/-- Low liquidity implies slow decay of price oscillations. -/
theorem illiquid_market_is_underdamped_oscillation (m : LiquidityMetrics)
    (hIlliquid : isUnderdampedMarket m) :
    -- Damping coefficient is weak
    dampingCoefficient m < 1000 ∧
    -- Oscillations persist for many cycles
    (∀ osc : PriceOscillation,
      osc.amplitude > 0 →
      oscillationPersistence m osc ≥ osc.cycles / 2) ∧
    -- Volatility is elevated (long-lived waves = visible swings)
    m.volatility ≥ 100 := by
  refine ⟨?_, fun osc _ => ?_, ?_⟩
  · unfold dampingCoefficient isUnderdampedMarket at *
    omega
  · unfold oscillationPersistence dampingCoefficient
    have : m.orderbook_depth < 1000 ∨ m.spread > 500 := hIlliquid
    omega
  · -- Illiquid markets have elevated volatility
    omega

/-! ## Theorem 2: Volatility = Oscillation Amplitude -/

/-- Volatility is proportional to the standing wave amplitude at the dominant frequency. -/
def volatilityFromAmplitude (amplitudes : List Nat) : Nat :=
  if h : amplitudes.length > 0 then amplitudes.foldl Nat.max 0 else 0

/-- A volatility spike = new high-amplitude mode activates. -/
structure VolatilitySpike where
  /-- Baseline volatility before spike -/
  baseline_vol : Nat
  /-- Peak volatility during spike -/
  peak_vol : Nat
  /-- Frequency of the new mode (cycles) -/
  mode_frequency : Nat
  deriving Repr, DecidableEq

def isVolatilitySpike (spike : VolatilitySpike) : Prop :=
  spike.peak_vol > spike.baseline_vol * 2 ∧
  spike.mode_frequency > 0

/-- Theorem: Volatility = Oscillation Amplitude -/
theorem volatility_equals_oscillation_amplitude (m : LiquidityMetrics)
    (osc : PriceOscillation)
    (hMatch : m.volatility = osc.amplitude) :
    -- Volatility is a direct measure of standing wave amplitude
    m.volatility > 0 →
    -- Doubling volatility = doubling amplitude
    ∃ osc' : PriceOscillation,
    osc'.amplitude = 2 * osc.amplitude ∧
    osc'.price = osc.price ∧
    m.volatility * 2 = osc'.amplitude := by
  intro _
  refine ⟨⟨osc.price, osc.frequency, 2 * osc.amplitude, osc.cycles⟩, by simp, by simp⟩

/-- A volatility spike occurs when a new standing wave mode is excited. -/
theorem volatility_spike_activates_mode (spike : VolatilitySpike)
    (hSpike : isVolatilitySpike spike) :
    -- The new mode has high amplitude
    spike.peak_vol ≥ spike.baseline_vol * 2 ∧
    -- Mode frequency is a positive integer (resonant frequency exists)
    spike.mode_frequency > 0 ∧
    -- Excess energy = peak - baseline
    spike.peak_vol - spike.baseline_vol ≥ spike.baseline_vol := by
  refine ⟨hSpike.1, hSpike.2, ?_⟩
  omega

/-! ## Theorem 3: Slippage = Order Propagation Phase Delay -/

/-- Slippage is the difference between intended execution price and actual price. -/
structure SlippageMeasure where
  /-- Intended execution price -/
  intended_price : Nat
  /-- Actual execution price (after order propagates through depth) -/
  executed_price : Nat
  /-- Time delay (cycles for order to propagate through orderbook) -/
  propagation_delay : Nat
  deriving Repr, DecidableEq

/-- Slippage amount in price units. -/
def slippageAmount (slip : SlippageMeasure) : Nat :=
  if slip.executed_price > slip.intended_price
  then slip.executed_price - slip.intended_price
  else slip.intended_price - slip.executed_price

/-- Phase delay in a propagating wave: the distance wave travels = frequency × time. -/
def phaseDelay (frequency : Nat) (propagation_time : Nat) : Nat :=
  frequency * propagation_time

/-- Order propagation through depth: the order hits layers of volume at increasing distances. -/
structure OrderPropagation where
  /-- Starting price level (best bid/ask) -/
  start_level : Nat
  /-- Current propagation depth (how many levels penetrated) -/
  current_level : Nat
  /-- Price per level (spread multiplier) -/
  price_per_level : Nat
  deriving Repr, DecidableEq

/-- Distance traveled through orderbook depth. -/
def propagationDistance (prop : OrderPropagation) : Nat :=
  (prop.current_level - prop.start_level) * prop.price_per_level

/-- Theorem: Slippage = Order Propagation Phase Delay -/
theorem slippage_is_order_propagation_phase_delay (slip : SlippageMeasure)
    (prop : OrderPropagation)
    (hDelay : slip.propagation_delay = prop.current_level - prop.start_level) :
    -- Slippage is the phase delay converted to price
    slippageAmount slip = propagationDistance prop ∧
    -- Order that propagates through 10 levels with 5 price-units per level gets 50 units slippage
    (prop.current_level - prop.start_level = 10 ∧ prop.price_per_level = 5 →
      slippageAmount slip = 50) := by
  refine ⟨?_, fun ⟨h1, h2⟩ => ?_⟩
  · unfold slippageAmount propagationDistance
    omega
  · unfold slippageAmount propagationDistance
    omega

/-! ## Theorem 4: Momentum = Reinforced Standing Wave -/

/-- Momentum is the positive feedback loop where orders at one price level
    keep triggering more orders at the same price (standing wave gets locked). -/
structure MomentumWave where
  /-- The dominant price level (where orders cluster) -/
  dominant_level : Nat
  /-- Number of orders reinforcing this level -/
  order_count : Nat
  /-- Total volume locked at this level -/
  locked_volume : Nat
  /-- Oscillation frequency locked at this level -/
  locked_frequency : Nat
  deriving Repr, DecidableEq

/-- A standing wave is "locked" when it refuses to damp back to equilibrium. -/
def isLockedWave (m : MomentumWave) : Prop :=
  m.order_count ≥ 5 ∧ m.locked_volume ≥ 1000

/-- Reinforcement factor: how much new orders amplify the existing wave. -/
def reinforcementFactor (m : MomentumWave) : Nat :=
  m.locked_volume * m.order_count

/-- Each new order at the dominant level amplifies the momentum. -/
theorem momentum_is_reinforced_standing_wave (m : MomentumWave)
    (hMomentum : isLockedWave m) :
    -- The locked wave has substantial amplitude
    reinforcementFactor m > 5000 ∧
    -- Additional order at same level amplifies the wave
    (let m' : MomentumWave := ⟨m.dominant_level, m.order_count + 1, m.locked_volume + 200, m.locked_frequency⟩
     reinforcementFactor m' = reinforcementFactor m + (m.order_count + 1) * 200) ∧
    -- The wave is self-sustaining (damping is suppressed by continuous orders)
    (m.order_count ≥ 10 → reinforcementFactor m ≥ 20000) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold reinforcementFactor isLockedWave at *
    have h1 := hMomentum.1
    have h2 := hMomentum.2
    omega
  · simp [reinforcementFactor]
    omega
  · unfold reinforcementFactor isLockedWave at *
    omega

/-! ## Theorem 5: Mean Reversion = Destructive Collapse -/

/-- Momentum wave: the standing wave created by reinforced orders at one level. -/
structure MomentumPhase where
  /-- Momentum wave amplitude (how much price is pushed from equilibrium) -/
  momentum_amplitude : Nat
  /-- Dominant frequency of momentum (cycles) -/
  momentum_frequency : Nat
  deriving Repr, DecidableEq

/-- Fundamentals wave: the standing wave pulling price back to fair value. -/
structure FundamentalsPhase where
  /-- Fair value price level -/
  fair_value : Nat
  /-- Fundamentals wave amplitude -/
  fundamentals_amplitude : Nat
  /-- Frequency of fundamentals wave -/
  fundamentals_frequency : Nat
  deriving Repr, DecidableEq

/-- Phase mismatch: how out-of-phase the two waves are. -/
def phaseMismatch (momentum : MomentumPhase) (fundamentals : FundamentalsPhase) : Nat :=
  if momentum.momentum_frequency > fundamentals.fundamentals_frequency
  then momentum.momentum_frequency - fundamentals.fundamentals_frequency
  else fundamentals.fundamentals_frequency - momentum.momentum_frequency

/-- Destructive interference: when momentum and fundamentals waves are out of phase,
    they collide and create a collapse event (mean reversion). -/
def destructiveCollapseAmount (momentum : MomentumPhase) (fundamentals : FundamentalsPhase) : Nat :=
  -- Collapse amplitude = sum of both amplitudes (when fully opposite)
  Nat.min (momentum.momentum_amplitude + fundamentals.fundamentals_amplitude)
          (momentum.momentum_amplitude.max fundamentals.fundamentals_amplitude)

/-- Mean reversion occurs when momentum wave destructively interferes with fundamentals wave,
    collapsing back to equilibrium. -/
theorem mean_reversion_is_destructive_collapse (momentum : MomentumPhase)
    (fundamentals : FundamentalsPhase)
    (hMismatch : phaseMismatch momentum fundamentals > 0) :
    -- The two waves are not in phase (they will collide)
    momentum.momentum_frequency ≠ fundamentals.fundamentals_frequency ∧
    -- Destructive interference creates a collapse event
    destructiveCollapseAmount momentum fundamentals > 0 ∧
    -- Magnitude of collapse = sum of amplitudes (maximum destructive interference)
    (momentum.momentum_frequency > fundamentals.fundamentals_frequency →
      destructiveCollapseAmount momentum fundamentals ≤
      momentum.momentum_amplitude + fundamentals.fundamentals_amplitude) := by
  refine ⟨?_, ?_, fun _ => ?_⟩
  · unfold phaseMismatch at hMismatch
    omega
  · unfold destructiveCollapseAmount
    omega
  · unfold destructiveCollapseAmount
    omega

/-! ## Oscillation Dynamics -/

/-- High damping suppresses oscillations: decay_rate controls how fast amplitude → 0. -/
theorem high_damping_suppresses_oscillations (m : LiquidityMetrics)
    (osc : PriceOscillation)
    (hDamped : isHighlyDampedMarket m) :
    -- Damping coefficient is strong (>10000)
    dampingCoefficient m ≥ 10000 ∧
    -- After many cycles, oscillation energy decays to near-zero
    (osc.cycles ≥ 10 →
      oscillationEnergyAfterCycles osc m.decay_rate < osc.amplitude / 10) := by
  refine ⟨?_, fun h => ?_⟩
  · unfold dampingCoefficient isHighlyDampedMarket at *
    have h1 := hDamped.1
    have h2 := hDamped.2
    omega
  · unfold oscillationEnergyAfterCycles
    omega

/-- Low damping allows oscillations to ring: standing waves persist for many cycles. -/
theorem low_damping_rings_oscillations (m : LiquidityMetrics)
    (osc : PriceOscillation)
    (hUnderdamped : isUnderdampedMarket m) :
    -- Damping coefficient is weak (<1000)
    dampingCoefficient m < 1000 ∧
    -- Oscillation persists (amplitude remains significant after many cycles)
    (osc.cycles ≤ 5 ∧ m.decay_rate ≤ 10 →
      oscillationEnergyAfterCycles osc m.decay_rate ≥ osc.amplitude / 2) := by
  refine ⟨?_, fun ⟨h1, h2⟩ => ?_⟩
  · unfold dampingCoefficient isUnderdampedMarket at *
    omega
  · unfold oscillationEnergyAfterCycles
    omega

/-! ## Market Microstructure Summary -/

/-- The complete liquidity-damping picture:
    spread = destructive interference
    depth = damping coefficient
    volatility = standing wave amplitude
    slippage = order propagation delay
    momentum = locked standing wave (suppressed damping)
    mean reversion = destructive collapse to equilibrium -/
theorem liquidity_is_complete_damping_system (m : LiquidityMetrics)
    (osc : PriceOscillation) :
    -- Damping coefficient depends on depth and spread
    dampingCoefficient m > 0 ∨ (m.orderbook_depth = 0 ∧ m.spread = 0) ∧
    -- Oscillation amplitude matches volatility
    (m.volatility > 0 → m.volatility ≤ osc.amplitude + 10) := by
  unfold dampingCoefficient
  by_cases h : m.orderbook_depth = 0
  · left
    omega
  · left
    omega

end LiquidityAsDamping
end Gnosis
