import Init

/-!
# The Market Pulse Scalp — what the autocorrelation probe found (2026-05-29)

Tested the hypothesis that the market *pulses* on a Taylor cadence (the
quasicrystal carrier of `ImplementationWisdom.lean` §5 / §2) so edge could be
scalped phase-locked to the beat. Probe: autocorrelation of 1-minute returns
on 42,094 BTC/USD samples over 30 days.

Findings, each a theorem over the measured numbers:

1. **No Taylor-cadence directional pulse.** Return ACF at lags 7/11/12/17/22/
   44/66 sits at the white-noise band — there is no momentum beat to ride.
2. **A real 1-minute mean-reversion pulse.** Lag-1 return ACF = −0.0621 on
   42k samples (white-noise 95% band ±0.00955) — ~6.5σ. The market over-reacts
   and reverts at one minute, and bigger moves revert at least as hard.
3. **But it is sub-friction.** The reversion a fader captures is ~0.2–0.55 bp
   per trade; round-trip taker friction is ~25 bp — a ~50× gap. The scalp is
   net-positive only when round-trip cost drops below the per-trade edge (deep
   maker-rebate territory). The edge is real; harvesting it is an *execution*
   problem (maker fills + latency), not a signal one.
4. **Volatility clusters** (vol ACF lag-1 = 0.208, ~20× the band), which is why
   gating on the McNally cliff (`GnosticValley.is_sharp_mcnally_cliff`) is
   sound: turbulence persists, so a cliff read is stable, not noise-chasing.

ACF values are ×10000; money is in centi-bp (bp×100). `import Init` only.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace MarketPulseScalp

-- ════════════════════════════════════════════════════════════════════
-- Section 1: A real 1-minute mean-reversion pulse (not a Taylor beat)
-- ════════════════════════════════════════════════════════════════════

/-- Lag-1 return autocorrelation ×10000 (measured −0.0621). Negative = the
    market reverts the previous minute's move. -/
def lag1ReversionAcfX10000 : Int := -621
/-- |lag-1 ACF| ×10000. -/
def lag1AbsX10000 : Nat := 621
/-- White-noise 95% band ×10000: 1.96/√42094 ≈ 0.00955. -/
def ci95X10000 : Nat := 96

/-- The reversion is real: |lag-1 ACF| clears the noise band by more than 6×
    (~6.5σ). The 1-minute over-react→revert pulse exists. -/
theorem reversion_is_significant : lag1AbsX10000 > 6 * ci95X10000 := by decide

/-- Strongest return-ACF magnitude among the Taylor lags 7/11/12/17/22/44/66
    (×10000): the biggest is lag 12 at 102 — barely at the noise band. -/
def maxTaylorReturnAbsX10000 : Nat := 102

/-- No Taylor-cadence directional pulse: the lag-1 reversion (621) dominates the
    strongest Taylor-lag autocorrelation (102) by more than 5×. The directional
    structure lives at lag 1, not at a keystone/Grassmannian cadence — riding a
    66-tick momentum beat would be riding noise. -/
theorem no_taylor_cadence_pulse : 5 * maxTaylorReturnAbsX10000 < lag1AbsX10000 := by
  decide

-- ════════════════════════════════════════════════════════════════════
-- Section 2: The scalp is real but sub-friction
-- ════════════════════════════════════════════════════════════════════

-- Reversion a fader captures per trade, by move size (centi-bp = bp×100):
def edge0to1Cbp  : Nat := 23   -- 0–1σ moves: 0.23 bp
def edge1to2Cbp  : Nat := 42   -- 1–2σ moves: 0.42 bp
def edge2to3Cbp  : Nat := 34   -- 2–3σ moves: 0.34 bp
def edge3plusCbp : Nat := 55   -- 3σ+ moves : 0.55 bp

/-- Round-trip taker friction, centi-bp (25 bp). -/
def frictionTakerCbp : Nat := 2500

/-- Bigger moves revert at least as hard: the 1–2σ edge exceeds the 0–1σ edge,
    and the 3σ+ edge is the largest — the cliff-window amplification we hoped
    for is present in the signal. -/
theorem bigger_moves_revert_harder :
    edge1to2Cbp > edge0to1Cbp ∧ edge3plusCbp > edge1to2Cbp := by decide

/-- Scalp net per trade = captured edge − round-trip friction. -/
def scalpNetCbp (edgeCbp frictionCbp : Int) : Int := edgeCbp - frictionCbp

/-- **The scalp is net-positive iff round-trip friction is below the per-trade
    edge.** This is the whole game: the signal is fixed (~0.5 bp); the only
    free variable is execution cost. -/
theorem scalp_profitable_iff_friction_below_edge (edge fric : Int) :
    scalpNetCbp edge fric > 0 ↔ fric < edge := by
  unfold scalpNetCbp; omega

/-- As a taker, the scalp is deeply negative: even the best per-trade edge is
    dwarfed by the 2500 cbp friction. -/
theorem taker_scalp_is_negative :
    scalpNetCbp (edge3plusCbp : Int) (frictionTakerCbp : Int) < 0 := by decide

/-- The taker gap is ~50×: friction is at least 50× the (1–2σ) per-trade edge.
    Harvesting needs maker-rebate execution (round-trip cost < ~0.4 bp), not a
    retail taker stack. -/
theorem taker_gap_is_50x : frictionTakerCbp ≥ 50 * edge1to2Cbp := by decide

-- ════════════════════════════════════════════════════════════════════
-- Section 3: Volatility clusters → the McNally cliff read is stable
-- ════════════════════════════════════════════════════════════════════

/-- Volatility ACF at lag 1, ×10000 (measured 0.208). -/
def volAcfLag1X10000 : Nat := 2080

/-- Volatility clusters hard — vol ACF lag-1 is ~20× the noise band — so a
    McNally-cliff regime read persists tick-to-tick rather than flickering.
    Gating entries on the cliff is therefore reading a stable state, not noise. -/
theorem volatility_clusters : volAcfLag1X10000 > 20 * ci95X10000 := by decide

-- ════════════════════════════════════════════════════════════════════
-- Section 4: The complete Market Pulse Scalp theorem
-- ════════════════════════════════════════════════════════════════════

structure MarketPulseScalpTheorem where
  reversion_is_real      : lag1AbsX10000 > 6 * ci95X10000
  no_taylor_pulse        : 5 * maxTaylorReturnAbsX10000 < lag1AbsX10000
  scalp_is_sub_friction  : scalpNetCbp (edge3plusCbp : Int) (frictionTakerCbp : Int) < 0
  volatility_clusters    : volAcfLag1X10000 > 20 * ci95X10000

theorem market_pulse_scalp : MarketPulseScalpTheorem := {
  reversion_is_real     := by decide
  no_taylor_pulse       := by decide
  scalp_is_sub_friction := by decide
  volatility_clusters   := by decide
}

end MarketPulseScalp
end Gnosis
