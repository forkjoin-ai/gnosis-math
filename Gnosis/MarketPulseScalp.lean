import Init

/-!
# The Market Pulse Scalp — BTC/USD as witness (2026-05-29)

Tested whether the market *pulses* on a Taylor cadence (the quasicrystal carrier
of `ImplementationWisdom.lean` §5/§2) so edge could be scalped phase-locked to a
beat. Instrument: autocorrelation of 1-minute returns, run live against the
hft.finance broker data.

Pattern mirrors `GnosticValley.lean`'s McNally-cliff witnesses (`qwen_layer_13`):
abstract predicates over a `PulseProbe`, with the **measured BTC/USD reading as
the concrete witness** and ETH/USD as a contrast witness that the directional
pulse is symbol-specific.

What the witnesses prove:
1. **No Taylor-cadence directional pulse** — return ACF at the Taylor lags is at
   the white-noise band; lag-1 dominates by >5×. No momentum beat to ride.
2. **A real 1-minute mean-reversion pulse on BTC** — lag-1 return ACF = −0.0621
   on 42,094 samples (band ±0.00955), ~6.5σ. ETH does **not** revert
   (lag-1 +0.0089, inside the band) — the pulse is BTC-specific.
3. **Sub-friction** — the reversion a fader captures is ~0.2–0.55 bp/trade vs
   ~25 bp round-trip taker: a ~50× gap. Net-positive iff round-trip cost falls
   below the per-trade edge (maker-rebate territory). Execution problem, not a
   signal one.
4. **Volatility clusters** (vol ACF lag-1 0.208, ~20× the band) → the McNally
   cliff read is stable, so cliff-gating is sound.

ACF ×10000; money in centi-bp (bp×100). `import Init` only. Zero `sorry`,
zero new `axiom`.
-/

namespace Gnosis
namespace MarketPulseScalp

/-- A market autocorrelation-probe reading. -/
structure PulseProbe where
  symbol                 : String
  samples                : Nat
  ci95X10000             : Nat   -- white-noise 95% band ×10000 = 19600/√samples
  lag1AcfX10000          : Int   -- signed lag-1 return ACF (negative = reverts)
  maxTaylorReturnAbsX10000 : Nat -- strongest |return ACF| among lags 7..66
  edge1to2Cbp            : Int   -- reversion captured fading a 1–2σ move (bp×100)
  edge3plusCbp           : Int   -- ... fading a 3σ+ move
  volAcfLag1X10000       : Nat   -- volatility (|return|) ACF at lag 1, ×10000
  frictionTakerCbp       : Nat   -- round-trip taker friction (bp×100)

-- ── Abstract predicates ──────────────────────────────────────────────

/-- The series reverts at one minute: lag-1 ACF is negative and clears the
    white-noise band by >6× (significant over-react→revert). -/
def reverts (p : PulseProbe) : Prop :=
  p.lag1AcfX10000 < 0 ∧ p.lag1AcfX10000.natAbs > 6 * p.ci95X10000

/-- There is a Taylor-cadence beat: some Taylor lag's autocorrelation is within
    5× of the lag-1 magnitude (i.e. a comparable periodic peak exists). -/
def hasTaylorPulse (p : PulseProbe) : Prop :=
  5 * p.maxTaylorReturnAbsX10000 ≥ p.lag1AcfX10000.natAbs

/-- Net per trade for a fader = captured edge − round-trip friction. -/
def scalpNetCbp (edgeCbp frictionCbp : Int) : Int := edgeCbp - frictionCbp

/-- A taker can scalp the reversion profitably (best-case 3σ+ move). -/
def takerScalpProfitable (p : PulseProbe) : Prop :=
  scalpNetCbp p.edge3plusCbp (p.frictionTakerCbp : Int) > 0

/-- Volatility clusters: vol ACF lag-1 exceeds 20× the noise band, so the regime
    (turbulent vs laminar) persists tick-to-tick. -/
def volClusters (p : PulseProbe) : Prop :=
  p.volAcfLag1X10000 > 20 * p.ci95X10000

instance (p : PulseProbe) : Decidable (reverts p) := by
  unfold reverts; exact inferInstance
instance (p : PulseProbe) : Decidable (hasTaylorPulse p) := by
  unfold hasTaylorPulse; exact Nat.decLe _ _
instance (p : PulseProbe) : Decidable (takerScalpProfitable p) := by
  unfold takerScalpProfitable scalpNetCbp; exact inferInstance
instance (p : PulseProbe) : Decidable (volClusters p) := by
  unfold volClusters; exact Nat.decLt _ _

-- ── The witnesses (measured live, 30 days, 1-minute bars) ─────────────

/-- BTC/USD, 42,094 1-minute returns over 30 days. The witness. -/
def btc30d : PulseProbe :=
  { symbol := "BTC/USD"
    samples := 42094
    ci95X10000 := 96            -- 1.96/√42094 ≈ 0.00955
    lag1AcfX10000 := -621       -- −0.0621
    maxTaylorReturnAbsX10000 := 102  -- lag 12, the strongest Taylor lag
    edge1to2Cbp := 42           -- 0.42 bp
    edge3plusCbp := 55          -- 0.55 bp
    volAcfLag1X10000 := 2080    -- 0.208
    frictionTakerCbp := 2500 }  -- 25 bp

/-- ETH/USD, 23,847 returns — contrast witness: the directional pulse is
    BTC-specific. -/
def eth30d : PulseProbe :=
  { symbol := "ETH/USD"
    samples := 23847
    ci95X10000 := 127           -- 1.96/√23847 ≈ 0.01269
    lag1AcfX10000 := 89         -- +0.0089 (inside the band, not reversion)
    maxTaylorReturnAbsX10000 := 134
    edge1to2Cbp := -11          -- −0.11 bp (slight momentum, not reversion)
    edge3plusCbp := 53
    volAcfLag1X10000 := 1864    -- 0.186
    frictionTakerCbp := 2500 }

-- ── Theorems witnessed by the measurements ───────────────────────────

/-- **BTC reverts at one minute** — the real pulse. -/
theorem btc_reverts : reverts btc30d := by decide

/-- **No Taylor-cadence pulse on BTC** — lag-1 dominates every Taylor lag. -/
theorem btc_has_no_taylor_pulse : ¬ hasTaylorPulse btc30d := by decide

/-- **A taker cannot scalp it** — the captured reversion is sub-friction. -/
theorem btc_taker_scalp_unprofitable : ¬ takerScalpProfitable btc30d := by decide

/-- **Bigger moves revert harder on BTC** (cliff-window amplification). -/
theorem btc_bigger_moves_revert_harder : btc30d.edge3plusCbp > btc30d.edge1to2Cbp := by
  decide

/-- **Volatility clusters on BTC** → the McNally-cliff read is stable. -/
theorem btc_vol_clusters : volClusters btc30d := by decide

/-- **The pulse is symbol-specific**: ETH does not exhibit the reversion. -/
theorem eth_does_not_revert : ¬ reverts eth30d := by decide

/-- The general law behind the wall: the scalp is net-positive **iff** round-trip
    friction is below the per-trade edge. The signal is fixed (~0.5 bp); the only
    free variable is execution cost — so harvesting is a maker-rebate / latency
    problem, not a signal-discovery one. -/
theorem scalp_profitable_iff_friction_below_edge (edge fric : Int) :
    scalpNetCbp edge fric > 0 ↔ fric < edge := by
  unfold scalpNetCbp; omega

-- ── The complete certificate, witnessed by BTC ───────────────────────

structure MarketPulseScalpTheorem where
  btc_reverts          : reverts btc30d
  no_taylor_pulse      : ¬ hasTaylorPulse btc30d
  taker_sub_friction   : ¬ takerScalpProfitable btc30d
  vol_clusters         : volClusters btc30d
  pulse_is_btc_specific : ¬ reverts eth30d

theorem market_pulse_scalp : MarketPulseScalpTheorem := {
  btc_reverts           := by decide
  no_taylor_pulse       := by decide
  taker_sub_friction    := by decide
  vol_clusters          := by decide
  pulse_is_btc_specific := by decide
}

end MarketPulseScalp
end Gnosis
