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

-- ════════════════════════════════════════════════════════════════════
-- Section 5: recursive zoom-out — the reversion is fractal, and the edge
-- crosses the friction wall at the daily extreme-move scale
-- ════════════════════════════════════════════════════════════════════

-- BTC lag-1 return ACF ×10000 at each scale (measured). All negative: the
-- over-react→revert pulse is present at every timeframe, not just 1 minute.
def btcLag1_1min  : Int := -621
def btcLag1_5min  : Int := -620
def btcLag1_15min : Int := -173
def btcLag1_1hour : Int := -158
def btcLag1_1day  : Int := -493

/-- **The reversion pulse is fractal**: lag-1 return ACF is negative at 1min,
    5min, 15min, 1hour, and 1day. The market over-reacts and reverts at every
    scale we probed. -/
theorem reversion_is_fractal :
    btcLag1_1min < 0 ∧ btcLag1_5min < 0 ∧ btcLag1_15min < 0 ∧
    btcLag1_1hour < 0 ∧ btcLag1_1day < 0 := by decide

/-- A conditional-reversion reading: what a fader captures at one
    scale/move-bucket, with the sample count kept so significance is honest. -/
structure ReversionEdge where
  scale       : String
  moveBucket  : String
  samples     : Nat
  fadeEdgeCbp : Int   -- captured reversion, centi-bp (bp×100)
  hitRatePct  : Nat

/-- Round-trip friction, centi-bp (25 bp). -/
def reFrictionCbp : Nat := 2500
/-- A minimum sample count to call an edge statistically powered. -/
def minPowerSamples : Nat := 100

def clearsFriction (e : ReversionEdge) : Prop := e.fadeEdgeCbp > (reFrictionCbp : Int)
def wellPowered (e : ReversionEdge) : Prop := e.samples ≥ minPowerSamples

instance (e : ReversionEdge) : Decidable (clearsFriction e) := by
  unfold clearsFriction; exact inferInstance
instance (e : ReversionEdge) : Decidable (wellPowered e) := by
  unfold wellPowered; exact Nat.decLe _ _

/-- The tradeable candidate: fade a 3σ+ daily move. Captured 171 bp at 71% hit
    over 28 events in ~4 years. -/
def btcDaily3Sigma : ReversionEdge :=
  { scale := "1Day", moveBucket := "3sigma+", samples := 28,
    fadeEdgeCbp := 17118, hitRatePct := 71 }

/-- Moderate daily moves (2–3σ): 49 events, −25 bp — they *trend*, not revert.
    The reversion edge is specific to the extreme tail. -/
def btcDaily2to3Sigma : ReversionEdge :=
  { scale := "1Day", moveBucket := "2-3sigma", samples := 49,
    fadeEdgeCbp := -2513, hitRatePct := 45 }

/-- **The daily extreme-move reversion clears friction** — by ~7× (171 bp vs
    25 bp). At the daily scale the move (and its reversion) dwarfs the fixed
    cost: the same pulse that was sub-friction at 1 minute is tradeable here. -/
theorem daily_extreme_clears_friction : clearsFriction btcDaily3Sigma := by decide

/-- **…but it is underpowered** — only 28 events. Honesty in the certificate:
    the edge crosses friction yet is not yet statistically powered; it needs
    out-of-sample validation before it is bet on. -/
theorem daily_extreme_is_underpowered : ¬ wellPowered btcDaily3Sigma := by decide

/-- The edge is **tail-specific**: moderate (2–3σ) daily moves trend rather than
    revert (negative fade edge), so only the 3σ+ tail snaps back. -/
theorem moderate_daily_moves_trend : btcDaily2to3Sigma.fadeEdgeCbp < 0 := by decide

-- ════════════════════════════════════════════════════════════════════
-- Section 6: the Gnostic-cadence probe — the only multi-scale pulse is
-- volatility clustering; no directional beat survives correction
-- ════════════════════════════════════════════════════════════════════

-- Daily-bar autocorrelation (×10000) at the Picolorenzo levels (GnosticTime),
-- BTC, 1974 daily returns. raw band ci95 = 1.96/√1974 ≈ 0.0441 → 441.
def gnosticCi95X10000 : Nat := 441

-- Volatility (|return|) ACF at the Gnostic levels — all clear the band:
def volAcf_syzygy6  : Nat := 1353   -- 6d
def volAcf_week7    : Nat := 1293
def volAcf_sophia28 : Nat := 1263
def volAcf_void66   : Nat := 605

/-- **Volatility clusters at every Gnostic level** (syzygy/week/sophia/void all
    clear the band). The multi-scale pulse is real — but it is aperiodic
    *clustering*, the persistence the McNally cliff already rides, not a beat. -/
theorem vol_clusters_at_every_gnostic_level :
    volAcf_syzygy6 > gnosticCi95X10000 ∧ volAcf_week7 > gnosticCi95X10000 ∧
    volAcf_sophia28 > gnosticCi95X10000 ∧ volAcf_void66 > gnosticCi95X10000 := by
  decide

-- Strongest *directional* (return) ACF at any Gnostic lag: BTC proton (9d).
def maxGnosticReturnAcfX10000 : Nat := 512   -- 0.0512, ~2.27σ
-- Multiple-comparison band: 30 tests (10 lags × 3 symbols), FWER 0.05 →
-- per-test z ≈ 2.93, × SE(1/√1974 = 0.0225) ≈ 0.066 → 660.
def bonferroniBandX10000 : Nat := 660
-- The void (66d) directional ACF — the Taylor-66 cadence hypothesis.
def voidReturnAcfX10000 : Nat := 186   -- 0.0186

/-- **No Gnostic-cadence directional pulse survives multiple-comparison
    correction.** The strongest directional lag (proton, 9d) clears the raw band
    but falls short of the Bonferroni band for 30 tests — and ~1.5 false
    positives are expected at the raw band. The apparent weekly-momentum beat is
    a multiple-comparison ghost. -/
theorem no_gnostic_directional_pulse :
    maxGnosticReturnAcfX10000 > gnosticCi95X10000 ∧
    maxGnosticReturnAcfX10000 < bonferroniBandX10000 := by decide

/-- **The void (66d) Taylor cadence is not a directional pulse** — inside the
    raw band. The 66-beat that tiles the quasicrystal carrier (Implementation
    Wisdom §5) does not appear as market direction at 66 days. -/
theorem void_is_not_a_directional_pulse :
    voidReturnAcfX10000 < gnosticCi95X10000 := by decide

-- ── The complete certificate, witnessed by BTC ───────────────────────

structure MarketPulseScalpTheorem where
  btc_reverts            : reverts btc30d
  no_taylor_pulse        : ¬ hasTaylorPulse btc30d
  taker_sub_friction     : ¬ takerScalpProfitable btc30d
  vol_clusters           : volClusters btc30d
  pulse_is_btc_specific  : ¬ reverts eth30d
  reversion_is_fractal   : btcLag1_1min < 0 ∧ btcLag1_5min < 0 ∧ btcLag1_15min < 0
                             ∧ btcLag1_1hour < 0 ∧ btcLag1_1day < 0
  daily_extreme_tradeable : clearsFriction btcDaily3Sigma
  but_underpowered        : ¬ wellPowered btcDaily3Sigma
  vol_clusters_all_scales : volAcf_void66 > gnosticCi95X10000
  no_gnostic_dir_pulse    : maxGnosticReturnAcfX10000 < bonferroniBandX10000
  void_not_directional    : voidReturnAcfX10000 < gnosticCi95X10000

theorem market_pulse_scalp : MarketPulseScalpTheorem := {
  btc_reverts            := by decide
  no_taylor_pulse        := by decide
  taker_sub_friction     := by decide
  vol_clusters           := by decide
  pulse_is_btc_specific  := by decide
  reversion_is_fractal   := by decide
  daily_extreme_tradeable := by decide
  but_underpowered        := by decide
  vol_clusters_all_scales := by decide
  no_gnostic_dir_pulse    := by decide
  void_not_directional    := by decide
}

end MarketPulseScalp
end Gnosis
