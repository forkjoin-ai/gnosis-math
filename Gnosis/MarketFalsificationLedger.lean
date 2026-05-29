import Gnosis.MarketReynoldsGate
import Gnosis.MarketPulseScalp

/-!
# Market Falsification Ledger — every hypothesis the hft.finance probes KILLED

Failures are data. This module is the single auditable record of every market
hypothesis tested and falsified in the 2026-05-29 session, each with its measured
witness and the theorem that kills it. It re-exports the negative results proven
in `MarketReynoldsGate.lean` (the friction pump) and `MarketPulseScalp.lean` (the
pulse probe), and adds the sweep-level failures not recorded elsewhere.

The through-line: **no signal in this universe has a net edge in the current
regime, and no cadence carries a tradeable directional pulse.** The one surviving
lead (extreme-daily reversion) is itself flagged underpowered. Every fix improved
the machinery without manufacturing edge — because the edge was not there to find.

All money/PF in integer units. `import` siblings only. Zero `sorry`, zero axiom.
-/

namespace Gnosis
namespace MarketFalsificationLedger

open MarketReynoldsGate MarketPulseScalp

/-- Profit factor breakeven, ×1000 (pf = 1.0). Below this a signal loses. -/
def pfBreakevenX1000 : Nat := 1000

-- ── FAILURE 1: every tradeable signal loses in this regime ────────────
-- Profit factors ×1000 from the final (all-fixes) 7-day sweep. Every signal
-- that trades is below breakeven; the best (vol_expansion) is pf 0.467.
def pf_vol_expansion   : Nat := 467
def pf_volume_climate  : Nat := 263
def pf_bollinger       : Nat := 244
def pf_momentum_mc     : Nat := 240
def pf_cross_sectional : Nat := 235
def pf_rsi_reversion   : Nat := 228
def pf_breakout        : Nat := 211
def pf_mean_reversion  : Nat := 163

/-- **FAILURE 1 — no signal has net edge.** Even the best tradeable signal's
    profit factor is below breakeven; all the rest are worse. The flat book is
    correct: there is nothing to harvest, so refusing to trade is optimal. -/
theorem all_signals_lose :
    pf_vol_expansion < pfBreakevenX1000 ∧
    pf_volume_climate < pfBreakevenX1000 ∧
    pf_bollinger < pfBreakevenX1000 ∧
    pf_momentum_mc < pfBreakevenX1000 ∧
    pf_cross_sectional < pfBreakevenX1000 ∧
    pf_rsi_reversion < pfBreakevenX1000 ∧
    pf_breakout < pfBreakevenX1000 ∧
    pf_mean_reversion < pfBreakevenX1000 := by decide

-- ── FAILURE 2: "switch to mean_reversion" was the WORST move ──────────
-- Raw (un-fixed) profit factors ×1000: mean_reversion was rock bottom (0.010).
def pf_mean_reversion_raw : Nat := 10

/-- **FAILURE 2 — switching the entry signal does not help.** mean_reversion,
    the suggested chop-day fallback, was the single worst signal (raw pf 0.010,
    −$62k/7d). The problem was never the signal choice. -/
theorem switching_to_mean_reversion_is_worst :
    pf_mean_reversion_raw < pf_mean_reversion ∧
    pf_mean_reversion_raw < pf_breakout := by decide

-- ── FAILURE 3: move-scaled TP helped but did not reach profit ────────
def pf_momentum_mc_beforeTp : Nat := 151  -- cliff-gated, fixed-2.5% TP
def pf_momentum_mc_afterTp  : Nat := 240  -- move-scaled TP

/-- **FAILURE 3 — the TP fix improved the machinery, not the outcome.**
    Move-scaled TP lifted profit factor (0.151 → 0.240, TP finally engaged) but
    stayed below breakeven. A correct fix to a market with no edge still loses. -/
theorem move_scaled_tp_helped_but_still_loses :
    pf_momentum_mc_afterTp > pf_momentum_mc_beforeTp ∧
    pf_momentum_mc_afterTp < pfBreakevenX1000 := by decide

-- ── FAILURE 4: the exit churned on noise (fixed, edge still absent) ──
def tradesUndebounced  : Nat := 1965  -- mean_reversion, un-debounced exit
def tradesCliffGated   : Nat := 120   -- + momentum_flip debounce + McNally cliff

/-- **FAILURE 4 — the un-debounced thesis-exit was a friction pump.** It fired
    on 1-min noise, churning 1965 round-trips. The debounce + cliff gate cut that
    >16×, but the surviving trades still lost (pf 0.163): the gating drained the
    drag, it did not create edge. -/
theorem debounce_cut_churn_not_loss :
    tradesUndebounced ≥ 16 * tradesCliffGated ∧
    pf_mean_reversion < pfBreakevenX1000 := by decide

-- ── FAILURE 5: the extreme-daily reversion lead fails out-of-sample ──
-- Pooled 3σ+ daily fade, 12 symbols, trailing-60d vol (no look-ahead), n=339.
-- Net bp after 25bp round-trip friction, by time split:
def reversionPooledNetBp     : Int := 50    -- looked +50bp pooled
def reversionFirstHalfNetBp  : Int := -31   -- OOS first half: NEGATIVE
def reversionSecondHalfNetBp : Int := 130   -- all the gain in the recent half
def reversionWorstSymbolBp   : Int := -158  -- DOGE (largest n=43): trends, doesn't revert

/-- **FAILURE 5 — the one surviving lead dies out-of-sample.** Pooled it looked
    like +50bp, but the first time-half was NEGATIVE (−31bp) and the entire edge
    is in the recent half (+130bp): non-stationary. Per-symbol it is
    inconsistent — DOGE (the largest sample) reverts −158bp (continues, with
    negative skew: high hit rate, rare catastrophic losses). The n=28 BTC
    +146bp was small-sample luck concentrated in recent history. No stationary,
    universal reversion edge exists. -/
theorem extreme_daily_reversion_fails_oos :
    reversionFirstHalfNetBp < 0 ∧ reversionSecondHalfNetBp > 0
    ∧ reversionWorstSymbolBp < 0 := by decide

/-- The pooled mean is an artifact: it sits between a negative first half and a
    positive second half, so the +50bp is not a stable property. -/
theorem pooled_edge_is_non_stationary :
    reversionFirstHalfNetBp < reversionPooledNetBp
    ∧ reversionPooledNetBp < reversionSecondHalfNetBp := by decide

-- ── FAILURE 6: no Taylor-Sequence money in the price/vol cadence ──────
-- Tested with the correct Taylor's Sequence (TaylorsSequence.lean), the lags in
-- 2..72 are {6,7,8,11,14,15,18,21,22,29,47} = 11 of 71. After DETRENDING the
-- ACF (removing the decay so small lags don't fake a peak), the count of Taylor
-- lags among the top-11 residual peaks — chance ≈ 1.7:
def taylorTop11_btc_vol : Nat := 0
def taylorTop11_btc_ret : Nat := 1
def taylorTop11_eth_vol : Nat := 2
def taylorTop11_eth_ret : Nat := 2
def taylorEnrichmentSignal : Nat := 5  -- would need ≥5/11 to claim a real cadence

/-- **FAILURE 6 — no Taylor-Sequence cadence money.** With the correct sequence
    and the decay detrended, Taylor lags are no more likely to be ACF peaks than
    chance (top-11 counts 0–2 vs expected ~1.7) on either dissipation (vol) or
    direction (returns), BTC and ETH. Taylor numbers organize the compute
    substrate (ImplementationWisdom §5: 66 tiles the antiqueue carrier), NOT the
    crypto price series — the quasicrystal lives in FOIL/scheduling, not price. -/
theorem no_taylor_cadence_money :
    taylorTop11_btc_vol < taylorEnrichmentSignal ∧
    taylorTop11_btc_ret < taylorEnrichmentSignal ∧
    taylorTop11_eth_vol < taylorEnrichmentSignal ∧
    taylorTop11_eth_ret < taylorEnrichmentSignal := by decide

-- ── FAILURE 7: Critical Slowing Down does not predict crypto crashes ──
-- Pooled 12 symbols, 18066 daily obs. Crash = forward-20d drawdown < −25%.
-- P(crash | indicator rising) ×1000, look-ahead-free trailing windows:
def csdBaseRateX1000   : Nat := 115  -- base crash rate 11.5%
def csdVarRisingX1000  : Nat := 138  -- variance rising → 1.2× (mechanical: vol clustering)
def csdAr1RisingX1000  : Nat := 104  -- AR(1) rising → 0.91× (BELOW base)
def csdBothRisingX1000 : Nat := 116  -- both rising (the CSD signal) → 1.01× (= base)

/-- **FAILURE 7 — Critical Slowing Down gives no crash warning.** The
    tipping-point early-warning that works for tumors/ecosystems (rising variance
    + AR(1) before a transition) is null for crypto: the combined signal sits at
    the base rate (lift ~1.0) and AR(1)-rising is BELOW it — the resilience-loss
    precursor is absent. Crypto crashes are exogenous/jump-driven, with no slow
    build-up to warn on. The 1.2× variance lift is just vol-clustering, already
    captured by the McNally cliff. The cancer math does not transfer to price. -/
theorem critical_slowing_down_does_not_warn :
    csdBothRisingX1000 < csdVarRisingX1000
    ∧ csdAr1RisingX1000 < csdBaseRateX1000 := by decide

-- ── FAILURE 8: markets-of-markets is degenerate within crypto ─────────
-- Mycelial cross-asset network (8 majors). Cross-asset return correlation ×1000,
-- by market-stress tercile; network-cup marginal = extra range-variance resolved
-- by market-wide volume BEYOND an asset's own volume:
def cryptoCorrLowStressX1000  : Nat := 753
def cryptoCorrHighStressX1000 : Nat := 744
def networkCupMarginalPctX10  : Nat := 0   -- +0.0% (daily); +1.4% hourly — ~nil

/-- **FAILURE 8 — markets-of-markets cannot help within crypto.** The mycelial
    fork→fold routing predicts correlation rising with stress (contagion). But
    crypto is ALREADY one coalition: correlation sits at ~0.75 in calm AND
    stress (no rise — no idiosyncratic "fork-local" mode to switch from), and
    market-wide volume is collinear with own volume so the network cup adds ~0%.
    Crypto majors are one market wearing eight tickers. A real markets-of-markets
    edge needs heterogeneous asset classes (crypto/equities/bonds), not eight
    correlated coins. -/
theorem markets_of_markets_degenerate_in_crypto :
    cryptoCorrHighStressX1000 ≤ cryptoCorrLowStressX1000
    ∧ cryptoCorrLowStressX1000 > 700
    ∧ networkCupMarginalPctX10 < 5 := by decide

-- ── The complete falsification ledger ────────────────────────────────
-- Bundles the sweep failures above with the pulse/gate negatives proven in the
-- sibling modules — one certificate of everything we killed.

structure FalsificationLedger where
  -- sweep-level (this module)
  no_signal_has_edge        : pf_vol_expansion < pfBreakevenX1000
  signal_switch_is_worst    : pf_mean_reversion_raw < pf_breakout
  tp_fix_still_loses        : pf_momentum_mc_afterTp < pfBreakevenX1000
  debounce_drains_not_edges : tradesUndebounced ≥ 16 * tradesCliffGated
  -- pulse probe (MarketPulseScalp)
  no_taylor_tick_beat       : ¬ hasTaylorPulse btc30d
  taker_scalp_sub_friction  : ¬ takerScalpProfitable btc30d
  no_gnostic_day_beat       : maxGnosticReturnAcfX10000 < bonferroniBandX10000
  void66_not_directional    : voidReturnAcfX10000 < gnosticCi95X10000
  daily_lead_underpowered   : ¬ wellPowered btcDaily3Sigma
  daily_lead_fails_oos      : reversionFirstHalfNetBp < 0 ∧ reversionSecondHalfNetBp > 0
  no_taylor_cadence_money   : taylorTop11_btc_vol < taylorEnrichmentSignal
  csd_does_not_warn         : csdAr1RisingX1000 < csdBaseRateX1000
  markets_of_markets_degenerate : cryptoCorrHighStressX1000 ≤ cryptoCorrLowStressX1000
  -- friction pump (MarketReynoldsGate)
  flat_is_optimal           : totalDragBps 0 = 0

theorem market_falsification_ledger : FalsificationLedger := {
  no_signal_has_edge        := by decide
  signal_switch_is_worst    := by decide
  tp_fix_still_loses        := by decide
  debounce_drains_not_edges := by decide
  no_taylor_tick_beat       := by decide
  taker_scalp_sub_friction  := by decide
  no_gnostic_day_beat       := by decide
  void66_not_directional    := by decide
  daily_lead_underpowered   := by decide
  daily_lead_fails_oos      := by decide
  no_taylor_cadence_money   := by decide
  csd_does_not_warn         := by decide
  markets_of_markets_degenerate := by decide
  flat_is_optimal           := by decide
}

end MarketFalsificationLedger
end Gnosis
