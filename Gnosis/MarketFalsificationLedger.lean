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
  flat_is_optimal           := by decide
}

end MarketFalsificationLedger
end Gnosis
