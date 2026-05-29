import Init

/-!
# The Market Reynolds Gate — trading lessons formalized from the 2026-05-29 session

What the hft.finance backtest sweeps taught, each proven from the measured
numbers. The spine is the Reynolds Principle (`ImplementationWisdom.lean` §1):
a trade is a *prediction*, and a prediction is only profitable ABOVE a
turbulence threshold. Below it the market is laminar — chop with no dominant
mode, i.e. no sharp McNally Cliff (`GnosticValley.lean` `is_sharp_mcnally_cliff`,
σ₁ ≥ 8·σ₂) — and firing only pays friction drag.

Measured on a 7-day window: gross edge per trade ≈ 0 (flat), so realized
net P&L = −friction × (trade count). The loss is therefore a pure *friction
pump*: it scales with how often you fire, and the only loss-minimizing action
below the cliff is **not trading**. As the gates tightened (momentum_flip
debounce, then the McNally-cliff Reynolds gate), the trade count — and the
bleed with it — collapsed exactly as this law predicts.

All money is in basis points (1 bp = 0.01%), Nat/Int only. `import Init` only.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace MarketReynoldsGate

-- ════════════════════════════════════════════════════════════════════
-- Section 1: The friction pump — below-cliff trading is pure drag
-- ════════════════════════════════════════════════════════════════════

/-- Round-trip friction (fees + slippage + spread), basis points.
    `SIGNAL_MC_FRICTION_PCT = 0.0025 = 25 bp`. -/
def frictionBps : Nat := 25

/-- Measured net P&L per trade on the chop window: avgPnl ≈ −$40 on a ~$15k
    position = −0.267% ≈ −27 bp. -/
def measuredNetPerTradeBps : Int := -27

/-- Gross edge per trade = net + friction (add the cost back). −27 + 25 = −2 bp:
    essentially flat. A flat gross edge means σ₁ ≈ σ₂ in the return spectrum —
    no dominant mode, no McNally cliff, no edge. -/
def grossEdgeBps : Int := measuredNetPerTradeBps + (frictionBps : Int)

theorem gross_edge_is_flat : grossEdgeBps = -2 := by decide

/-- The per-trade bleed below the cliff: friction minus the (flat, ≈0) gross
    edge. Measured ≈ 27 bp; taken as a positive Nat (the drag per fire). -/
def dragPerTradeBps : Nat := 27

/-- Total drag from firing `trades` times below the cliff. -/
def totalDragBps (trades : Nat) : Nat := trades * dragPerTradeBps

/-- The friction pump: more trades, strictly more loss. -/
theorem drag_strictly_increases (n : Nat) :
    totalDragBps n < totalDragBps (n + 1) := by
  unfold totalDragBps dragPerTradeBps
  omega

/-- Monotone form: fewer fires, no more drag. -/
theorem drag_monotone {a b : Nat} (h : a ≤ b) :
    totalDragBps a ≤ totalDragBps b :=
  Nat.mul_le_mul h (Nat.le_refl dragPerTradeBps)

/-- **Below the cliff, not trading is loss-optimal.** Zero fires = zero drag,
    and any number of fires costs at least as much. This is the Reynolds
    lazy-gate: below the turbulence threshold, the right action is to not fire.
    A correctly-flat book is not a failure — it is the optimum. -/
theorem flat_is_optimal_below_cliff (trades : Nat) :
    totalDragBps 0 ≤ totalDragBps trades :=
  drag_monotone (Nat.zero_le trades)

theorem flat_has_zero_drag : totalDragBps 0 = 0 := by decide

-- ════════════════════════════════════════════════════════════════════
-- Section 2: The McNally-cliff turbulence gate (the SNR form)
-- ════════════════════════════════════════════════════════════════════

/-- Cliff threshold for the single-symbol SNR, ×100 (so 7.00 → 700). The
    heptad (7) is a Taylor Number; it sits above the random-walk noise floor.
    Mirrors `GnosticValley.is_sharp_mcnally_cliff` (σ₁ ≥ 8·σ₂) in SNR form. -/
def cliffThresholdX100 : Nat := 700

/-- A market regime as a signal-to-noise reading: the realized move `|r20|`
    against the per-tick noise `vol`, both in bp. -/
structure Regime where
  moveBps  : Nat
  noiseBps : Nat

/-- SNR ×100 = move / noise. Zero noise reads as 0 (degenerate, fail-laminar). -/
def snrX100 (r : Regime) : Nat :=
  if r.noiseBps = 0 then 0 else r.moveBps * 100 / r.noiseBps

/-- Turbulent (tradeable) iff the move dominates noise past the cliff. -/
def isTurbulent (r : Regime) : Prop := snrX100 r ≥ cliffThresholdX100

instance (r : Regime) : Decidable (isTurbulent r) := by
  unfold isTurbulent; exact Nat.decLe _ _

/-- Chop: a 40 bp move on 10 bp noise → SNR 4.0 (< cliff). Laminar. -/
def chopRegime : Regime := { moveBps := 40, noiseBps := 10 }
/-- Trend: a 100 bp move on 10 bp noise → SNR 10.0 (≥ cliff). Turbulent. -/
def trendRegime : Regime := { moveBps := 100, noiseBps := 10 }

theorem chop_is_laminar : ¬ isTurbulent chopRegime := by decide
theorem trend_is_turbulent : isTurbulent trendRegime := by decide

/-- Random-walk noise floor for the 20-tick lookback: `|r20|/vol ~ √20`.
    `447² = 199809 ≤ 200000 = 20·100² < 448² = 200704`, so √20·100 ≈ 447. -/
def noiseFloorX100 : Nat := 447

theorem noise_floor_is_sqrt_20 :
    noiseFloorX100 * noiseFloorX100 ≤ 20 * 100 * 100
    ∧ 20 * 100 * 100 < (noiseFloorX100 + 1) * (noiseFloorX100 + 1) := by decide

/-- **The cliff sits above the noise floor**, so a cliff-pass is a genuine
    dominant mode, not a random-walk tail. This is why gating on it filters
    the laminar chop the friction pump bleeds in. -/
theorem cliff_above_noise_floor : noiseFloorX100 < cliffThresholdX100 := by decide

-- ════════════════════════════════════════════════════════════════════
-- Section 3: The measured collapse (tightening the gate drains the pump)
-- ════════════════════════════════════════════════════════════════════

/-- mean_reversion trade counts on the same 7-day window as the gates tightened:
    raw → +momentum_flip debounce → +McNally-cliff Reynolds gate. -/
def tradesRaw        : Nat := 1965
def tradesDebounced  : Nat := 380
def tradesCliffGated : Nat := 120

theorem gates_cut_trade_count :
    tradesCliffGated < tradesDebounced ∧ tradesDebounced < tradesRaw := by decide

/-- Because net ≈ −friction × trades, draining the trade count drains the
    loss. The cliff-gated book bleeds a fraction of the raw churn. -/
theorem cliff_gate_drains_the_pump :
    totalDragBps tradesCliffGated < totalDragBps tradesRaw := by decide

/-- The collapse is ~16× fewer fires (1965 → 120). -/
theorem collapse_is_sixteen_x : tradesRaw ≥ 16 * tradesCliffGated := by decide

-- ════════════════════════════════════════════════════════════════════
-- Section 4: A win must clear friction (the take-profit floor)
-- ════════════════════════════════════════════════════════════════════

/-- The old fixed take-profit: 2.5% = 250 bp. -/
def oldTpBps : Nat := 250
/-- The move-scaled TP floor: 0.6% = 60 bp. -/
def tpFloorBps : Nat := 60
/-- A representative cliff-passing move in the low-vol window: ≈ 70 bp. -/
def chopMoveBps : Nat := 70

/-- A take-profit hit nets `tp − friction`; it is profitable iff `tp > friction`.
    The TP floor (60 bp) clears the 25 bp friction. -/
theorem tp_floor_clears_friction : frictionBps < tpFloorBps := by decide

/-- The old 250 bp TP was *unreachable*: it demanded a bigger move than the
    turbulent regime delivered (≈70 bp), so every entry timed/flipped out
    before target — TP was hit ~0 times. -/
theorem old_tp_unreachable : chopMoveBps < oldTpBps := by decide

/-- The move-scaled TP *is* reachable: the cliff move clears the floor, so the
    turbulent move can be captured as a (small, friction-positive) win. -/
theorem move_scaled_tp_reachable : tpFloorBps ≤ chopMoveBps := by decide

/-- Net per captured win at the floor: 60 − 25 = 35 bp > 0. -/
theorem floor_win_is_net_positive : tpFloorBps - frictionBps = 35 := by decide

-- ════════════════════════════════════════════════════════════════════
-- Section 5: The complete Market Reynolds Gate theorem
-- ════════════════════════════════════════════════════════════════════

structure MarketReynoldsGateTheorem where
  flat_is_optimal_below_cliff : totalDragBps 0 = 0
  chop_is_laminar             : ¬ isTurbulent chopRegime
  cliff_above_noise_floor     : noiseFloorX100 < cliffThresholdX100
  gate_drains_the_pump        : totalDragBps tradesCliffGated < totalDragBps tradesRaw
  win_clears_friction         : frictionBps < tpFloorBps

theorem market_reynolds_gate : MarketReynoldsGateTheorem := {
  flat_is_optimal_below_cliff := by decide
  chop_is_laminar             := by decide
  cliff_above_noise_floor     := by decide
  gate_drains_the_pump        := by decide
  win_clears_friction         := by decide
}

end MarketReynoldsGate
end Gnosis
