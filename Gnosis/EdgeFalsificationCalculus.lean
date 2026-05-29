import Init

/-!
# Edge Falsification Calculus — the anti-theory of tradeable edge

An *anti-theory*: rather than assert where edge IS, it states the gates a
candidate edge must pass to be tradeable, and proves that failing ANY gate kills
it — generally, for any claim, with **tweakable thresholds**. It scales: plug in
a measured `(edge, friction, samples, out-of-sample halves)` for any
strategy/universe and the verdict follows by `decide`. The 2026-05-29
hft.finance findings (see `MarketFalsificationLedger.lean`) are instances.

The gates are deliberately the cheap, ruthless ones that kill most "edges":
1. **friction** — net per trade must exceed round-trip cost;
2. **power** — enough events to not be small-sample luck (tweakable
   `minPowerSamples`);
3. **stationarity** — the edge must hold in BOTH out-of-sample halves, not just
   the recent one.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace EdgeFalsificationCalculus

/-- Tweakable gate thresholds. Raise `minPowerSamples` to be stricter. -/
structure Gates where
  minPowerSamples : Nat

def defaultGates : Gates := { minPowerSamples := 100 }

/-- A candidate edge, as measured. All figures in basis points. -/
structure EdgeClaim where
  perTradeEdgeBp  : Int   -- observed capture per trade (gross of friction)
  frictionBp      : Nat   -- round-trip execution cost
  samples         : Nat   -- events observed
  firstHalfNetBp  : Int   -- out-of-sample first half, net of friction
  secondHalfNetBp : Int   -- out-of-sample second half, net of friction

def netPerTradeBp (e : EdgeClaim) : Int := e.perTradeEdgeBp - (e.frictionBp : Int)

/-- Gate 1: net per trade beats friction. -/
def clearsFriction (e : EdgeClaim) : Prop := netPerTradeBp e > 0
/-- Gate 2: enough events to be statistically powered. -/
def powered (e : EdgeClaim) (g : Gates) : Prop := e.samples ≥ g.minPowerSamples
/-- Gate 3: holds in BOTH out-of-sample halves (not just the recent one). -/
def stationary (e : EdgeClaim) : Prop :=
  e.firstHalfNetBp > 0 ∧ e.secondHalfNetBp > 0

/-- A claim is tradeable only if it passes every gate. -/
def tradeable (e : EdgeClaim) (g : Gates) : Prop :=
  clearsFriction e ∧ powered e g ∧ stationary e

instance (e : EdgeClaim) : Decidable (clearsFriction e) := by
  unfold clearsFriction netPerTradeBp; exact inferInstance
instance (e : EdgeClaim) (g : Gates) : Decidable (powered e g) := by
  unfold powered; exact Nat.decLe _ _
instance (e : EdgeClaim) : Decidable (stationary e) := by
  unfold stationary; exact inferInstance

-- ── The anti-theory: failing any one gate kills tradeability (general) ──

theorem sub_friction_kills (e : EdgeClaim)
    (h : e.perTradeEdgeBp ≤ (e.frictionBp : Int)) : ¬ clearsFriction e := by
  unfold clearsFriction netPerTradeBp; omega

theorem underpower_kills (e : EdgeClaim) (g : Gates)
    (h : e.samples < g.minPowerSamples) : ¬ powered e g := by
  unfold powered; omega

theorem nonstationary_kills (e : EdgeClaim)
    (h : e.firstHalfNetBp ≤ 0) : ¬ stationary e := by
  unfold stationary; omega

/-- The master anti-theorem: any failed gate falsifies tradeability. -/
theorem any_failed_gate_kills (e : EdgeClaim) (g : Gates)
    (h : ¬ clearsFriction e ∨ ¬ powered e g ∨ ¬ stationary e) :
    ¬ tradeable e g := by
  intro t
  rcases h with h | h | h
  · exact h t.1
  · exact h t.2.1
  · exact h t.2.2

-- ── Instances: the measured market witnesses (params = real numbers) ──

/-- 1-minute mean-reversion: statistically real (n=42094) but sub-friction. -/
def microReversion : EdgeClaim :=
  { perTradeEdgeBp := 1, frictionBp := 25, samples := 42094,
    firstHalfNetBp := -24, secondHalfNetBp := -24 }

theorem micro_dies_on_friction : ¬ tradeable microReversion defaultGates :=
  any_failed_gate_kills _ _ (Or.inl (sub_friction_kills microReversion (by decide)))

/-- Extreme-daily reversion, pooled across 12 symbols (n=339): clears friction
    AND is powered, but the first out-of-sample half is negative — it is not
    stationary, so it dies. -/
def extremeDailyReversion : EdgeClaim :=
  { perTradeEdgeBp := 75, frictionBp := 25, samples := 339,
    firstHalfNetBp := -31, secondHalfNetBp := 130 }

theorem extreme_daily_clears_friction : clearsFriction extremeDailyReversion := by decide
theorem extreme_daily_is_powered : powered extremeDailyReversion defaultGates := by decide
theorem extreme_daily_dies_on_stationarity :
    ¬ tradeable extremeDailyReversion defaultGates :=
  any_failed_gate_kills _ _
    (Or.inr (Or.inr (nonstationary_kills extremeDailyReversion (by decide))))

/-- The same idea, BTC-only (n=28): clears friction but underpowered — a
    *different* failure mode for the same hypothesis. -/
def extremeDailyBtcOnly : EdgeClaim :=
  { perTradeEdgeBp := 171, frictionBp := 25, samples := 28,
    firstHalfNetBp := 1, secondHalfNetBp := 1 }

theorem btc_only_dies_on_power : ¬ tradeable extremeDailyBtcOnly defaultGates :=
  any_failed_gate_kills _ _
    (Or.inr (Or.inl (underpower_kills extremeDailyBtcOnly defaultGates (by decide))))

/-- Capstone: every candidate edge the probes surfaced fails at least one gate.
    The flat book is correct — not for lack of looking, but because nothing
    cleared the bar. -/
theorem no_candidate_is_tradeable :
    ¬ tradeable microReversion defaultGates
    ∧ ¬ tradeable extremeDailyReversion defaultGates
    ∧ ¬ tradeable extremeDailyBtcOnly defaultGates :=
  ⟨micro_dies_on_friction,
   extreme_daily_dies_on_stationarity,
   btc_only_dies_on_power⟩

end EdgeFalsificationCalculus
end Gnosis
