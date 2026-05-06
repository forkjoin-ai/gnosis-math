import Init
import Gnosis.GodFormula
import Gnosis.CapGnosisScaffold

namespace Gnosis
namespace DistributedLedgerMorphism

open Gnosis (godWeight godWeight_ceiling godWeight_conservation godWeight_floor)
open CapGnosisScaffold (StrongLedger EventualLedger)

/-!
# Distributed ledger morphism (**algebraic**, dimensionless)

This does **not** define milliseconds, RTT, or the speed of light. **`lag`** is an abstract **`Nat`**
counter (logical ticks, retry counts, rounds — whatever you label outside this file).

**`ventFromAbstractLag`** clamps **`lag`** into **`min lag R`**, i.e. into the rejection slot **`v`** used by **`godWeight R v`**.

When **`R ≤ lag`**, that clamp is **`v = R`** (**full rejection face**), so **`godWeightFromAbstractLag`** agrees with **`godWeight R R`** and collapses to **`1`** (**`godWeight_floor`**). Ledger-wise this is the opposite pole from the per-pillar **`R + 1`** ceiling in **`TriplePillarCeiling`** (**`BuleyWalrasGnosisCertificate`**) — same **`Init`** formula, saturated **`v`**.

**Two-regime spine.** If **`lag ≤ R`**, then **`vent = lag`** and **`godWeightFromAbstractLag R lag = R + 1 - lag`** (**`godWeightFromAbstractLag_eq_succ_sub_lag_of_le`**). If **`R ≤ lag`**, then **`godWeightFromAbstractLag R lag = 1`**. Bundle: **`godWeightFromAbstractLag_two_regime`**.

**Multi-channel lag (no Walras import).** Sum three abstract lags, then the same **`min (·) R`** clamp (**`ventFromLagSum3`**) equals **`ventFromAbstractLag R (l₁ + l₂ + l₃)`** — same piecewise story with **`lag := l₁ + l₂ + l₃`**.

Calibration (**ms → lag**) stays **external**: hardware clocks are not **`Init`**.

See **`CapGnosisScaffold`** for **`StrongLedger` / `EventualLedger`** vocabulary on **`v`** alone.
-/

/-- Clamp abstract lag/ticks into rejection **`v`** for **`godWeight R v`** (**always `≤ R`**). -/
def ventFromAbstractLag (R lag : Nat) : Nat :=
  min lag R

/-- Lag ⇒ vent ⇒ **`godWeight`** (pure **`Nat`** composition). -/
def godWeightFromAbstractLag (R lag : Nat) : Nat :=
  godWeight R (ventFromAbstractLag R lag)

theorem ventFromAbstractLag_le_R (R lag : Nat) : ventFromAbstractLag R lag ≤ R :=
  Nat.min_le_right lag R

/-- When **`lag ≤ R`**, clamp is identity — vent equals lag (**honest low-lag regime**). -/
theorem ventFromAbstractLag_eq_lag_of_le {R lag : Nat} (hl : lag ≤ R) :
    ventFromAbstractLag R lag = lag := by
  unfold ventFromAbstractLag
  rw [Nat.min_eq_left hl]

/-- In that regime, **`v = 0` iff lag = 0`** (**strong** ledger ⇔ zero lag). -/
theorem vent_zero_iff_lag_zero_of_lag_le_R {R lag : Nat} (hl : lag ≤ R) :
    ventFromAbstractLag R lag = 0 ↔ lag = 0 := by
  rw [ventFromAbstractLag_eq_lag_of_le hl]

/-- Overshoot regime: **`lag ≥ R`** ⇒ vent saturates at **`R`** (**full rejection face**). -/
theorem ventFromAbstractLag_eq_R_of_ge {R lag : Nat} (hl : R ≤ lag) :
    ventFromAbstractLag R lag = R := by
  unfold ventFromAbstractLag
  rw [Nat.min_eq_right hl]

/-- Overshoot: lag morphism reads the same **`v`** as maximal rejection **`R`**. -/
theorem godWeightFromAbstractLag_eq_godWeight_R_R {R lag : Nat} (hl : R ≤ lag) :
    godWeightFromAbstractLag R lag = godWeight R R := by
  unfold godWeightFromAbstractLag
  rw [ventFromAbstractLag_eq_R_of_ge hl]

/-- Overshoot: weight sits at the **`godWeight_floor`** pole (**`1`**). -/
theorem godWeightFromAbstractLag_floor_of_ge {R lag : Nat} (hl : R ≤ lag) :
    godWeightFromAbstractLag R lag = 1 := by
  rw [godWeightFromAbstractLag_eq_godWeight_R_R hl, godWeight_floor R]

/-- Low regime (**`lag ≤ R`**): same closed form as **`godWeight R lag`** — ceiling minus lag in **`ℕ`**. -/
theorem godWeightFromAbstractLag_eq_succ_sub_lag_of_le {R lag : Nat} (hl : lag ≤ R) :
    godWeightFromAbstractLag R lag = R + 1 - lag := by
  unfold godWeightFromAbstractLag
  rw [ventFromAbstractLag_eq_lag_of_le hl]
  have hc := godWeight_conservation R lag hl
  have hleSucc : lag ≤ R + 1 := Nat.le_succ_of_le hl
  have hsum : R + 1 - lag + lag = R + 1 := Nat.sub_add_cancel hleSucc
  have heq : godWeight R lag + lag = (R + 1 - lag) + lag := by
    rw [hc]
    exact hsum.symm
  exact Nat.add_right_cancel heq

/-- Single **`∧`** packaging: low regime (**`R + 1 - lag`**) vs overshoot (**`1`**). -/
theorem godWeightFromAbstractLag_two_regime (R lag : Nat) :
    (lag ≤ R → godWeightFromAbstractLag R lag = R + 1 - lag) ∧
      (R ≤ lag → godWeightFromAbstractLag R lag = 1) :=
  ⟨godWeightFromAbstractLag_eq_succ_sub_lag_of_le, godWeightFromAbstractLag_floor_of_ge⟩

/-- Pool three logical lag counters, then clamp to **`R`** (same **`min`–budget** face as summed pillar vents on **`ℕ`**). -/
def ventFromLagSum3 (R l₁ l₂ l₃ : Nat) : Nat :=
  min (l₁ + l₂ + l₃) R

/-- One **`godWeight`** read on pooled lag sum. -/
abbrev godWeightFromAbstractLagSum3 (R l₁ l₂ l₃ : Nat) : Nat :=
  godWeight R (ventFromLagSum3 R l₁ l₂ l₃)

/-- Pooled three-channel lag is the same clamp as abstract lag on the total tick count. -/
theorem ventFromLagSum3_eq_ventFromAbstractLag_add (R l₁ l₂ l₃ : Nat) :
    ventFromLagSum3 R l₁ l₂ l₃ = ventFromAbstractLag R (l₁ + l₂ + l₃) :=
  rfl

/-- Pooled lag inherits conservation (**`w + v = R + 1`** on the pooled vent). -/
theorem godWeight_conservation_via_lag_sum3 (R l₁ l₂ l₃ : Nat) :
    godWeightFromAbstractLagSum3 R l₁ l₂ l₃ + ventFromLagSum3 R l₁ l₂ l₃ = R + 1 :=
  godWeight_conservation R (ventFromLagSum3 R l₁ l₂ l₃)
    (Nat.min_le_right (l₁ + l₂ + l₃) R)

/-- Zero lag ⇒ **`godWeight` ceiling** (same as **`v = 0`**). -/
theorem godWeightFromAbstractLag_ceiling_at_zero_lag (R lag : Nat) (hz : lag = 0) :
    godWeightFromAbstractLag R lag = R + 1 := by
  subst hz
  unfold godWeightFromAbstractLag ventFromAbstractLag
  simp [godWeight]

/-- **`StrongLedger`** from zero lag when **`lag ≤ R`**. -/
theorem strongLedger_of_zero_lag {R lag : Nat} (_hl : lag ≤ R) (hz : lag = 0) :
    StrongLedger (ventFromAbstractLag R lag) := by
  subst hz
  unfold StrongLedger ventFromAbstractLag
  simp

/-- Positive lag ⇒ eventual-class ledger label (**pure **`Nat`**, no CAP semantics**). -/
theorem eventualLedger_of_pos_lag {R lag : Nat} (hl : lag ≤ R) (hp : 0 < lag) :
    EventualLedger (ventFromAbstractLag R lag) := by
  unfold EventualLedger ventFromAbstractLag
  rw [Nat.min_eq_left hl]
  exact hp

/-- Composition respects **`godWeight_conservation`** whenever **`vent ≤ R`** (always true here). -/
theorem godWeight_conservation_via_lag (R lag : Nat) :
    godWeightFromAbstractLag R lag + ventFromAbstractLag R lag = R + 1 :=
  godWeight_conservation R (ventFromAbstractLag R lag) (ventFromAbstractLag_le_R R lag)

end DistributedLedgerMorphism
end Gnosis
