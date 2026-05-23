import Gnosis.SleepDebt
import Gnosis.Body.Allostasis
import Gnosis.Body.Robustness

/-!
# Sleep Resilience — The Dose Makes the Poison, Applied to Sleep

Acute sleep debt recovers; chronic sleep deprivation crashes. This module welds
the three sibling spines into one statement of *sleep* resilience:

* `Gnosis.SleepDebt` — the per-night carry mechanics. Wake accrues a
  `totalRecoveryDemand`; a night recovers up to `recoveryQuota`; what is left over
  is `residualDebt`, the debt carried into the next night. `effectiveCapacity`
  reads how much of `maxCapacity` the carried debt eats. These are the per-cycle
  equations of a single night.
* `Gnosis.Body.Allostasis` — chronic accumulation. The nightly *deficit* (the
  gap between what wake demands and what sleep returns) is an allostatic
  `load perTick ticks` that grows linearly over nights and, past a `tolerance`,
  `breaks` the body. `the_dose_makes_the_poison` says the SAME per-night deficit
  is survived acutely and fatal chronically; `allostaticGrit` is how many
  deprived nights the body tolerates.
* `Gnosis.Body.Robustness` — the breaking semantics: `withstands` while within
  tolerance, `breaks` past it; grit is the sharp wall.

The arc, as theorems:

1. **One good night clears acute debt** — `one_good_night_clears_acute_debt`:
   if a night's full recovery covers wake load plus the carried deficit, the
   residual debt is exactly `0`. Reuses
   `SleepDebt.full_recovery_clears_residual_debt`.
2. **Capacity restored** — `restores_capacity`: after that full night, effective
   capacity returns to `maxCapacity`. Reuses
   `SleepDebt.full_recovery_restores_capacity`.
3. **Chronic deprivation accumulates** — `chronic_deprivation_accumulates`: when
   each night's quota stays below the daily load, the accumulated sleep deficit
   grows monotonically over nights. Reuses `Allostasis.load_monotone`.
4. **Chronic deprivation breaks** — `chronic_deprivation_breaks`: a sustained
   nightly deficit, given enough nights, exceeds any fixed tolerance and the body
   `breaks` (microsleeps / collapse). Bridges to `Allostasis.chronic_breaks`.
5. **The dose makes the poison, for sleep** — `the_dose_makes_the_poison_sleep`:
   one all-nighter is withstood and its acute debt clears in a single full night,
   yet the same deficit sustained nightly breaks the body. Composes (1) and (4).
6. **Sleep grit** — `sleep_grit`: the number of deprived nights tolerated before
   collapse is finite (collapse is inevitable in bounded time) yet positive (the
   body endures at least one bad night). Reuses `Allostasis.allostatic_grit`.

Rustic Church: `import Init` only, here via three Init-clean sibling spines
(`Gnosis.SleepDebt`, `Gnosis.Body.Allostasis`, `Gnosis.Body.Robustness`, whose
own transitive imports bottom out at `Init`). `Nat` only, no Float/Real, no
Mathlib. Proofs are term-mode / named core `Nat` lemmas with reuse of the spine
theorems. No `sorry`, no `simp`/`decide`/`omega` on open goals.
-/

namespace Gnosis.Body.SleepResilience

open Gnosis.SleepDebt
open Gnosis.Body.Allostasis
open Gnosis.Body.Robustness

/-! ## 0. The nightly deficit

A single night accrues a `wakeLoad` of recovery demand and is granted a
`recoveryQuota` of restorative sleep. The *nightly deficit* is the shortfall:
how much wake demanded that sleep failed to return. When the quota covers the
load the deficit is `0` (truncated `Nat.sub`); when it falls short, the deficit
is the seed of accumulating chronic debt. -/

/-- **Nightly deficit.** The per-night shortfall of recovery: daily recovery
    demand `perDay` minus the night's `recoveryQuota`, truncated at `0`. A
    sustained positive deficit is what accumulates into chronic sleep debt. -/
def nightlyDeficit (perDay recoveryQuota : Nat) : Nat := perDay - recoveryQuota

/-- A night whose quota meets the daily demand leaves no deficit: an adequately
    rested night adds nothing to the chronic ledger. -/
theorem rested_night_no_deficit {perDay recoveryQuota : Nat}
    (hRested : perDay ≤ recoveryQuota) : nightlyDeficit perDay recoveryQuota = 0 := by
  unfold nightlyDeficit
  exact Nat.sub_eq_zero_of_le hRested

/-- A night whose quota falls short of the daily demand leaves a strictly
    positive deficit — the per-night stressor that, sustained, becomes the
    chronic load. -/
theorem deprived_night_positive_deficit {perDay recoveryQuota : Nat}
    (hShort : recoveryQuota < perDay) : 0 < nightlyDeficit perDay recoveryQuota := by
  unfold nightlyDeficit
  exact Nat.sub_pos_of_lt hShort

/-! ## 1. One good night clears an acute deficit (reuse SleepDebt spine) -/

/-- **(THM 1) One good night clears acute debt.** An *acute* deficit — one night's
    wake load plus whatever debt was carried in — that is fully covered by the
    night's recovery quota leaves `residualDebt = 0`. A single adequate night
    resolves an acute deficit. This is exactly
    `SleepDebt.full_recovery_clears_residual_debt`, read as sleep recovery. -/
theorem one_good_night_clears_acute_debt {wakeLoad carried recoveryQuota : Nat}
    (hClear : wakeLoad + carried ≤ recoveryQuota) :
    residualDebt wakeLoad carried recoveryQuota = 0 :=
  full_recovery_clears_residual_debt hClear

/-! ## 2. Capacity restored after a full night (reuse SleepDebt spine) -/

/-- **(THM 2) Effective capacity is restored.** After the full night of (1) the
    carried debt is gone, so effective capacity returns to `maxCapacity`: the body
    wakes whole. Reuses `SleepDebt.full_recovery_restores_capacity`. -/
theorem restores_capacity {maxCapacity wakeLoad carried recoveryQuota : Nat}
    (hClear : wakeLoad + carried ≤ recoveryQuota) :
    effectiveCapacity maxCapacity (residualDebt wakeLoad carried recoveryQuota) = maxCapacity :=
  full_recovery_restores_capacity hClear

/-! ## 3. Chronic deprivation accumulates (reuse Allostasis load)

A sustained nightly deficit is an allostatic load that grows with the number of
nights. We measure accumulated sleep debt as `Allostasis.load deficit nights`
(deficit per night, linearly summed). When each night's quota stays below the
daily demand the per-night deficit is fixed and positive, so the accumulation is
monotone in `nights`. -/

/-- **Accumulated sleep debt.** The chronic ledger after `nights` of a fixed
    nightly deficit: `Allostasis.load (nightlyDeficit perDay recoveryQuota) nights`
    — deficit per night, summed linearly over nights. -/
def accumulatedSleepDebt (perDay recoveryQuota nights : Nat) : Nat :=
  load (nightlyDeficit perDay recoveryQuota) nights

/-- **Accumulation is monotone in nights** (the `≤` form, deficit-agnostic). Even
    counting a zero deficit, more deprived nights never means less accumulated
    debt. Reuses `Allostasis.load_monotone`. -/
theorem accumulation_monotone {perDay recoveryQuota n₁ n₂ : Nat} (hNights : n₁ ≤ n₂) :
    accumulatedSleepDebt perDay recoveryQuota n₁ ≤
      accumulatedSleepDebt perDay recoveryQuota n₂ := by
  unfold accumulatedSleepDebt
  exact load_monotone (nightlyDeficit perDay recoveryQuota) n₁ n₂ hNights

/-- **(THM 3) Chronic deprivation accumulates.** In the chronic regime — each
    night's quota strictly below the daily recovery demand, so the per-night
    deficit is genuinely positive — the accumulated sleep debt grows *strictly*
    with the number of nights: strictly more deprived nights means strictly more
    debt (and, weakly, accumulation is monotone). The positivity of the deficit,
    forced by `hShort`, is exactly what turns weak monotonicity into a genuine
    climb. Built from `Allostasis.load` strict-monotonicity in the night count. -/
theorem chronic_deprivation_accumulates {perDay recoveryQuota n₁ n₂ : Nat}
    (hShort : recoveryQuota < perDay) (hNights : n₁ < n₂) :
    accumulatedSleepDebt perDay recoveryQuota n₁ <
      accumulatedSleepDebt perDay recoveryQuota n₂ := by
  unfold accumulatedSleepDebt load
  exact (Nat.mul_lt_mul_left (deprived_night_positive_deficit hShort)).mpr hNights

/-- **Each extra deprived night strictly adds debt.** In the chronic regime the
    per-night deficit is positive, so one more deprived night strictly increases
    the accumulated ledger — accumulation is not just monotone but genuinely
    climbing. (Reuses `SleepDebt.repeated_truncation_strictly_increases_debt` on
    the per-night carry: the carried debt strictly grows when the quota falls
    short of the next night's wake load.) -/
theorem extra_deprived_night_grows_carry {nextWakeLoad carried recoveryQuota : Nat}
    (hShort : recoveryQuota < nextWakeLoad) :
    carried < residualDebt nextWakeLoad carried recoveryQuota :=
  repeated_truncation_strictly_increases_debt hShort

/-! ## 4. Chronic deprivation breaks (bridge to Allostasis.chronic_breaks) -/

/-- **(THM 4) Chronic deprivation breaks the body.** For any fixed positive
    nightly deficit and any tolerance, there is a number of nights after which the
    accumulated sleep debt strictly exceeds the tolerance — the body `breaks`:
    microsleeps, attentional lapses, collapse. The breaking witness is
    `tolerance / deficit + 1` nights. Bridges directly to
    `Allostasis.chronic_breaks`, which supplies exactly this. -/
theorem chronic_deprivation_breaks {perDay recoveryQuota tolerance : Nat}
    (hShort : recoveryQuota < perDay) :
    ∃ nights : Nat, breaks tolerance (accumulatedSleepDebt perDay recoveryQuota nights) := by
  unfold accumulatedSleepDebt
  exact chronic_breaks (nightlyDeficit perDay recoveryQuota) tolerance
    (deprived_night_positive_deficit hShort)

/-! ## 5. The dose makes the poison, for sleep -/

/-- **(THM 5) The dose makes the poison — for sleep.** The headline, sleep
    edition. The *same* nightly deficit is benign acutely and fatal chronically;
    only the dose (the number of nights) differs.

    * (acute) one all-nighter whose wake load plus carried debt is covered by a
      single full night of recovery clears to `residualDebt = 0` — the acute
      deficit resolves (this is `one_good_night_clears_acute_debt`); and any
      acute run of deprived nights whose accumulated debt is within tolerance is
      `withstood`;
    * (chronic) yet the same positive nightly deficit, sustained long enough,
      breaks the body.

    Composes the acute clearance of (1) and the survivability of a short run with
    the chronic breakage of (4). One all-nighter you sleep off; the same deficit
    every night collapses you. -/
theorem the_dose_makes_the_poison_sleep
    {wakeLoad carried recoveryQuota : Nat}
    {perDay tolerance acuteNights : Nat}
    (hClear : wakeLoad + carried ≤ recoveryQuota)
    (hShort : recoveryQuota < perDay)
    (hAcute : accumulatedSleepDebt perDay recoveryQuota acuteNights ≤ tolerance) :
    -- acute: one full night clears the carried debt
    residualDebt wakeLoad carried recoveryQuota = 0 ∧
    -- acute: a short deprived run is still within tolerance, hence withstood
    withstands tolerance (accumulatedSleepDebt perDay recoveryQuota acuteNights) ∧
    -- chronic: the same nightly deficit, sustained, breaks the body
    (∃ chronicNights : Nat,
      breaks tolerance (accumulatedSleepDebt perDay recoveryQuota chronicNights)) :=
  ⟨one_good_night_clears_acute_debt hClear,
   hAcute,
   chronic_deprivation_breaks hShort⟩

/-- **Rest vs ruin, side by side.** A concrete two-dose instance: zero deprived
    nights (`accumulatedSleepDebt … 0 = 0`) is withstood under any tolerance,
    while `tolerance / deficit + 1` deprived nights of the same positive nightly
    deficit break the body. The two endpoints of `the_dose_makes_the_poison_sleep`
    made explicit. -/
theorem rested_withstands_chronic_breaks {perDay recoveryQuota tolerance : Nat}
    (hShort : recoveryQuota < perDay) :
    withstands tolerance (accumulatedSleepDebt perDay recoveryQuota 0) ∧
    breaks tolerance
      (accumulatedSleepDebt perDay recoveryQuota
        (tolerance / nightlyDeficit perDay recoveryQuota + 1)) := by
  unfold accumulatedSleepDebt
  refine ⟨rest_withstands (nightlyDeficit perDay recoveryQuota) tolerance, ?_⟩
  unfold breaks
  exact load_at_witness_exceeds (nightlyDeficit perDay recoveryQuota) tolerance
    (deprived_night_positive_deficit hShort)

/-! ## 6. Sleep grit: the deprived nights tolerated before collapse -/

/-- **Sleep grit.** The maximum number of deprived nights, at a fixed positive
    nightly deficit, the body tolerates before collapse: the integer quotient
    `tolerance / deficit` (`Allostasis.allostaticGrit` for the sleep deficit).
    One more night is exactly the breaking witness of
    `chronic_deprivation_breaks`. -/
def sleepGrit (perDay recoveryQuota tolerance : Nat) : Nat :=
  allostaticGrit (nightlyDeficit perDay recoveryQuota) tolerance

/-- **The grit night is still withstood.** The accumulated debt after exactly
    `sleepGrit` deprived nights stays within tolerance: the body endures right up
    to its sleep grit before cracking. Reuses `Allostasis.grit_load_withstood`. -/
theorem sleep_grit_night_withstood (perDay recoveryQuota tolerance : Nat) :
    withstands tolerance
      (accumulatedSleepDebt perDay recoveryQuota
        (sleepGrit perDay recoveryQuota tolerance)) := by
  unfold accumulatedSleepDebt sleepGrit
  exact grit_load_withstood (nightlyDeficit perDay recoveryQuota) tolerance

/-- **(THM 6) Sleep grit is finite and positive.** For a survivable positive
    nightly deficit — `0 < deficit ≤ tolerance`, i.e. the night falls short
    (`recoveryQuota < perDay`) but a single night's deficit alone does not break
    the body — the body's grit against chronic sleep deprivation is

    * *finite*: it never exceeds `tolerance`, so collapse is inevitable in bounded
      time — there is no infinite reservoir of deprived nights;
    * *positive*: the body can take at least one deprived night before it begins
      to crack.

    Reuses `Allostasis.allostatic_grit` for the nightly sleep deficit. -/
theorem sleep_grit {perDay recoveryQuota tolerance : Nat}
    (hShort : recoveryQuota < perDay)
    (hSurvivable : nightlyDeficit perDay recoveryQuota ≤ tolerance) :
    0 < sleepGrit perDay recoveryQuota tolerance ∧
    sleepGrit perDay recoveryQuota tolerance ≤ tolerance := by
  unfold sleepGrit
  exact allostatic_grit (nightlyDeficit perDay recoveryQuota) tolerance
    (deprived_night_positive_deficit hShort) hSurvivable

/-! ## 7. The headline synthesis -/

/-- **The sleep-resilience principle.** Sleep-debt resilience, proved and composed
    into one theorem so the three pictures are provably one theory:

    * (acute recovery) one full night clears an acute deficit (`residualDebt = 0`)
      and restores effective capacity to `maxCapacity` — you sleep off an
      all-nighter;
    * (the dose) the same positive nightly deficit is *withstood* for a short
      enough run of nights but *breaks* the body for a long enough one — chronic
      sleep deprivation is the acute deficit repeated in time, and the dose (here,
      number of nights) makes the poison;
    * (sleep grit) the body's grit against chronic deprivation is finite (collapse
      is inevitable in bounded time) yet positive (it endures at least one bad
      night).

    Bundled from the spine theorems of `Gnosis.SleepDebt`, `Gnosis.Body.Allostasis`,
    and `Gnosis.Body.Robustness`. -/
theorem sleep_resilience_principle
    {maxCapacity wakeLoad carried recoveryQuota : Nat}
    {perDay tolerance acuteNights : Nat}
    (hClear : wakeLoad + carried ≤ recoveryQuota)
    (hShort : recoveryQuota < perDay)
    (hSurvivable : nightlyDeficit perDay recoveryQuota ≤ tolerance)
    (hAcute : accumulatedSleepDebt perDay recoveryQuota acuteNights ≤ tolerance) :
    -- 1. acute: one good night clears debt and restores capacity
    (residualDebt wakeLoad carried recoveryQuota = 0 ∧
      effectiveCapacity maxCapacity (residualDebt wakeLoad carried recoveryQuota) = maxCapacity) ∧
    -- 2. the dose makes the poison: a short run withstands, a long run breaks
    (withstands tolerance (accumulatedSleepDebt perDay recoveryQuota acuteNights) ∧
      ∃ chronicNights, breaks tolerance (accumulatedSleepDebt perDay recoveryQuota chronicNights)) ∧
    -- 3. sleep grit is finite and positive
    (0 < sleepGrit perDay recoveryQuota tolerance ∧
      sleepGrit perDay recoveryQuota tolerance ≤ tolerance) :=
  ⟨⟨one_good_night_clears_acute_debt hClear, restores_capacity hClear⟩,
   ⟨hAcute, chronic_deprivation_breaks hShort⟩,
   sleep_grit hShort hSurvivable⟩

end Gnosis.Body.SleepResilience
