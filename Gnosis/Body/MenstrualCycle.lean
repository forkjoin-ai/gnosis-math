import Init

/-!
# The Menstrual Cycle — A Robust Infradian Oscillator on the Gnosis Clock

The Lean counterpart of the project's circadian/infradian rhythm thread. Where
`Gnosis.Circadian` formalizes the ~24h *circadian* dial and
`Gnosis.GnosisTimeClock` the twelve-phase aeon dial, this module formalizes the
human **menstrual cycle** as an *infradian* (slower-than-a-day) oscillator: a
healthy, **sustained**, **self-restoring** rhythm that closes on itself every
`period` days.

The clinical-neutral framing throughout is that of a *living, sustained cycle*:
the recurring period-`period` orbit is the signature of an intact infradian
rhythm — the counterpoint to a *collapsed* cycle (a rhythm that fails to return,
the dynamical picture of e.g. amenorrhea or the flattened diurnal/affective
rhythms studied elsewhere in `Gnosis.Body`). Nothing here diagnoses; it records
the mathematics of a rhythm that returns.

The carrier is `cyclePhase day := day % period`, mirroring the `% twelve`
construction of `Gnosis.GnosisTimeClock.phaseOfNatTick` and the `% aeon`
identifications of `Gnosis.CircadianGnosisAlignment` — re-derived here from pure
`Nat` so the module needs no GnosisTime import. Four ordered named phases
(menstrual, follicular, ovulation, luteal) partition the dial.

The arc, as theorems:

1. **The cycle closes** (`cycle_closes`): `cyclePhase (day + period) = cyclePhase day`.
   After a full period the dial returns — a sustained, closed oscillation. (Via
   `Nat.add_mod` / `Nat.mod_self`.)
2. **The phase is bounded** (`phase_is_bounded`): `cyclePhase day < period` for
   `period > 0` — the phase always lies on the dial. (Via `Nat.mod_lt`.)
3. **The phases are exhaustive and exclusive** (`phases_are_exhaustive`,
   `phase_is_unique`): every day falls in exactly one of the four phases — a
   quadrichotomy over the period.
4. **Re-entrainment after perturbation** (`reentrains_after_perturbation`): a
   phase shift `s` (stress, travel, illness) merely rotates the dial; the cycle
   still re-closes after a full period regardless of `s` — infradian resilience.
5. **Period relates to the aeon** (`period_relates_to_aeon`): with `period = 28`
   and the Gnosis aeon `12`, `28 = 2 * 12 + 4` — a clean honest Nat bridge to the
   twelve-phase clock.
6. **Headline** (`menstrual_cycle_is_a_robust_oscillator`): closure +
   boundedness + re-entrainment, composed — the cycle is a sustained,
   self-restoring infradian oscillation.

Rustic Church: `import Init` only. `Nat` only (a `Fin 4` phase tag for the dial),
no Float/Real, no Mathlib, no `sorry`, no `simp`/`decide`/`omega` on open goals —
term-mode and named core `Nat` lemmas throughout.
-/

namespace Gnosis.Body.MenstrualCycle

/-! ## 0. The dial: the cyclic phase

The cycle has `period` days. The canonical human cycle is ~28 days; we fix
`period := 28` (the boundaries below assume this concrete period), but the
*cyclic-structure* theorems (`cycle_closes`, `phase_is_bounded`,
`reentrains_after_perturbation`) hold for the abstract `% period` construction
and are stated over a `period`-parameter where the proof does not need the value.
-/

/-- The canonical period of the human cycle, in days. The dial has `period`
    positions; the cycle closes after exactly this many days. -/
def period : Nat := 28

/-- `period` is positive — there is a dial to turn. -/
theorem period_pos : 0 < period := Nat.zero_lt_succ _

/-- **The cyclic phase.** Where on the cycle a given `day` falls: `day` reduced
    modulo the period. This is the infradian counterpart of
    `GnosisTimeClock.phaseOfNatTick` (`m % twelve`) and the `% aeon`
    identifications of `CircadianGnosisAlignment`, re-derived from pure `Nat`. -/
def cyclePhase (day : Nat) : Nat := day % period

/-! ## 1. The cycle closes — a sustained, returning oscillation

The defining property of a *healthy, sustained* rhythm: it returns. After a full
period the phase is exactly where it began. This is the dynamical opposite of a
collapsed cycle (one that fails to return). -/

/-- **(THM 1) The cycle closes.** After one full period the cyclic phase returns
    to its starting value: `cyclePhase (day + period) = cyclePhase day`. The dial
    is *closed* — the rhythm is sustained, not run-down. Proved generically via
    `Nat.add_mod` and `Nat.mod_self`, so it holds for any modulus. -/
theorem cycle_closes (day : Nat) : cyclePhase (day + period) = cyclePhase day := by
  unfold cyclePhase
  rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

/-- **The cycle closes after any whole number of periods.** Adding `k` complete
    periods leaves the phase unchanged — the oscillation persists indefinitely,
    cycle after cycle, never drifting off the dial. -/
theorem cycle_closes_after_k_periods (day k : Nat) :
    cyclePhase (day + k * period) = cyclePhase day := by
  unfold cyclePhase
  rw [Nat.add_mul_mod_self_right]

/-! ## 2. The phase is bounded — it always lies on the dial -/

/-- **(THM 2) The phase is bounded.** The cyclic phase always lies strictly below
    the period: it is a genuine position on the dial, never off it. Via
    `Nat.mod_lt`, exactly as `phaseOfNatTick` lands in `Fin twelve`. -/
theorem phase_is_bounded (day : Nat) : cyclePhase day < period := by
  unfold cyclePhase
  exact Nat.mod_lt day period_pos

/-! ## 3. The four phases partition the cycle

The cycle has four ordered, biologically named segments. With `period = 28` the
canonical day-boundaries are:

* **menstrual**  : days `[0, 5)`   — `cyclePhase < 5`
* **follicular** : days `[5, 13)`  — `5 ≤ cyclePhase < 13`
* **ovulation**  : days `[13, 17)` — `13 ≤ cyclePhase < 17`
* **luteal**     : days `[17, 28)` — `17 ≤ cyclePhase`

These tile the dial: every day is in exactly one phase (`phases_are_exhaustive`,
`phase_is_unique`). The exact boundaries are conventional; the *partition* is the
content. -/

/-- The four named phases of the cycle, in order — a `Fin 4` phase dial. -/
inductive Phase where
  | menstrual    -- shedding; the cycle's start
  | follicular   -- follicle maturation
  | ovulation    -- release
  | luteal       -- post-ovulatory
  deriving DecidableEq, Repr

/-- Boundary day where the follicular phase begins (`= 5`). -/
def follicularStart : Nat := 5
/-- Boundary day where the ovulation phase begins (`= 13`). -/
def ovulationStart : Nat := 13
/-- Boundary day where the luteal phase begins (`= 17`). -/
def lutealStart : Nat := 17

/-- **The phase classifier.** Total: classifies any day's cyclic phase into
    exactly one of the four named segments by its position on the dial. Because
    `cyclePhase day < period` and the boundaries are ordered, the four arms are
    exhaustive and mutually exclusive. -/
def phaseOf (day : Nat) : Phase :=
  let p := cyclePhase day
  if p < follicularStart then Phase.menstrual
  else if p < ovulationStart then Phase.follicular
  else if p < lutealStart then Phase.ovulation
  else Phase.luteal

/-- Membership predicate: the cyclic phase lies in the day-range owned by `ph`.
    Each phase owns a half-open interval `[lo, hi)` of the dial; the menstrual
    arm owns `[0, follicularStart)`, the luteal arm `[lutealStart, period)`. -/
def inPhase (ph : Phase) (day : Nat) : Prop :=
  let p := cyclePhase day
  match ph with
  | Phase.menstrual  => p < follicularStart
  | Phase.follicular => follicularStart ≤ p ∧ p < ovulationStart
  | Phase.ovulation  => ovulationStart ≤ p ∧ p < lutealStart
  | Phase.luteal     => lutealStart ≤ p

/-- The classifier agrees with membership: `phaseOf day` is a phase the day is
    genuinely in. (Establishes existence half of the partition.) -/
theorem phaseOf_mem (day : Nat) : inPhase (phaseOf day) day := by
  unfold phaseOf inPhase
  by_cases h0 : cyclePhase day < follicularStart
  · rw [if_pos h0]; exact h0
  · rw [if_neg h0]
    by_cases h1 : cyclePhase day < ovulationStart
    · rw [if_pos h1]
      exact ⟨Nat.le_of_not_lt h0, h1⟩
    · rw [if_neg h1]
      by_cases h2 : cyclePhase day < lutealStart
      · rw [if_pos h2]
        exact ⟨Nat.le_of_not_lt h1, h2⟩
      · rw [if_neg h2]
        exact Nat.le_of_not_lt h2

/-- **(THM 3a) The phases are exhaustive.** Every day falls in at least one of the
    four named phases — the four segments cover the entire dial, leaving no day
    unclassified. (`phaseOf` always returns a phase the day is in.) -/
theorem phases_are_exhaustive (day : Nat) :
    inPhase Phase.menstrual day ∨ inPhase Phase.follicular day ∨
    inPhase Phase.ovulation day ∨ inPhase Phase.luteal day := by
  unfold inPhase
  by_cases h0 : cyclePhase day < follicularStart
  · exact Or.inl h0
  · by_cases h1 : cyclePhase day < ovulationStart
    · exact Or.inr (Or.inl ⟨Nat.le_of_not_lt h0, h1⟩)
    · by_cases h2 : cyclePhase day < lutealStart
      · exact Or.inr (Or.inr (Or.inl ⟨Nat.le_of_not_lt h1, h2⟩))
      · exact Or.inr (Or.inr (Or.inr (Nat.le_of_not_lt h2)))

/-- The phase boundaries are ordered: `follicularStart ≤ ovulationStart`
    (`5 ≤ 13`). Term-mode, no `decide`. -/
theorem follicularStart_le_ovulationStart : follicularStart ≤ ovulationStart :=
  Nat.le.intro (k := 8) rfl

/-- `ovulationStart ≤ lutealStart` (`13 ≤ 17`). -/
theorem ovulationStart_le_lutealStart : ovulationStart ≤ lutealStart :=
  Nat.le.intro (k := 4) rfl

/-- `follicularStart ≤ lutealStart` (`5 ≤ 17`), by transitivity of the two above. -/
theorem follicularStart_le_lutealStart : follicularStart ≤ lutealStart :=
  Nat.le_trans follicularStart_le_ovulationStart ovulationStart_le_lutealStart

/-- The single arithmetic shape behind exclusivity: a phase point cannot be both
    strictly below a lower boundary `a` and at-or-above a higher boundary `b ≥ a`.
    Used to contradict every cross-phase pair. -/
theorem cannot_be_below_and_above {p a b : Nat}
    (hlo : a ≤ b) (hbelow : p < a) (habove : b ≤ p) : False :=
  Nat.lt_irrefl p (Nat.lt_of_lt_of_le hbelow (Nat.le_trans hlo habove))

/-- **(THM 3b) The phase is unique.** No day lies in two different phases at once:
    the four intervals are pairwise disjoint. Stated as: whenever a day is in two
    phases, those phases are equal. Together with `phases_are_exhaustive` this is
    the full quadrichotomy — every day is in *exactly* one phase. The ordered
    boundaries (`follicularStart ≤ ovulationStart ≤ lutealStart`) make each
    cross-pair a `Nat` order clash via `cannot_be_below_and_above`. -/
theorem phase_is_unique (day : Nat) (ph₁ ph₂ : Phase)
    (h₁ : inPhase ph₁ day) (h₂ : inPhase ph₂ day) : ph₁ = ph₂ := by
  unfold inPhase at h₁ h₂
  cases ph₁ <;> cases ph₂ <;>
    first
      | rfl
      -- menstrual (p < 5) vs a higher phase (lower bound ≥ 5)
      | exact (cannot_be_below_and_above (Nat.le_refl _) h₁ h₂.1).elim
      | exact (cannot_be_below_and_above (Nat.le_refl _) h₂ h₁.1).elim
      | exact (cannot_be_below_and_above follicularStart_le_ovulationStart h₁ h₂.1).elim
      | exact (cannot_be_below_and_above follicularStart_le_ovulationStart h₂ h₁.1).elim
      | exact (cannot_be_below_and_above follicularStart_le_lutealStart h₁ h₂).elim
      | exact (cannot_be_below_and_above follicularStart_le_lutealStart h₂ h₁).elim
      -- follicular (p < 13) vs ovulation/luteal (lower bound ≥ 13)
      | exact (cannot_be_below_and_above (Nat.le_refl _) h₁.2 h₂.1).elim
      | exact (cannot_be_below_and_above (Nat.le_refl _) h₂.2 h₁.1).elim
      | exact (cannot_be_below_and_above ovulationStart_le_lutealStart h₁.2 h₂).elim
      | exact (cannot_be_below_and_above ovulationStart_le_lutealStart h₂.2 h₁).elim
      -- ovulation (p < 17) vs luteal (lower bound ≥ 17)
      | exact (cannot_be_below_and_above (Nat.le_refl _) h₁.2 h₂).elim
      | exact (cannot_be_below_and_above (Nat.le_refl _) h₂.2 h₁).elim

/-! ## 4. Re-entrainment after perturbation — infradian resilience

Stress, travel, or illness can *shift* the cycle by some number of days `s`. The
robust-oscillator claim is that such a shift only **rotates the dial**: it does
not break the rhythm. Whatever the perturbation, the cycle still re-closes after
a full period — the hallmark of a sustained, self-restoring oscillation. -/

/-- **(THM 4) Re-entrainment after perturbation.** A phase shift `s` (stress,
    travel, illness) merely rotates the dial: after the shift, waiting one full
    period restores the shifted phase exactly. The cycle re-closes *regardless of
    the perturbation* — infradian resilience. This is `cycle_closes` applied at
    the perturbed day `day + s`. -/
theorem reentrains_after_perturbation (day s : Nat) :
    cyclePhase ((day + s) + period) = cyclePhase (day + s) :=
  cycle_closes (day + s)

/-- **Re-entrainment is total over perturbations.** *For every* shift `s`, the
    perturbed cycle still closes after a full period — the resilience is not
    contingent on the size or kind of the perturbation. -/
theorem reentrains_for_all_perturbations (day : Nat) :
    ∀ s : Nat, cyclePhase ((day + s) + period) = cyclePhase (day + s) :=
  fun s => reentrains_after_perturbation day s

/-- **A perturbed cycle remains on the dial.** Even after an arbitrary shift the
    phase stays a genuine dial position — the perturbation rotates but never
    ejects the rhythm. -/
theorem perturbed_phase_is_bounded (day s : Nat) : cyclePhase (day + s) < period :=
  phase_is_bounded (day + s)

/-! ## 5. The aeon bridge — the period in twelve-phase units

A small, honest arithmetic bridge from the 28-day cycle to the Gnosis aeon
(`twelve`, the modulus of `GnosisTimeClock` and `Circadian.aeon`): the cycle
spans two full aeons plus a remainder of four. No structural claim — just the
clean Nat decomposition. -/

/-- The Gnosis aeon modulus (the `twelve` of `GnosisTimeClock`, the `aeon` of
    `Circadian`), recorded locally to keep this module Init-clean. -/
def aeon : Nat := 12

/-- **(THM 5) The period relates to the aeon.** The 28-day cycle is exactly two
    aeons plus four: `28 = 2 * 12 + 4`. A clean Nat identity bridging the
    infradian dial to the twelve-phase Gnosis clock. -/
theorem period_relates_to_aeon : period = 2 * aeon + 4 := rfl

/-- The cycle's remainder against the aeon dial: `28 % 12 = 4`. The cycle does not
    tile the aeon evenly — its overhang is exactly the Gnosis `kenoma`-minus-six /
    four-day sliver, recorded as an honest residue rather than forced to zero. -/
theorem period_mod_aeon : period % aeon = 4 := rfl

/-! ## 6. The headline synthesis -/

/-- **The menstrual cycle is a robust oscillator.** The infradian counterpart of
    the project's circadian theorems, composed: the cycle is a *sustained*,
    *self-restoring* oscillation on its dial. For every day and every
    perturbation `s`:

    * (closure) the cycle returns after a full period — a sustained, closed
      oscillation that never runs down (`cyclePhase (day + period) = cyclePhase day`);
    * (boundedness) the phase always lies on the dial — it never leaves
      (`cyclePhase day < period`);
    * (re-entrainment) any perturbation merely rotates the dial; the cycle still
      re-closes after a full period — resilience that does not depend on the
      shift (`cyclePhase ((day + s) + period) = cyclePhase (day + s)`);
    * (partition) every day falls in exactly one of the four named phases.

    Bundled so the four pictures are provably one rhythm. Clinical-neutral: this
    is the mathematics of a *living, returning* cycle — health as the sustained
    oscillation, the counterpoint to a collapsed one. -/
theorem menstrual_cycle_is_a_robust_oscillator (day s : Nat) :
    -- 1. closure: a sustained, returning oscillation
    cyclePhase (day + period) = cyclePhase day ∧
    -- 2. boundedness: always on the dial
    cyclePhase day < period ∧
    -- 3. re-entrainment: any perturbation only rotates the dial
    cyclePhase ((day + s) + period) = cyclePhase (day + s) ∧
    -- 4. partition: every day is in exactly one phase
    (inPhase Phase.menstrual day ∨ inPhase Phase.follicular day ∨
      inPhase Phase.ovulation day ∨ inPhase Phase.luteal day) :=
  ⟨cycle_closes day,
   phase_is_bounded day,
   reentrains_after_perturbation day s,
   phases_are_exhaustive day⟩

end Gnosis.Body.MenstrualCycle
