/-
  EchoChamberAsTaoBowl.lean
  =========================

  Echo chambers read as actual physical chambers — Tao-style bowls
  where the **void** is what makes the vessel function.

  ## The Daoist reading (Daodejing 11)

  > 三十輻共一轂，當其無，有車之用。
  > 埏埴以為器，當其無，有器之用。
  > 鑿戶牖以為室，當其無，有室之用。
  > 故有之以為利，無之以為用。
  >
  > Thirty spokes meet at a hub; the void at its center makes the
  > wheel useful. Clay is shaped into a vessel; the empty space
  > makes it a vessel. Walls are cut for doors and windows; the
  > void makes the room. So form gives benefit; void gives function.

  Translated to a discussion chamber:

  * **Rim** — the voices on the boundary of the chamber (their
    positions, their views).
  * **Void** — the interior empty capacity: room for thought to
    circulate, dissent to breathe, off-mode signals to propagate.
  * **Rigidity** — wall stiffness / consensus tightness — sets the
    fundamental resonant frequency.
  * **Damping** — wall absorption — sets how quickly off-mode
    signals decay.

  The bowl has two opposite failure modes:

  1. **Empty bowl** (no rim): nothing to echo, no boundary, no
     chamber.
  2. **Filled bowl** (no void): nothing can resonate, no room for
     compression, the standing wave cannot form.

  Healthy function lives between the two — both rim and void must
  be non-zero for the bowl to do its job. Daodejing 11 names the
  non-trivial half explicitly: *void gives function*. The
  pejorative-echo-chamber failure is exactly the case where the
  void has been filled with consensus and the bowl loses its
  ability to echo.

  This co-reads with the **standing-wave** echo-chamber model
  (`Gnosis.EchoChamberAsStandingWave`): a high-Q Tao bowl produces
  the locked phase relationship the standing-wave model describes,
  and the bowl reading explains *why* the lock can fail in two
  directions (empty / filled), not just one.

  It also co-reads with **secondary interference**
  (`Gnosis.VibesHotellingVoting.secondaryField`): the bowl's
  fundamental mode is the carrier the aggregate re-radiates onto;
  void preservation is exactly the breathing room that lets the
  field move at all.

  ## What's formalized here

  All scalar fields are `Nat` calibration dials — finite
  bookkeeping, not real-valued physics claims.

  * `TaoBowl` structure with `rim`, `void`, `rigidity`, `damping`.
  * `fundamentalMode`, `qFactor`, `bowlUsefulness`, `freqMismatch`.
  * `IsEmptyBowl`, `IsFilledBowl` — the two failure predicates.
  * Concrete witnesses showing usefulness collapses at both
    extremes and is strictly positive at moderate balance.
  * Resonance / damping behavior: matched signals get amplified by
    Q, off-mode signals get attenuated by damping.
  * `IsPejorativeEchoAt` / `IsPejorativeEcho` — the high-Q failure
    mode that selectively amplifies one frequency and destroys the
    rest (fixed 100-threshold vs arbitrary `q₀`).
  * Bridges to `EchoChamberAsStandingWave` (high-Q ↔ phase-lock)
    and to `SkyrmsUltraLongRunEquilibrium` (filled bowl ↔
    polarization trap; balanced bowl ↔ ULR fixed point).

  Imports `Init`. The bridges import only what they need from
  upstream modules. Zero `sorry`, zero new `axiom`.
-/

import Init
import Gnosis.EchoChamberAsStandingWave
import Gnosis.SkyrmsUltraLongRunEquilibrium

namespace EchoChamberAsTaoBowl

/-! ## The Tao bowl -/

/-- A physical chamber whose function is in its void.

    All scalar fields are finite calibration dials. -/
structure TaoBowl where
  rim : Nat
  void : Nat
  rigidity : Nat
  damping : Nat
  deriving DecidableEq, Repr

/-- **Tao usefulness** — Daodejing 11: the function is in the void.

    Operationalized as `rim × void`: the multiplicative form
    enforces the Daoist reading directly. Either component at
    zero collapses the product; both must be present for the
    bowl to function. The product also grows monotonically when
    rim and void grow together, capturing the "both pillars
    matter" reading. -/
def bowlUsefulness (b : TaoBowl) : Nat :=
  b.rim * b.void

/-- **Fundamental resonant mode.** Higher rigidity and rim density
    push the mode frequency up; bigger void lowers it. A filled
    bowl (void = 0) has no mode at all. -/
def fundamentalMode (b : TaoBowl) : Nat :=
  if b.void = 0 then 0 else (b.rim * b.rigidity) / b.void

/-- **Q factor** — selectivity: high rim/rigidity relative to
    damping yields a sharp resonance. Zero damping is treated as
    "infinitely selective"; we return 0 to keep arithmetic finite,
    and the high-Q regime is exposed via `IsPejorativeEcho` /
    `IsPejorativeEchoAt` instead. -/
def qFactor (b : TaoBowl) : Nat :=
  if b.damping = 0 then 0
  else (b.rim * b.rigidity) / b.damping

/-- Frequency mismatch: distance from the bowl's fundamental mode. -/
def freqMismatch (b : TaoBowl) (f : Nat) : Nat :=
  let m := fundamentalMode b
  if m ≤ f then f - m else m - f

/-- Filtered amplitude after the bowl acts on an external signal:
    matched signals (zero mismatch) are amplified by Q; off-mode
    signals are damped by `damping + 1`. -/
def filteredAmplitude (b : TaoBowl) (f amplitude : Nat) : Nat :=
  if freqMismatch b f = 0 then amplitude * qFactor b
  else amplitude / (b.damping + 1)

/-! ## Two failure modes -/

/-- The empty bowl: no rim, no chamber. -/
def IsEmptyBowl (b : TaoBowl) : Prop := b.rim = 0

/-- The filled bowl: no void, no function. -/
def IsFilledBowl (b : TaoBowl) : Prop := b.void = 0

theorem empty_bowl_dead (b : TaoBowl) (h : IsEmptyBowl b) :
    bowlUsefulness b = 0 := by
  unfold bowlUsefulness IsEmptyBowl at *
  rw [h]
  simp

theorem filled_bowl_dead (b : TaoBowl) (h : IsFilledBowl b) :
    bowlUsefulness b = 0 := by
  unfold bowlUsefulness IsFilledBowl at *
  rw [h]
  simp

/-- **Daodejing 11 punchline:** the filled bowl loses its mode.
    Removing the void destroys the very function the bowl was for. -/
theorem filled_bowl_has_no_mode (b : TaoBowl) (h : IsFilledBowl b) :
    fundamentalMode b = 0 := by
  unfold fundamentalMode IsFilledBowl at *
  rw [h]
  simp

/-- **Either-direction failure:** rim or void zero implies dead bowl. -/
theorem bowl_dead_at_either_extreme (b : TaoBowl)
    (h : IsEmptyBowl b ∨ IsFilledBowl b) :
    bowlUsefulness b = 0 := by
  cases h with
  | inl hEmpty => exact empty_bowl_dead b hEmpty
  | inr hFilled => exact filled_bowl_dead b hFilled

/-! ## Concrete bowls -/

/-- A bowl with no voices on the rim. -/
def emptyBowl : TaoBowl :=
  { rim := 0, void := 5, rigidity := 3, damping := 1 }

/-- A bowl whose interior void has been packed with consensus. -/
def filledBowl : TaoBowl :=
  { rim := 5, void := 0, rigidity := 3, damping := 1 }

/-- A balanced bowl: rim and void in proportion, healthy resonance. -/
def balancedBowl : TaoBowl :=
  { rim := 5, void := 5, rigidity := 3, damping := 1 }

/-- A pejorative echo chamber: rigid walls, scant damping, voids
    sealed by consensus. Q factor balloons; resonance is razor-sharp;
    off-mode signals get crushed. -/
def pejorativeBowl : TaoBowl :=
  { rim := 10, void := 2, rigidity := 100, damping := 1 }

theorem empty_bowl_useless : bowlUsefulness emptyBowl = 0 := by
  unfold bowlUsefulness emptyBowl
  decide

theorem filled_bowl_useless : bowlUsefulness filledBowl = 0 := by
  unfold bowlUsefulness filledBowl
  decide

theorem balanced_bowl_useful : bowlUsefulness balancedBowl > 0 := by
  unfold bowlUsefulness balancedBowl
  decide

theorem balanced_strictly_useful_over_empty :
    bowlUsefulness balancedBowl > bowlUsefulness emptyBowl := by
  unfold bowlUsefulness balancedBowl emptyBowl
  decide

theorem balanced_strictly_useful_over_filled :
    bowlUsefulness balancedBowl > bowlUsefulness filledBowl := by
  unfold bowlUsefulness balancedBowl filledBowl
  decide

/-! ## Resonance / damping behavior -/

/-- The balanced bowl has a definite, finite resonant mode. -/
theorem balanced_bowl_mode_value :
    fundamentalMode balancedBowl = 3 := by
  unfold fundamentalMode balancedBowl
  decide

/-- A signal at the bowl's fundamental mode has zero mismatch. -/
theorem on_mode_signal_has_zero_mismatch :
    freqMismatch balancedBowl 3 = 0 := by
  unfold freqMismatch fundamentalMode balancedBowl
  decide

/-- An on-mode signal gets amplified by the bowl's Q factor. -/
theorem on_mode_signal_is_amplified :
    filteredAmplitude balancedBowl 3 1 = qFactor balancedBowl := by
  unfold filteredAmplitude freqMismatch fundamentalMode balancedBowl
  decide

/-- An off-mode signal gets attenuated by the damping term. -/
theorem off_mode_signal_is_damped :
    filteredAmplitude balancedBowl 10 100 < 100 := by
  unfold filteredAmplitude freqMismatch fundamentalMode balancedBowl qFactor
  decide

/-! ## The pejorative echo chamber: high-Q failure -/

/-- A bowl whose finite calibration Q meets or exceeds `q₀`. -/
def IsPejorativeEchoAt (b : TaoBowl) (q₀ : Nat) : Prop :=
  qFactor b ≥ q₀

/-- A bowl with Q ≥ 100: razor-sharp resonance, near-total damping
    of off-mode signals. This is the failure mode the colloquial
    phrase "echo chamber" usually points at. -/
def IsPejorativeEcho (b : TaoBowl) : Prop :=
  IsPejorativeEchoAt b 100

theorem is_pejorative_echo_at_iff (b : TaoBowl) :
    IsPejorativeEcho b ↔ IsPejorativeEchoAt b 100 :=
  Iff.rfl

theorem pejorative_bowl_is_high_q :
    IsPejorativeEcho pejorativeBowl := by
  unfold IsPejorativeEcho IsPejorativeEchoAt qFactor pejorativeBowl
  decide

/-- The pejorative bowl over-amplifies its on-mode signal: a unit
    input at the fundamental returns at amplitude ≥ 100. -/
theorem pejorative_bowl_over_amplifies :
    filteredAmplitude pejorativeBowl (fundamentalMode pejorativeBowl) 1 ≥ 100 := by
  unfold filteredAmplitude freqMismatch qFactor pejorativeBowl
  decide

/-! ### Q thresholds: damping = 0 and monotonicity

When `damping = 0`, `qFactor` is pinned to `0` (finite sentinel); all
`IsPejorativeEchoAt` claims with positive `q₀` are then false. With
`0 < damping`, `qFactor` is monotone in `rim` and `rigidity` when the
other structural fields match. Lowering the threshold weakens the
predicate. -/

theorem qFactor_eq_zero_of_damping_eq_zero (b : TaoBowl) (hd : b.damping = 0) :
    qFactor b = 0 := by
  unfold qFactor
  rw [hd]
  simp

theorem qFactor_mono_rim {b b' : TaoBowl} (_ : b.void = b'.void)
    (hrig : b.rigidity = b'.rigidity) (hdmp : b.damping = b'.damping)
    (hdpos : 0 < b.damping) (hrle : b.rim ≤ b'.rim) :
    qFactor b ≤ qFactor b' := by
  have h0 : ¬ b.damping = 0 := Nat.ne_of_gt hdpos
  have h0' : ¬ b'.damping = 0 := by
    intro hbad
    exact h0 (hdmp.trans hbad)
  unfold qFactor
  simp only [if_neg h0, if_neg h0']
  have hun : b.rim * b.rigidity ≤ b'.rim * b'.rigidity := by
    calc
      b.rim * b.rigidity ≤ b'.rim * b.rigidity := Nat.mul_le_mul_right b.rigidity hrle
      _ = b'.rim * b'.rigidity := by rw [hrig]
  rw [hdmp]
  exact Nat.div_le_div_right hun

theorem qFactor_mono_rigidity {b b' : TaoBowl} (_ : b.void = b'.void)
    (hrim : b.rim = b'.rim) (hdmp : b.damping = b'.damping)
    (hdpos : 0 < b.damping) (hrle : b.rigidity ≤ b'.rigidity) :
    qFactor b ≤ qFactor b' := by
  have h0 : ¬ b.damping = 0 := Nat.ne_of_gt hdpos
  have h0' : ¬ b'.damping = 0 := by
    intro hbad
    exact h0 (hdmp.trans hbad)
  unfold qFactor
  simp only [if_neg h0, if_neg h0']
  have hun : b.rim * b.rigidity ≤ b'.rim * b'.rigidity := by
    calc
      b.rim * b.rigidity ≤ b.rim * b'.rigidity := Nat.mul_le_mul_left b.rim hrle
      _ = b'.rim * b'.rigidity := by rw [hrim]
  rw [hdmp]
  exact Nat.div_le_div_right hun

theorem is_pejorative_echo_at_of_le_threshold {b : TaoBowl} {q₀ q₁ : Nat}
    (h : IsPejorativeEchoAt b q₀) (hle : q₁ ≤ q₀) : IsPejorativeEchoAt b q₁ := by
  unfold IsPejorativeEchoAt at *
  exact Nat.le_trans hle h

/-! ## Bridge: high-Q bowl induces a standing-wave-shaped chamber

The standing-wave reading
(`Gnosis.EchoChamberAsStandingWave.is_standing_wave`) requires
phase-locked members at a single frequency with high coherence.
A pejorative high-Q Tao bowl is exactly the regime that produces
that lock: the resonance picks one mode and damps everything else,
so any persistent population of voices on the rim ends up
phase-aligned with the mode. -/

open EchoChamberAsStandingWave (EchoChamber)

/-- Convert a bowl plus a list of phase-locked voices into the
    standing-wave chamber the existing module expects. The center
    frequency is the bowl's fundamental mode; coherence is `100`
    when the bowl is in the high-Q (pejorative) regime, `50`
    otherwise. -/
def chamberOfBowl (b : TaoBowl)
    (members : List OpinionAsInterference.OpinionWave) : EchoChamber where
  members := members
  center_position := 0
  center_frequency := fundamentalMode b
  center_phase := 0
  coherence := if qFactor b ≥ 100 then 100 else 50

theorem pejorative_bowl_chamber_high_coherence
    (members : List OpinionAsInterference.OpinionWave) :
    (chamberOfBowl pejorativeBowl members).coherence = 100 := by
  unfold chamberOfBowl
  show (if qFactor pejorativeBowl ≥ 100 then 100 else 50) = 100
  unfold qFactor pejorativeBowl
  decide

/-! ## Bridge: bowl polarization mirrors the Skyrms polarization trap

The polarization trap of `Gnosis.SkyrmsUltraLongRunEquilibrium`
is the case where the population sits at mutual extremes with no
shared interior. In bowl vocabulary, that *is* the filled-bowl
failure: the rim has saturated, the void has been squeezed out,
and the chamber can no longer move. The Skyrms ULR fixed point
is the balanced bowl: rim and void in proportion, the mode is
at the median, joint welfare is high, and re-radiation continues
to flow.
-/

/-- The polarization trap as a bowl: rim and void inverted from
    the balanced configuration. -/
def polarizationTrapAsBowl : TaoBowl :=
  { rim := 10, void := 0, rigidity := 3, damping := 1 }

/-- The Skyrms ULR fixed point as a bowl: balanced rim and void. -/
def skyrmsUltraLongRunAsBowl : TaoBowl :=
  { rim := 5, void := 5, rigidity := 3, damping := 1 }

theorem polarization_trap_is_filled_bowl :
    IsFilledBowl polarizationTrapAsBowl := by
  unfold IsFilledBowl polarizationTrapAsBowl
  rfl

theorem polarization_trap_is_dead_bowl :
    bowlUsefulness polarizationTrapAsBowl = 0 :=
  filled_bowl_dead polarizationTrapAsBowl polarization_trap_is_filled_bowl

theorem skyrms_ulr_bowl_is_useful :
    bowlUsefulness skyrmsUltraLongRunAsBowl > 0 := by
  unfold bowlUsefulness skyrmsUltraLongRunAsBowl
  decide

theorem ulr_bowl_strictly_useful_over_polarization_trap :
    bowlUsefulness skyrmsUltraLongRunAsBowl
      > bowlUsefulness polarizationTrapAsBowl := by
  unfold bowlUsefulness skyrmsUltraLongRunAsBowl polarizationTrapAsBowl
  decide

/-! ## Honesty note

The Tao bowl is a calibration sketch, not a physical claim. The
multiplicative `bowlUsefulness = rim × void` captures the Daoist
asymmetry (both pillars must be non-zero) but does not encode
non-trivial peak-at-balance dynamics — for that we would need
either a `min`-based formulation or a real-valued harmonic-mean
treatment. The two failure modes (`empty_bowl_dead`,
`filled_bowl_dead`) are the structurally honest piece: removing
either rim or void destroys function, exactly as Daodejing 11
names. The bridges to `EchoChamberAsStandingWave` and to
`SkyrmsUltraLongRunEquilibrium` keep the bowl reading aligned
with the existing wave-mechanical and game-theoretic ledgers
without claiming an identity between them.
-/

end EchoChamberAsTaoBowl
