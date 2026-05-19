import Init

/-
  HiroshimaRepetitionTraumaWitness.lean
  =====================================

  Hiroshima / hibakusha testimony as repetition-trauma witness: memory fails
  not by absence, but by replay that cannot yet be integrated.

  Cultural floor: survivor testimony, memorial photography, shadows, ruins,
  and recurring public narration are treated here as the operator register.
  The witness is not "too little evidence." It is evidence returning again and
  again while action, mourning, and political comprehension lag behind it.

  Formal reading in this repository:

  * repetition trauma maps to `repetitionPreventsIntegration`.
  * witness burden maps to `testimonyRepeatsBeforeMetabolized`.
  * machine failure maps to `destructiveTechnologyOutrunsMoralFrame`.

  This file does not prove a theory of nuclear history. It names the categorical
  failure: replay alone is not integration.

  Repo cousins: `GoyaSleepOfReasonWitness` (nightmare when reason idles);
  `BaconVelazquezPopeStudiesWitness` (body under modern pressure);
  `MagritteTheSurvivorWitness` (guilt transferred onto hardware);
  `TraumaSpectralSieve`; `TraumaAsStandingWave`.

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace HiroshimaRepetitionTraumaWitness

/-- Tag: repetition blocks integration rather than completing memory. -/
abbrev repetitionPreventsIntegration (claim : Prop) : Prop :=
  claim

/-- Tag: testimony repeats before the public system metabolizes it. -/
abbrev testimonyRepeatsBeforeMetabolized (claim : Prop) : Prop :=
  claim

/-- Tag: destructive technology outruns available moral frame. -/
abbrev destructiveTechnologyOutrunsMoralFrame (claim : Prop) : Prop :=
  claim

/--
  Repetition trauma bundle: replay + unmet metabolism + moral scale lag.
-/
structure RepetitionTraumaWitness (replay testimony frame : Prop) where
  replayStuck : repetitionPreventsIntegration replay
  witnessBurden : testimonyRepeatsBeforeMetabolized testimony
  frameLag : destructiveTechnologyOutrunsMoralFrame frame

theorem repetition_trauma_conjuncts
    (R T F : Prop) (w : RepetitionTraumaWitness R T F) : R ∧ T ∧ F :=
  And.intro w.replayStuck (And.intro w.witnessBurden w.frameLag)

def buildRepetitionTraumaWitness
    (R T F : Prop) (hR : R) (hT : T) (hF : F) : RepetitionTraumaWitness R T F :=
  ⟨hR, hT, hF⟩

end HiroshimaRepetitionTraumaWitness
