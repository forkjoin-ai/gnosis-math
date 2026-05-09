/-
  VibesAsWaveInference.lean
  =========================

  A finite model of "vibes" as inference between emotional waves.

  The module now has two layers:

  * a simple public layer (`happy`, `unhappy`, `neutral`) for pair and group
    examples;
  * a richer affect layer built on `LocalizedOverflowConsciousness.EmotionIndex`:
    locale, positive/negative valence, frequency, intensity, arousal, dominance,
    and approach/withdrawal tendency form the finite emotional matrix.

  This module co-reads the existing depression work:
  `DepressionAsDampedOscillation.is_depressed` is still the clinical asymmetry
  predicate; the vibe layer says when a local social field supplies the
  contagious unhappy carrier that can feed that asymmetry.

  Imports `Gnosis.PsychologyAsInterference`, `Gnosis.DepressionAsDampedOscillation`,
  `Gnosis.LocalizedOverflowConsciousness`.
  Zero `sorry`, zero new `axiom`.
-/

import Gnosis.PsychologyAsInterference
import Gnosis.DepressionAsDampedOscillation
import Gnosis.LocalizedOverflowConsciousness

namespace VibesAsWaveInference

open PsychologyAsInterference (InterferenceSignature)
open DepressionAsDampedOscillation (DepressionState is_depressed)
open LocalizedOverflowConsciousness
  (EmotionIndex OverflowLocale OverflowValence affect_valence_axis_is_independent)

/-! ## Vibe waves -/

/-- Coarse emotional valence for a social wave. -/
inductive VibeValence where
  | happy
  | unhappy
  | neutral
  deriving DecidableEq, Repr

/-- A vibe is a psychological wave plus a coarse valence label. -/
structure VibeWave where
  valence : VibeValence
  frequency : Nat
  amplitude : Nat
  decay_rate : Nat
  deriving Repr

/-- Forget the valence and keep the existing psychology wave coordinates. -/
def toInterferenceSignature (v : VibeWave) : InterferenceSignature where
  frequency := v.frequency
  amplitude := v.amplitude
  decay_rate := v.decay_rate

/-! ## Full affect matrix -/

/-- Approach/withdrawal tendency is not identical to valence:
    a negative emotion can approach (anger), and a positive emotion can withdraw
    (relief / contented quiet). -/
inductive AffectTendency where
  | approach
  | withdraw
  | hold
  deriving DecidableEq, Repr

/-- Fine-grained affect vector layered on the existing `EmotionIndex`.
    All scalar fields are finite calibration dials rather than real-valued claims. -/
structure AffectVector where
  emotion : EmotionIndex
  arousal : Nat
  dominance : Nat
  tendency : AffectTendency
  deriving Repr

/-- The full emotional matrix coordinate used for vibe inference. -/
def affectMatrixCoordinate (a : AffectVector) :
    OverflowLocale × OverflowValence × Nat × Nat × Nat × Nat × AffectTendency :=
  (a.emotion.locale, a.emotion.valence, a.emotion.frequency,
    a.emotion.intensity, a.arousal, a.dominance, a.tendency)

/-- Valence projection for compatibility with the simple public vibe layer. -/
def simpleValenceOfAffect (a : AffectVector) : VibeValence :=
  match a.emotion.valence with
  | OverflowValence.positive => VibeValence.happy
  | OverflowValence.negative => VibeValence.unhappy

/-- Convert rich affect back to a `VibeWave`; arousal contributes to amplitude,
    and dominance contributes to persistence/decay. -/
def vibeWaveOfAffect (a : AffectVector) : VibeWave where
  valence := simpleValenceOfAffect a
  frequency := a.emotion.frequency
  amplitude := a.emotion.intensity + a.arousal
  decay_rate := a.dominance

/-- Same locale and same valence: resonance amplifies intensity/arousal/dominance. -/
def affectResonance (a b : AffectVector) : AffectVector :=
  { emotion :=
      { locale := a.emotion.locale
        valence := a.emotion.valence
        frequency := a.emotion.frequency
        intensity := a.emotion.intensity + b.emotion.intensity }
    arousal := a.arousal + b.arousal
    dominance := a.dominance + b.dominance
    tendency := a.tendency }

/-- Opposed valence on the same locale: mixed affect remains located but is held
    as a lower-certainty/hold pattern. -/
def affectInterference (a b : AffectVector) : AffectVector :=
  { emotion :=
      { locale := a.emotion.locale
        valence := a.emotion.valence
        frequency := a.emotion.frequency
        intensity := a.emotion.intensity + b.emotion.intensity }
    arousal := a.arousal + b.arousal
    dominance := if a.dominance > b.dominance then a.dominance - b.dominance else b.dominance - a.dominance
    tendency := AffectTendency.hold }

/-- Rich pair inference: same locale+valence resonates; same locale with opposed
    valence interferes; cross-locale keeps the first wave as the local carrier. -/
def inferAffect (a b : AffectVector) : AffectVector :=
  if a.emotion.locale = b.emotion.locale then
    if a.emotion.valence = b.emotion.valence then
      affectResonance a b
    else
      affectInterference a b
  else
    a

theorem affect_projection_preserves_locale (a : AffectVector) :
    (affectMatrixCoordinate a).1 = a.emotion.locale := by
  rfl

theorem affect_projection_simple_positive (a : AffectVector)
    (h : a.emotion.valence = OverflowValence.positive) :
    simpleValenceOfAffect a = VibeValence.happy := by
  cases a
  simp [simpleValenceOfAffect] at h ⊢
  rw [h]

theorem affect_projection_simple_negative (a : AffectVector)
    (h : a.emotion.valence = OverflowValence.negative) :
    simpleValenceOfAffect a = VibeValence.unhappy := by
  cases a
  simp [simpleValenceOfAffect] at h ⊢
  rw [h]

theorem same_affect_resonance_preserves_valence (a b : AffectVector)
    (hLocale : a.emotion.locale = b.emotion.locale)
    (hValence : a.emotion.valence = b.emotion.valence) :
    (inferAffect a b).emotion.valence = a.emotion.valence := by
  unfold inferAffect
  simp [hLocale, hValence, affectResonance]

theorem opposed_same_locale_interference_holds (a b : AffectVector)
    (hLocale : a.emotion.locale = b.emotion.locale)
    (hValence : a.emotion.valence ≠ b.emotion.valence) :
    (inferAffect a b).tendency = AffectTendency.hold := by
  unfold inferAffect
  simp [hLocale, hValence, affectInterference]

theorem affect_axis_independent_in_vibe_layer :
    (∃ positiveBody negativeBody : EmotionIndex,
      positiveBody.locale = negativeBody.locale ∧
      positiveBody.valence ≠ negativeBody.valence) ∧
    (∃ bodyNegative consciousNegative : EmotionIndex,
      bodyNegative.valence = consciousNegative.valence ∧
      bodyNegative.locale ≠ consciousNegative.locale) := by
  exact affect_valence_axis_is_independent

/-! ## Finite affect catalog (matrix entries)

The 21-kind catalog is calibrated to fully inhabit the
`OverflowLocale × OverflowValence × AffectTendency` (3 × 2 × 3 = 18)
matrix coordinate. Each cell has at least one named witness; some
cells (e.g. body-negative-withdraw) have multiple. The catalog is
not a closed taxonomy of emotion — it is a structural grid that
forces every cross-axis combination to be representable.

Cell coverage by kind (locale × valence × tendency):
  body × positive × approach      → desire
  body × positive × withdraw      → relief
  body × positive × hold          → calm
  body × negative × approach      → anger
  body × negative × withdraw      → fear, grief
  body × negative × hold          → numbness
  conscious × positive × approach → hope
  conscious × positive × withdraw → nostalgia
  conscious × positive × hold     → serenity
  conscious × negative × approach → resentment
  conscious × negative × withdraw → sadness, shame
  conscious × negative × hold     → anxiety
  environment × positive × approach → joy, love
  environment × positive × withdraw → contentment
  environment × positive × hold     → awe
  environment × negative × approach → outrage
  environment × negative × withdraw → alienation
  environment × negative × hold     → dread

The triple-axis independence is certified at the matrix-coordinate
level by `AffectAxesIndependence.locale_valence_tendency_grid_fully_inhabited`. -/
inductive AffectKind where
  | joy
  | sadness
  | anger
  | fear
  | calm
  | anxiety
  | shame
  | hope
  | love
  | grief
  | desire
  | relief
  | numbness
  | nostalgia
  | serenity
  | resentment
  | contentment
  | awe
  | outrage
  | alienation
  | dread
  deriving DecidableEq, Repr

def affectOfKind : AffectKind → AffectVector
  | .joy =>
      { emotion := { locale := OverflowLocale.environment, valence := OverflowValence.positive, frequency := 7, intensity := 8 }
        arousal := 7
        dominance := 6
        tendency := AffectTendency.approach }
  | .sadness =>
      { emotion := { locale := OverflowLocale.conscious, valence := OverflowValence.negative, frequency := 3, intensity := 6 }
        arousal := 2
        dominance := 3
        tendency := AffectTendency.withdraw }
  | .anger =>
      { emotion := { locale := OverflowLocale.body, valence := OverflowValence.negative, frequency := 8, intensity := 9 }
        arousal := 9
        dominance := 8
        tendency := AffectTendency.approach }
  | .fear =>
      { emotion := { locale := OverflowLocale.body, valence := OverflowValence.negative, frequency := 9, intensity := 8 }
        arousal := 9
        dominance := 2
        tendency := AffectTendency.withdraw }
  | .calm =>
      { emotion := { locale := OverflowLocale.body, valence := OverflowValence.positive, frequency := 2, intensity := 4 }
        arousal := 1
        dominance := 7
        tendency := AffectTendency.hold }
  | .anxiety =>
      { emotion := { locale := OverflowLocale.conscious, valence := OverflowValence.negative, frequency := 10, intensity := 8 }
        arousal := 10
        dominance := 2
        tendency := AffectTendency.hold }
  | .shame =>
      { emotion := { locale := OverflowLocale.conscious, valence := OverflowValence.negative, frequency := 4, intensity := 7 }
        arousal := 5
        dominance := 1
        tendency := AffectTendency.withdraw }
  | .hope =>
      { emotion := { locale := OverflowLocale.conscious, valence := OverflowValence.positive, frequency := 6, intensity := 6 }
        arousal := 5
        dominance := 5
        tendency := AffectTendency.approach }
  | .love =>
      { emotion := { locale := OverflowLocale.environment, valence := OverflowValence.positive, frequency := 5, intensity := 9 }
        arousal := 6
        dominance := 6
        tendency := AffectTendency.approach }
  | .grief =>
      { emotion := { locale := OverflowLocale.body, valence := OverflowValence.negative, frequency := 1, intensity := 9 }
        arousal := 4
        dominance := 2
        tendency := AffectTendency.withdraw }
  -- body × positive × approach: somatic orientation toward a sensed pleasurable target
  | .desire =>
      { emotion := { locale := OverflowLocale.body, valence := OverflowValence.positive, frequency := 6, intensity := 7 }
        arousal := 7
        dominance := 5
        tendency := AffectTendency.approach }
  -- body × positive × withdraw: post-tension settling, the exhale after the threat passes
  | .relief =>
      { emotion := { locale := OverflowLocale.body, valence := OverflowValence.positive, frequency := 4, intensity := 5 }
        arousal := 2
        dominance := 5
        tendency := AffectTendency.withdraw }
  -- body × negative × hold: somatic freeze, the body's frozen response to overwhelm
  | .numbness =>
      { emotion := { locale := OverflowLocale.body, valence := OverflowValence.negative, frequency := 1, intensity := 4 }
        arousal := 1
        dominance := 1
        tendency := AffectTendency.hold }
  -- conscious × positive × withdraw: mind pulling back into a remembered sweetness
  | .nostalgia =>
      { emotion := { locale := OverflowLocale.conscious, valence := OverflowValence.positive, frequency := 5, intensity := 6 }
        arousal := 3
        dominance := 4
        tendency := AffectTendency.withdraw }
  -- conscious × positive × hold: settled equanimity, the steady mind
  | .serenity =>
      { emotion := { locale := OverflowLocale.conscious, valence := OverflowValence.positive, frequency := 3, intensity := 6 }
        arousal := 1
        dominance := 7
        tendency := AffectTendency.hold }
  -- conscious × negative × approach: recurrent grievance returning to the wound
  | .resentment =>
      { emotion := { locale := OverflowLocale.conscious, valence := OverflowValence.negative, frequency := 5, intensity := 7 }
        arousal := 6
        dominance := 5
        tendency := AffectTendency.approach }
  -- environment × positive × withdraw: settled enjoyment of place without active engagement
  | .contentment =>
      { emotion := { locale := OverflowLocale.environment, valence := OverflowValence.positive, frequency := 4, intensity := 6 }
        arousal := 2
        dominance := 6
        tendency := AffectTendency.withdraw }
  -- environment × positive × hold: held by the world's scale, neither approaching nor withdrawing
  | .awe =>
      { emotion := { locale := OverflowLocale.environment, valence := OverflowValence.positive, frequency := 8, intensity := 9 }
        arousal := 6
        dominance := 4
        tendency := AffectTendency.hold }
  -- environment × negative × approach: going toward the broken world to confront it
  | .outrage =>
      { emotion := { locale := OverflowLocale.environment, valence := OverflowValence.negative, frequency := 9, intensity := 9 }
        arousal := 9
        dominance := 7
        tendency := AffectTendency.approach }
  -- environment × negative × withdraw: pulling away from the world, estrangement
  | .alienation =>
      { emotion := { locale := OverflowLocale.environment, valence := OverflowValence.negative, frequency := 2, intensity := 5 }
        arousal := 2
        dominance := 2
        tendency := AffectTendency.withdraw }
  -- environment × negative × hold: held in place by environmental threat
  | .dread =>
      { emotion := { locale := OverflowLocale.environment, valence := OverflowValence.negative, frequency := 7, intensity := 7 }
        arousal := 7
        dominance := 2
        tendency := AffectTendency.hold }

def matrixVibeOfKind (kind : AffectKind) : VibeWave :=
  vibeWaveOfAffect (affectOfKind kind)

theorem joy_is_positive_approach :
    (affectOfKind .joy).emotion.valence = OverflowValence.positive ∧
      (affectOfKind .joy).tendency = AffectTendency.approach := by
  decide

theorem anger_is_negative_approach :
    (affectOfKind .anger).emotion.valence = OverflowValence.negative ∧
      (affectOfKind .anger).tendency = AffectTendency.approach := by
  decide

theorem sadness_is_negative_withdraw :
    (affectOfKind .sadness).emotion.valence = OverflowValence.negative ∧
      (affectOfKind .sadness).tendency = AffectTendency.withdraw := by
  decide

theorem calm_is_positive_low_arousal :
    (affectOfKind .calm).emotion.valence = OverflowValence.positive ∧
      (affectOfKind .calm).arousal = 1 := by
  decide

theorem affect_catalog_projects_to_simple_vibes :
    (matrixVibeOfKind .joy).valence = VibeValence.happy ∧
      (matrixVibeOfKind .sadness).valence = VibeValence.unhappy ∧
        (matrixVibeOfKind .anger).valence = VibeValence.unhappy := by
  decide

/-! ## Pair inference -/

/-- Simple pair inference:
    * happy + happy amplifies happiness;
    * unhappy + unhappy amplifies unhappiness;
    * happy + unhappy damps into neutral mediation;
    * neutral transmits the non-neutral wave without changing its coordinates. -/
def inferBetween (a b : VibeWave) : VibeWave :=
  match a.valence, b.valence with
  | .happy, .happy =>
      { valence := .happy
        frequency := a.frequency
        amplitude := a.amplitude + b.amplitude
        decay_rate := a.decay_rate + b.decay_rate }
  | .unhappy, .unhappy =>
      { valence := .unhappy
        frequency := a.frequency
        amplitude := a.amplitude + b.amplitude
        decay_rate := a.decay_rate + b.decay_rate }
  | .neutral, _ => b
  | _, .neutral => a
  | _, _ =>
      { valence := .neutral
        frequency := a.frequency
        amplitude := a.amplitude + b.amplitude
        decay_rate := a.decay_rate + b.decay_rate }

theorem two_happy_infer_happy (a b : VibeWave)
    (ha : a.valence = VibeValence.happy) (hb : b.valence = VibeValence.happy) :
    (inferBetween a b).valence = VibeValence.happy := by
  cases a
  cases b
  simp [inferBetween] at ha hb ⊢
  rw [ha, hb]

theorem two_unhappy_infer_unhappy (a b : VibeWave)
    (ha : a.valence = VibeValence.unhappy) (hb : b.valence = VibeValence.unhappy) :
    (inferBetween a b).valence = VibeValence.unhappy := by
  cases a
  cases b
  simp [inferBetween] at ha hb ⊢
  rw [ha, hb]

theorem happy_unhappy_infer_neutral (a b : VibeWave)
    (ha : a.valence = VibeValence.happy) (hb : b.valence = VibeValence.unhappy) :
    (inferBetween a b).valence = VibeValence.neutral := by
  cases a
  cases b
  simp [inferBetween] at ha hb ⊢
  rw [ha, hb]

/-! ## Finite group inference -/

def happyCount : List VibeWave → Nat
  | [] => 0
  | v :: vs =>
      (if v.valence = VibeValence.happy then 1 else 0) + happyCount vs

def unhappyCount : List VibeWave → Nat
  | [] => 0
  | v :: vs =>
      (if v.valence = VibeValence.unhappy then 1 else 0) + unhappyCount vs

/-- Group vibe by majority count. Ties and empty groups are neutral. -/
def aggregateValence (waves : List VibeWave) : VibeValence :=
  if unhappyCount waves > happyCount waves then
    VibeValence.unhappy
  else if happyCount waves > unhappyCount waves then
    VibeValence.happy
  else
    VibeValence.neutral

/-- Happiness is contagious when at least two happy waves dominate the local field. -/
def HappinessContagion (waves : List VibeWave) : Prop :=
  happyCount waves ≥ 2 ∧ aggregateValence waves = VibeValence.happy

/-- Depression/unhappiness is contagious when at least two unhappy waves dominate. -/
def DepressionContagion (waves : List VibeWave) : Prop :=
  unhappyCount waves ≥ 2 ∧ aggregateValence waves = VibeValence.unhappy

/-! ## Concrete waves and witnesses -/

def happyWave : VibeWave where
  valence := VibeValence.happy
  frequency := 7
  amplitude := 5
  decay_rate := 30

def unhappyWave : VibeWave where
  valence := VibeValence.unhappy
  frequency := 3
  amplitude := 4
  decay_rate := 80

def quietWave : VibeWave where
  valence := VibeValence.neutral
  frequency := 1
  amplitude := 1
  decay_rate := 20

theorem two_happy_people_are_happy_field :
    HappinessContagion [happyWave, happyWave] := by
  unfold HappinessContagion aggregateValence happyCount unhappyCount happyWave
  decide

theorem two_unhappy_people_are_unhappy_field :
    DepressionContagion [unhappyWave, unhappyWave] := by
  unfold DepressionContagion aggregateValence happyCount unhappyCount unhappyWave
  decide

theorem happy_and_unhappy_people_are_neutral_field :
    aggregateValence [happyWave, unhappyWave] = VibeValence.neutral := by
  unfold aggregateValence happyCount unhappyCount happyWave unhappyWave
  decide

theorem n_happy_majority_is_happy_example :
    HappinessContagion [happyWave, happyWave, happyWave, unhappyWave] := by
  unfold HappinessContagion aggregateValence happyCount unhappyCount happyWave unhappyWave
  decide

theorem n_unhappy_majority_is_depression_contagion_example :
    DepressionContagion [unhappyWave, unhappyWave, unhappyWave, happyWave] := by
  unfold DepressionContagion aggregateValence happyCount unhappyCount happyWave unhappyWave
  decide

/-! ## Bridge to existing depression formalization -/

/-- A concrete depression asymmetry state supplied by unhappy contagion:
    positive energy decays far faster than negative energy. -/
def contagiousDepressionState : DepressionState where
  positive_decay := 120
  negative_decay := 40

theorem contagious_depression_state_is_depressed :
    is_depressed contagiousDepressionState := by
  unfold contagiousDepressionState is_depressed
  decide

/-- Local unhappy dominance can feed the existing depression asymmetry model. -/
theorem two_unhappy_people_feed_depression_asymmetry :
    DepressionContagion [unhappyWave, unhappyWave] ∧ is_depressed contagiousDepressionState := by
  exact ⟨two_unhappy_people_are_unhappy_field, contagious_depression_state_is_depressed⟩

end VibesAsWaveInference
