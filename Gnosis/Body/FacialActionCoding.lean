import Init

/-!
# Facial Action Coding System (FACS) — Somatic → Emotion → Expression

The mechanical puppet's face is a readout of its affective state. The pipeline,
reusing the somatic signals the motor learner already produces:

  somatic signal  →  emotion (appraisal)  →  facial Action Units (expression)

This is the somatic-marker view (Damasio): the body's state shapes emotion,
which shapes expression. The 17 Action Units and 9 emotion → AU mappings mirror
`shared-ui/data/emotionalExpressiveness` (Ekman's universals + self-conscious
emotions). `scripts/extract-lean-body-constants.ts` codegens these tables into
`aeon-corpus/src/generated/facs_tables.rs`, and `aeon-corpus/src/affect.rs`
bridges `thoth_brain` somatic signals into this pipeline.

Rustic Church: `Init` only, all pipeline theorems hold by `rfl`.
-/

namespace Gnosis.Body.FacialActionCoding

/-- The 17 implemented FACS Action Units (subset covering Ekman's universals
    plus the self-conscious head/eye AUs). -/
inductive ActionUnit where
  | au1   -- Inner Brow Raiser
  | au2   -- Outer Brow Raiser
  | au4   -- Brow Lowerer
  | au5   -- Upper Lid Raiser
  | au6   -- Cheek Raiser (Duchenne marker)
  | au7   -- Lid Tightener
  | au9   -- Nose Wrinkler
  | au12  -- Lip Corner Puller
  | au14  -- Dimpler
  | au15  -- Lip Corner Depressor
  | au16  -- Lower Lip Depressor
  | au20  -- Lip Stretcher
  | au23  -- Lip Tightener
  | au26  -- Jaw Drop
  | au53  -- Head Up
  | au54  -- Head Down
  | au64  -- Eyes Down
  deriving Repr, DecidableEq

/-- FACS intensity, the standard A–E ordinal scale. -/
inductive Intensity where
  | a | b | c | d | e
  deriving Repr, DecidableEq

/-- Discrete emotions with characteristic facial signatures. -/
inductive Emotion where
  | happiness
  | sadness
  | anger
  | fear
  | surprise
  | disgust
  | contempt
  | pride
  | shame
  deriving Repr, DecidableEq

/-- Somatic signals the motor learner emits (mirrors
    `thoth_brain::NegativeSignalType`, plus `wellbeing` for the success case). -/
inductive SomaticSignal where
  | pain
  | discomfort
  | instability
  | collision
  | fatigue
  | wellbeing
  deriving Repr, DecidableEq

open ActionUnit Emotion SomaticSignal

/-- Characteristic Action Units for each emotion (from the Ekman/FACS atlas). -/
def emotionAUs : Emotion → List ActionUnit
  | happiness => [au6, au12]
  | sadness   => [au1, au4, au15]
  | anger     => [au4, au5, au7, au23]
  | fear      => [au1, au2, au4, au5, au20, au26]
  | surprise  => [au1, au2, au5, au26]
  | disgust   => [au9, au15, au16]
  | contempt  => [au12, au14]
  | pride     => [au6, au12, au53]
  | shame     => [au54, au64]

/-- Appraisal: map a somatic signal to the emotion it elicits. -/
def somaticEmotion : SomaticSignal → Emotion
  | pain        => sadness
  | discomfort  => disgust
  | instability => fear
  | collision   => surprise
  | fatigue     => sadness
  | wellbeing   => happiness

/-- Full somatic → expression pipeline: the AUs a somatic signal drives. -/
def somaticAUs (s : SomaticSignal) : List ActionUnit :=
  emotionAUs (somaticEmotion s)

-- Pipeline invariants (all definitional).

theorem instability_is_fear : somaticEmotion instability = fear := rfl

theorem wellbeing_is_happiness : somaticEmotion wellbeing = happiness := rfl

theorem happiness_is_duchenne : emotionAUs happiness = [au6, au12] := rfl

/-- Instability drives the fear face (brow + lid + lip-stretch + jaw). -/
theorem instability_drives_fear_face :
    somaticAUs instability = [au1, au2, au4, au5, au20, au26] := rfl

/-- Wellbeing drives the Duchenne smile (cheek raiser + lip-corner puller). -/
theorem wellbeing_drives_smile : somaticAUs wellbeing = [au6, au12] := rfl

end Gnosis.Body.FacialActionCoding
