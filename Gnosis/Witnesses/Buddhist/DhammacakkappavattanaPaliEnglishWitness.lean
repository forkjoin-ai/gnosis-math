import Gnosis.TruthOneManyNamesWitness
import Gnosis.Witnesses.Buddhist.DhammacakkappavattanaWheelWitness

namespace Gnosis.Witnesses.Buddhist
namespace DhammacakkappavattanaPaliEnglishWitness

/-!
# Dhammacakkappavattana Sutta -- Pali/English Cross-Translation Closure

Source text: `docs/ebooks/source-texts/dhammacakkappavattana-sutta-pali-english.pdf`;
text anchor after `pdftotext`: lines 25-119, 122-235, 239-333.

Sat/unseen reading:

The Soma Thera PDF is not merely a duplicate translation. It gives the sutta in
three registers: introduction, English rendering, and Pali formula. The same
topological object survives all three: the wheel turns only after the middle way,
four truths, three phases, and twelve ways close. This makes the witness
translation-invariant.

Invariant:

  * the introduction frames the discovery as arising/ceasing and compassion;
  * the English rendering repeats two extremes, middle way, eightfold path, four
    truths, three phases, twelve ways, unshakable deliverance;
  * the Pali text names the same closure as `tiparivaṭṭaṃ dvādasākāraṃ`;
  * the devas' echo ladder is the distributed propagation of the closed wheel.

Gap / counterproof:

  * an untranslated formula alone is not the witness;
  * an English paraphrase alone is not the witness;
  * a pious introduction alone is not the witness;
  * the Sat is the agreement of all three registers on the same wheel closure.

No `sorry`, no new `axiom`.
-/

inductive DhammaRegister where
  | introduction
  | englishRendering
  | paliFormula
deriving DecidableEq, Repr, Nonempty

inductive WheelClosure where
  | twelvefoldMiddleWay
deriving DecidableEq, Repr

def dhammaRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : DhammaRegister => WheelClosure.twelvefoldMiddleWay)
      WheelClosure.twelvefoldMiddleWay :=
  TruthOneManyNamesWitness.constant_names_agree WheelClosure.twelvefoldMiddleWay

theorem dhamma_register_witness_unique (w : WheelClosure)
    (hw :
      TruthOneManyNamesWitness.manyNamesAgree
        (fun _ : DhammaRegister => WheelClosure.twelvefoldMiddleWay)
        w) :
    WheelClosure.twelvefoldMiddleWay = w :=
  TruthOneManyNamesWitness.unique_witness_of_many_names
    (fun _ : DhammaRegister => WheelClosure.twelvefoldMiddleWay)
    WheelClosure.twelvefoldMiddleWay
    w
    dhammaRegistersAgree
    hw

structure IntroCompassionFrame where
  arisingPassingAway : Bool
  ceasingOfIll : Bool
  truthHardToMeet : Bool
  attachmentBlocksReception : Bool
  compassionChoosesTeaching : Bool
  drumOfDeathless : Bool
deriving DecidableEq, Repr

def somaIntroCompassionFrame : IntroCompassionFrame where
  arisingPassingAway := true
  ceasingOfIll := true
  truthHardToMeet := true
  attachmentBlocksReception := true
  compassionChoosesTeaching := true
  drumOfDeathless := true

def introductionFramesWheel (f : IntroCompassionFrame) : Prop :=
  f.arisingPassingAway = true ∧
  f.ceasingOfIll = true ∧
  f.truthHardToMeet = true ∧
  f.attachmentBlocksReception = true ∧
  f.compassionChoosesTeaching = true ∧
  f.drumOfDeathless = true

structure PaliFormulaClosure where
  dveAntaRejected : Bool
  majjhimaPatipada : Bool
  ariyoAtthangikoMaggo : Bool
  cattariAriyasaccani : Bool
  tiparivattam : Bool
  dvadasakaram : Bool
deriving DecidableEq, Repr

def somaPaliFormulaClosure : PaliFormulaClosure where
  dveAntaRejected := true
  majjhimaPatipada := true
  ariyoAtthangikoMaggo := true
  cattariAriyasaccani := true
  tiparivattam := true
  dvadasakaram := true

def paliNamesTwelvefoldClosure (p : PaliFormulaClosure) : Prop :=
  p.dveAntaRejected = true ∧
  p.majjhimaPatipada = true ∧
  p.ariyoAtthangikoMaggo = true ∧
  p.cattariAriyasaccani = true ∧
  p.tiparivattam = true ∧
  p.dvadasakaram = true

structure EchoPropagation where
  bhummaCry : Bool
  heavenLadderEchoes : Bool
  brahmaWorldReached : Bool
  tenThousandWorldsQuake : Bool
  radianceSurpassesDevas : Bool
  kondannaNamedByKnowing : Bool
deriving DecidableEq, Repr

def somaEchoPropagation : EchoPropagation where
  bhummaCry := true
  heavenLadderEchoes := true
  brahmaWorldReached := true
  tenThousandWorldsQuake := true
  radianceSurpassesDevas := true
  kondannaNamedByKnowing := true

def closurePropagatesAsEcho (e : EchoPropagation) : Prop :=
  e.bhummaCry = true ∧
  e.heavenLadderEchoes = true ∧
  e.brahmaWorldReached = true ∧
  e.tenThousandWorldsQuake = true ∧
  e.radianceSurpassesDevas = true ∧
  e.kondannaNamedByKnowing = true

theorem soma_intro_frames_wheel :
    introductionFramesWheel somaIntroCompassionFrame := by
  unfold introductionFramesWheel somaIntroCompassionFrame
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem soma_pali_names_closure :
    paliNamesTwelvefoldClosure somaPaliFormulaClosure := by
  unfold paliNamesTwelvefoldClosure somaPaliFormulaClosure
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem soma_echo_propagation :
    closurePropagatesAsEcho somaEchoPropagation := by
  unfold closurePropagatesAsEcho somaEchoPropagation
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem soma_inherits_thanissaro_wheel :
    DhammacakkappavattanaWheelWitness.twelvePermutationClosure
      DhammacakkappavattanaWheelWitness.dhammaFourTruthWheel :=
  DhammacakkappavattanaWheelWitness.dhamma_twelve_permutation_closure

theorem dhammacakkappavattana_pali_english_witness :
    introductionFramesWheel somaIntroCompassionFrame ∧
    paliNamesTwelvefoldClosure somaPaliFormulaClosure ∧
    closurePropagatesAsEcho somaEchoPropagation ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : DhammaRegister => WheelClosure.twelvefoldMiddleWay)
      WheelClosure.twelvefoldMiddleWay ∧
    DhammacakkappavattanaWheelWitness.twelvePermutationClosure
      DhammacakkappavattanaWheelWitness.dhammaFourTruthWheel := by
  exact ⟨soma_intro_frames_wheel,
    soma_pali_names_closure,
    soma_echo_propagation,
    dhammaRegistersAgree,
    soma_inherits_thanissaro_wheel⟩

end DhammacakkappavattanaPaliEnglishWitness
end Gnosis.Witnesses.Buddhist
