import Gnosis.Witnesses.Chaldean.UddusunamirSphinxHadesGateWitness

namespace Gnosis.Witnesses.Chaldean
namespace WiseManAirRiddleWitness

/-!
# Wise Man Air / Wind Riddle Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter X,
fragment K 2407: the wise man puts a riddle to the gods.

The riddle asks after a presence in house, secret place, foundation, floor,
side, ditch, and body; it roars, brays, flutters, bleats, barks, growls, and
enters the breast of man and woman. Smith's reading is that the answer is air
or wind, because it is everywhere and imitates animal voices.

This is a clean riddle topology: distributed invisible carrier, many local
manifestations, one answer. It belongs near the Sphinx material, but it is not
the same gate. The wise man does not fight; he compresses a field into a name.

No `sorry`, no new `axiom`.
-/

structure RiddleQuestionField where
  appearsInHouse : Bool := true
  appearsInSecretPlace : Bool := true
  appearsInFoundationAndFloor : Bool := true
  descendsBySidesAndDitch : Bool := true
  entersHumanBreast : Bool := true
deriving DecidableEq, Repr

def riddleQuestionField : RiddleQuestionField := {}

def riddleDistributesAcrossPlaces (r : RiddleQuestionField) : Prop :=
  r.appearsInHouse = true ∧
  r.appearsInSecretPlace = true ∧
  r.appearsInFoundationAndFloor = true ∧
  r.descendsBySidesAndDitch = true ∧
  r.entersHumanBreast = true

structure VoiceImitationLedger where
  roarsLikeBull : Bool := true
  braysLikeAss : Bool := true
  fluttersLikeSail : Bool := true
  bleatsLikeSheep : Bool := true
  barksLikeDog : Bool := true
  growlsLikeBear : Bool := true
deriving DecidableEq, Repr

def voiceImitationLedger : VoiceImitationLedger := {}

def windImitatesManyVoices (v : VoiceImitationLedger) : Prop :=
  v.roarsLikeBull = true ∧
  v.braysLikeAss = true ∧
  v.fluttersLikeSail = true ∧
  v.bleatsLikeSheep = true ∧
  v.barksLikeDog = true ∧
  v.growlsLikeBear = true

structure AirWindAnswer where
  answerIsAirOrWind : Bool := true
  invisibleButEverywhere : Bool := true
  oneNameCompressesManyEffects : Bool := true
  godsMustConsiderRiddle : Bool := true
deriving DecidableEq, Repr

def airWindAnswer : AirWindAnswer := {}

def airWindSolvesRiddle (a : AirWindAnswer) : Prop :=
  a.answerIsAirOrWind = true ∧
  a.invisibleButEverywhere = true ∧
  a.oneNameCompressesManyEffects = true ∧
  a.godsMustConsiderRiddle = true

structure RiddleSphinxBridge where
  riddleUsesQuestionNotWeapon : Bool := true
  invisibleCarrierNamedByEffects : Bool := true
  sphinxUsesLiminalGatePresence : Bool := true
  bothRequireCompressionAtBoundary : Bool := true
deriving DecidableEq, Repr

def riddleSphinxBridge : RiddleSphinxBridge := {}

def riddleAndSphinxShareBoundaryCompression (b : RiddleSphinxBridge) : Prop :=
  b.riddleUsesQuestionNotWeapon = true ∧
  b.invisibleCarrierNamedByEffects = true ∧
  b.sphinxUsesLiminalGatePresence = true ∧
  b.bothRequireCompressionAtBoundary = true

theorem wise_man_riddle_distributes_across_places :
    riddleDistributesAcrossPlaces riddleQuestionField := by
  unfold riddleDistributesAcrossPlaces riddleQuestionField
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem wise_man_wind_imitates_many_voices :
    windImitatesManyVoices voiceImitationLedger := by
  unfold windImitatesManyVoices voiceImitationLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wise_man_air_wind_solves_riddle :
    airWindSolvesRiddle airWindAnswer := by
  unfold airWindSolvesRiddle airWindAnswer
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem wise_man_riddle_sphinx_bridge :
    riddleAndSphinxShareBoundaryCompression riddleSphinxBridge ∧
    UddusunamirSphinxHadesGateWitness.sphinxOpensUnderworldGate
      UddusunamirSphinxHadesGateWitness.uddusunamirSphinx := by
  exact ⟨by
    unfold riddleAndSphinxShareBoundaryCompression riddleSphinxBridge
    exact ⟨rfl, rfl, rfl, rfl⟩,
    UddusunamirSphinxHadesGateWitness.uddusunamir_sphinx_opens_underworld_gate⟩

theorem wise_man_air_riddle_witness :
    riddleDistributesAcrossPlaces riddleQuestionField ∧
    windImitatesManyVoices voiceImitationLedger ∧
    airWindSolvesRiddle airWindAnswer ∧
    riddleAndSphinxShareBoundaryCompression riddleSphinxBridge := by
  exact ⟨wise_man_riddle_distributes_across_places,
    wise_man_wind_imitates_many_voices,
    wise_man_air_wind_solves_riddle,
    wise_man_riddle_sphinx_bridge.left⟩

end WiseManAirRiddleWitness
end Gnosis.Witnesses.Chaldean
