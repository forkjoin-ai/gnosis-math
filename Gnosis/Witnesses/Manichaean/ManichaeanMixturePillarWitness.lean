namespace Gnosis.Witnesses.Manichaean
namespace ManichaeanMixturePillarWitness

/-!
# Manichaean Texts -- Mixture, Living Soul, and Pillar of Glory

Source slice:
- `docs/ebooks/source-texts/gardner-lieu-manichaean-texts.pdf`, introduction
  around the Father of Greatness, first/second time, Primal Man, Living Soul,
  call-answer awakening, and Pillar of Glory ascent.
- `docs/ebooks/key-to-the-manichaean-texts.md`.

Invariant: Manichaean dualism is not a simple two-god symmetry in this witness.
The Father remains hidden in the Land of Light while emissive signatures enter
the arena of mixture. Primal Man descends, the light elements are consumed and
mixed with darkness, and the Living Soul becomes the recoverable signal scattered
through matter.

Counterproof: the naive heresiology reads "two roots" as equal rival sources.
The better topological read is asymmetric: Darkness can grasp, consume, and
mix, but it does not generate a stable truth-position. The Manichaean drama is a
race/fold machine: mixture creates the rescue problem; call and answer awaken
the trapped signal; the Pillar of Glory names the return transport.

No `sorry`, no new `axiom`.
-/

structure LightHiddenness where
  fatherRulesRealmOfLight : Bool := true
  lightRealmExtendsFather : Bool := true
  fatherHasFiveIntellectualLimbs : Bool := true
  twelveAeonsSurroundFather : Bool := true
  fatherRemainsApartDuringConflict : Bool := true
deriving DecidableEq, Repr

def lightHiddenness : LightHiddenness := {}

def fatherHiddenNotCaptured (l : LightHiddenness) : Prop :=
  l.fatherRulesRealmOfLight = true ∧
  l.lightRealmExtendsFather = true ∧
  l.fatherHasFiveIntellectualLimbs = true ∧
  l.twelveAeonsSurroundFather = true ∧
  l.fatherRemainsApartDuringConflict = true

structure MixtureLivingSoul where
  darknessGlimpsesAndDesiresLight : Bool := true
  motherOfLifeEvokedFromFather : Bool := true
  primalManDescendsWithFiveSons : Bool := true
  lightElementsConsumedByDarkness : Bool := true
  livingSoulScatteredInMatter : Bool := true
  secondTimeIsArenaOfMixture : Bool := true
deriving DecidableEq, Repr

def mixtureLivingSoul : MixtureLivingSoul := {}

def mixtureTrapsRecoverableSignal (m : MixtureLivingSoul) : Prop :=
  m.darknessGlimpsesAndDesiresLight = true ∧
  m.motherOfLifeEvokedFromFather = true ∧
  m.primalManDescendsWithFiveSons = true ∧
  m.lightElementsConsumedByDarkness = true ∧
  m.livingSoulScatteredInMatter = true ∧
  m.secondTimeIsArenaOfMixture = true

structure CallAnswerPillar where
  livingSpiritCallsToPrimalMan : Bool := true
  answerAccompaniesCallAscending : Bool := true
  callAnswerAwakensSoul : Bool := true
  sunMoonServeAsLightShips : Bool := true
  pillarOfGloryCarriesSouls : Bool := true
  ascentRestoresFirstManPattern : Bool := true
deriving DecidableEq, Repr

def callAnswerPillar : CallAnswerPillar := {}

def pillarReturnsMixedLight (p : CallAnswerPillar) : Prop :=
  p.livingSpiritCallsToPrimalMan = true ∧
  p.answerAccompaniesCallAscending = true ∧
  p.callAnswerAwakensSoul = true ∧
  p.sunMoonServeAsLightShips = true ∧
  p.pillarOfGloryCarriesSouls = true ∧
  p.ascentRestoresFirstManPattern = true

theorem manichaean_father_hidden_not_captured :
    fatherHiddenNotCaptured lightHiddenness := by
  unfold fatherHiddenNotCaptured lightHiddenness
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem manichaean_mixture_traps_recoverable_signal :
    mixtureTrapsRecoverableSignal mixtureLivingSoul := by
  unfold mixtureTrapsRecoverableSignal mixtureLivingSoul
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem manichaean_pillar_returns_mixed_light :
    pillarReturnsMixedLight callAnswerPillar := by
  unfold pillarReturnsMixedLight callAnswerPillar
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem manichaean_mixture_pillar_witness :
    fatherHiddenNotCaptured lightHiddenness ∧
    mixtureTrapsRecoverableSignal mixtureLivingSoul ∧
    pillarReturnsMixedLight callAnswerPillar := by
  exact ⟨manichaean_father_hidden_not_captured,
    manichaean_mixture_traps_recoverable_signal,
    manichaean_pillar_returns_mixed_light⟩

end ManichaeanMixturePillarWitness
end Gnosis.Witnesses.Manichaean
