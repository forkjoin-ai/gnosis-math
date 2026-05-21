namespace Gnosis.Witnesses.Bible.Hebrews
namespace HebrewsBloodConscienceWitness

/-!
# Hebrews 9 -- Worldly Sanctuary, Blood, Conscience, and Once-for-All Entry

Source slice: Hebrews 9:1-28.

Chapter invariant: the first covenant's sanctuary is a figure with real divine
service, but its structure witnesses a blocked way. The first tabernacle stands,
priests continually serve, the high priest enters yearly with blood, and the
Spirit signifies that the holiest way is not yet manifest.

Primary gap/counterproof: gifts, sacrifices, meats, drinks, washings, and carnal
ordinances can purify flesh or order service, but they cannot perfect the
conscience. Christ's own blood, offered through the eternal Spirit, purges
conscience from dead works to serve the living God.

Unseen sat: testament requires death and blood, but finality requires non-repeat.
Christ enters heaven itself, appears for us before God, puts away sin by the
sacrifice of himself once at the end of the world, and appears a second time
without sin unto salvation.

No `sorry`, no new `axiom`.
-/

structure WorldlySanctuaryFigure where
  firstCovenantHasWorldlySanctuary : Bool := true
  furnitureWitnessesOrderedAccess : Bool := true
  firstTabernacleServiceContinues : Bool := true
  secondEnteredYearlyWithBlood : Bool := true
  holiestWayNotYetManifest : Bool := true
deriving DecidableEq, Repr

def worldlySanctuaryFigure : WorldlySanctuaryFigure := {}

def sanctuaryFigureWitness (s : WorldlySanctuaryFigure) : Prop :=
  s.firstCovenantHasWorldlySanctuary = true ∧
  s.furnitureWitnessesOrderedAccess = true ∧
  s.firstTabernacleServiceContinues = true ∧
  s.secondEnteredYearlyWithBlood = true ∧
  s.holiestWayNotYetManifest = true

structure ConsciencePurification where
  figureCannotPerfectConscience : Bool := true
  ordinancesStandUntilReformation : Bool := true
  christEntersGreaterTabernacle : Bool := true
  ownBloodObtainsEternalRedemption : Bool := true
  eternalSpiritOfferingPurgesConscience : Bool := true
deriving DecidableEq, Repr

def consciencePurification : ConsciencePurification := {}

def consciencePurificationWitness (p : ConsciencePurification) : Prop :=
  p.figureCannotPerfectConscience = true ∧
  p.ordinancesStandUntilReformation = true ∧
  p.christEntersGreaterTabernacle = true ∧
  p.ownBloodObtainsEternalRedemption = true ∧
  p.eternalSpiritOfferingPurgesConscience = true

structure TestamentOnceCounterproof where
  testamentRequiresDeath : Bool := true
  firstTestamentDedicatedWithBlood : Bool := true
  noRemissionWithoutBloodShedding : Bool := true
  heavenItselfExceedsHandmadeFigure : Bool := true
  repeatedOfferingWouldMeanRepeatedSuffering : Bool := true
  onceOfferingBearsManySins : Bool := true
  secondAppearingCompletesSalvationHope : Bool := true
deriving DecidableEq, Repr

def testamentOnceCounterproof : TestamentOnceCounterproof := {}

def repeatedFigureFinalityRejected (c : TestamentOnceCounterproof) : Prop :=
  c.testamentRequiresDeath = true ∧
  c.firstTestamentDedicatedWithBlood = true ∧
  c.noRemissionWithoutBloodShedding = true ∧
  c.heavenItselfExceedsHandmadeFigure = true ∧
  c.repeatedOfferingWouldMeanRepeatedSuffering = true ∧
  c.onceOfferingBearsManySins = true ∧
  c.secondAppearingCompletesSalvationHope = true

theorem hebrews_sanctuary_figure :
    sanctuaryFigureWitness worldlySanctuaryFigure := by
  unfold sanctuaryFigureWitness worldlySanctuaryFigure
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_conscience_purification :
    consciencePurificationWitness consciencePurification := by
  unfold consciencePurificationWitness consciencePurification
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_repeated_figure_finality_rejected :
    repeatedFigureFinalityRejected testamentOnceCounterproof := by
  unfold repeatedFigureFinalityRejected testamentOnceCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_blood_conscience_witness :
    sanctuaryFigureWitness worldlySanctuaryFigure ∧
    consciencePurificationWitness consciencePurification ∧
    repeatedFigureFinalityRejected testamentOnceCounterproof := by
  exact ⟨hebrews_sanctuary_figure,
    hebrews_conscience_purification,
    hebrews_repeated_figure_finality_rejected⟩

end HebrewsBloodConscienceWitness
end Gnosis.Witnesses.Bible.Hebrews
