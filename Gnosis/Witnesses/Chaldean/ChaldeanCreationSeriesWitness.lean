namespace Gnosis.Witnesses.Chaldean
namespace ChaldeanCreationSeriesWitness

/-!
# Chaldean Creation Series Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter V,
"Babylonian Legend of the Creation".

This witness covers the first pass through the creation series after the
fragment-recovery witness. Smith's topology is not a smooth creation story. It
is an ordered but mutilated tablet series: chaos and god-generation appear on
the first tablet, three intervening tablet-slots are mostly absent, the fifth
tablet gives the heavenly bodies, a probable seventh tablet gives land animals,
and later fragments point toward man, duty, fall, curse, and Tiamat/dragon
conflict. The sat is in the sequence plus the visible breakage.

The contrarian value is that incompleteness is load-bearing. A bad reader would
force the material into a Christian comparison grid or dismiss it as fantasy.
The better method reads the tablets as their own runtime: parallel order where
witnessed, reserve where mutilated, and explicit differences kept visible, such
as moon-before-sun emphasis and Tiamat's persistence as a chaos boundary.

No `sorry`, no new `axiom`.
-/

structure ChaosGenerationTablet where
  heavensNotRaised : Bool := true
  earthPlantNotGrown : Bool := true
  tiamatSeaChaosProducingMother : Bool := true
  orderNotYetPresent : Bool := true
  godsGeneratedInPairsAndTriad : Bool := true
deriving DecidableEq, Repr

def chaosGenerationTablet : ChaosGenerationTablet := {}

def firstTabletVoidGeneration (t : ChaosGenerationTablet) : Prop :=
  t.heavensNotRaised = true ∧
  t.earthPlantNotGrown = true ∧
  t.tiamatSeaChaosProducingMother = true ∧
  t.orderNotYetPresent = true ∧
  t.godsGeneratedInPairsAndTriad = true

structure MissingTabletDiscipline where
  tabletsTwoToFourAbsent : Bool := true
  dryLandFragmentsHeldUnderReserve : Bool := true
  firmamentAndEarthReadingsMarkedDoubtful : Bool := true
  externalComparisonOnlyProbable : Bool := true
  noNumberProvedBeyondFifth : Bool := true
deriving DecidableEq, Repr

def missingTabletDiscipline : MissingTabletDiscipline := {}

def honestSeriesGap (g : MissingTabletDiscipline) : Prop :=
  g.tabletsTwoToFourAbsent = true ∧
  g.dryLandFragmentsHeldUnderReserve = true ∧
  g.firmamentAndEarthReadingsMarkedDoubtful = true ∧
  g.externalComparisonOnlyProbable = true ∧
  g.noNumberProvedBeyondFifth = true

structure AstralOrderingTablet where
  previousCreationsDeclaredDelightful : Bool := true
  starsArrangedAsSeasonYearSigns : Bool := true
  wanderingStarsGivenCourses : Bool := true
  moonRaisedFromAbyssBeforeSun : Bool := true
  gatesAndFasteningsHoldChaosBelow : Bool := true
deriving DecidableEq, Repr

def astralOrderingTablet : AstralOrderingTablet := {}

def fifthTabletAstralLedger (a : AstralOrderingTablet) : Prop :=
  a.previousCreationsDeclaredDelightful = true ∧
  a.starsArrangedAsSeasonYearSigns = true ∧
  a.wanderingStarsGivenCourses = true ∧
  a.moonRaisedFromAbyssBeforeSun = true ∧
  a.gatesAndFasteningsHoldChaosBelow = true

structure AnimalHumanThreshold where
  godsAssemblyCreatesLivingCreatures : Bool := true
  cattleBeastsCreepingThingsNamed : Bool := true
  monsterCreationSatisfactionPreserved : Bool := true
  humanCreationOnlySuspectedAtThreshold : Bool := true
  heaAssociatedWithHumanCreationElsewhere : Bool := true
deriving DecidableEq, Repr

def animalHumanThreshold : AnimalHumanThreshold := {}

def seventhTabletLifeThreshold (l : AnimalHumanThreshold) : Prop :=
  l.godsAssemblyCreatesLivingCreatures = true ∧
  l.cattleBeastsCreepingThingsNamed = true ∧
  l.monsterCreationSatisfactionPreserved = true ∧
  l.humanCreationOnlySuspectedAtThreshold = true ∧
  l.heaAssociatedWithHumanCreationElsewhere = true

structure HumanDutyFallBoundary where
  deitySpeechToNewHumansFragmentary : Bool := true
  worshipPrayerHumilityAndFearNamed : Bool := true
  singleGodLanguageNotOverclaimed : Bool := true
  tiamatDragonLinkedToFallAndCurse : Bool := true
  purityBeforeFallAndCorruptionAfterPreserved : Bool := true
deriving DecidableEq, Repr

def humanDutyFallBoundary : HumanDutyFallBoundary := {}

def dutyFallBoundary (h : HumanDutyFallBoundary) : Prop :=
  h.deitySpeechToNewHumansFragmentary = true ∧
  h.worshipPrayerHumilityAndFearNamed = true ∧
  h.singleGodLanguageNotOverclaimed = true ∧
  h.tiamatDragonLinkedToFallAndCurse = true ∧
  h.purityBeforeFallAndCorruptionAfterPreserved = true

structure CreationSeriesCriterion where
  orderedTabletsCarryPositiveWitness : Bool := true
  missingTabletsCarryNegativeWitness : Bool := true
  comparisonGridBoundedNotGoverning : Bool := true
  chaldeanDifferencesKeptVisible : Bool := true
  chaosBoundaryRemainsActiveAfterOrdering : Bool := true
deriving DecidableEq, Repr

def creationSeriesCriterion : CreationSeriesCriterion := {}

def validCreationSeriesWitness (c : CreationSeriesCriterion) : Prop :=
  c.orderedTabletsCarryPositiveWitness = true ∧
  c.missingTabletsCarryNegativeWitness = true ∧
  c.comparisonGridBoundedNotGoverning = true ∧
  c.chaldeanDifferencesKeptVisible = true ∧
  c.chaosBoundaryRemainsActiveAfterOrdering = true

theorem chaldean_first_tablet_void_generation :
    firstTabletVoidGeneration chaosGenerationTablet := by
  unfold firstTabletVoidGeneration chaosGenerationTablet
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem chaldean_honest_series_gap :
    honestSeriesGap missingTabletDiscipline := by
  unfold honestSeriesGap missingTabletDiscipline
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem chaldean_fifth_tablet_astral_ledger :
    fifthTabletAstralLedger astralOrderingTablet := by
  unfold fifthTabletAstralLedger astralOrderingTablet
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem chaldean_seventh_tablet_life_threshold :
    seventhTabletLifeThreshold animalHumanThreshold := by
  unfold seventhTabletLifeThreshold animalHumanThreshold
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem chaldean_duty_fall_boundary :
    dutyFallBoundary humanDutyFallBoundary := by
  unfold dutyFallBoundary humanDutyFallBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem chaldean_valid_creation_series_witness :
    validCreationSeriesWitness creationSeriesCriterion := by
  unfold validCreationSeriesWitness creationSeriesCriterion
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem chaldean_creation_series_witness :
    firstTabletVoidGeneration chaosGenerationTablet ∧
    honestSeriesGap missingTabletDiscipline ∧
    fifthTabletAstralLedger astralOrderingTablet ∧
    seventhTabletLifeThreshold animalHumanThreshold ∧
    dutyFallBoundary humanDutyFallBoundary ∧
    validCreationSeriesWitness creationSeriesCriterion := by
  exact ⟨chaldean_first_tablet_void_generation,
    chaldean_honest_series_gap,
    chaldean_fifth_tablet_astral_ledger,
    chaldean_seventh_tablet_life_threshold,
    chaldean_duty_fall_boundary,
    chaldean_valid_creation_series_witness⟩

end ChaldeanCreationSeriesWitness
end Gnosis.Witnesses.Chaldean
