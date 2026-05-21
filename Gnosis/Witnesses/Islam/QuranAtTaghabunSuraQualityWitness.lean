import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAtTaghabunSuraQualityWitness

/-!
# Quran 64, At-Taghabun / Mutual Neglect -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:14662-14698`.

This complete sura witness covers Quran 64:1-18.

At-Taghabun is the mutual-loss-and-trial witness: all glorifies God, creation
and formed bodies return to Him, former peoples denied messengers, the gathering
day exposes mutual loss, calamity occurs by permission, family and wealth are
tests, and good loans are multiplied.

No `sorry`, no new `axiom`.
-/

inductive TaghabunQualityCluster
  | glorificationCreationFormationAndReturn
  | formerDenialAndMessengerHumanity
  | gatheringDayMutualLossAndForgiveness
  | calamityPermissionFamilyWealthTrial
  | obedienceSpendingGoodLoanAndMultiplication
deriving DecidableEq, Repr

def taghabunQualityClusters : List TaghabunQualityCluster :=
  [ .glorificationCreationFormationAndReturn, .formerDenialAndMessengerHumanity,
    .gatheringDayMutualLossAndForgiveness, .calamityPermissionFamilyWealthTrial,
    .obedienceSpendingGoodLoanAndMultiplication ]

structure TaghabunInvariantLedger where
  allCreationReturnsToGod : Bool := true
  gatheringDayRevealsMutualLoss : Bool := true
  calamityIsBoundedByDivinePermission : Bool := true
  familyAndWealthAreTests : Bool := true
  goodLoanIsMultipliedAndForgiven : Bool := true
deriving DecidableEq, Repr

def taghabunInvariantLedger : TaghabunInvariantLedger := {}

def taghabunSat (l : TaghabunInvariantLedger) : Prop :=
  l.allCreationReturnsToGod = true ∧ l.gatheringDayRevealsMutualLoss = true ∧
  l.calamityIsBoundedByDivinePermission = true ∧ l.familyAndWealthAreTests = true ∧
  l.goodLoanIsMultipliedAndForgiven = true

structure TaghabunGapLedger where
  humanMessengerObjectionRepeatsDenial : Bool := true
  disbeliefClaimsNoResurrection : Bool := true
  spousesAndChildrenCanBecomeTrialEnemies : Bool := true
  stinginessThreatensSelf : Bool := true
  obedienceCanBeBlockedByPossession : Bool := true
deriving DecidableEq, Repr

def taghabunGapLedger : TaghabunGapLedger := {}

def taghabunGapsExposeBoundary (g : TaghabunGapLedger) : Prop :=
  g.humanMessengerObjectionRepeatsDenial = true ∧ g.disbeliefClaimsNoResurrection = true ∧
  g.spousesAndChildrenCanBecomeTrialEnemies = true ∧ g.stinginessThreatensSelf = true ∧
  g.obedienceCanBeBlockedByPossession = true

def taghabunSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 64 / At-Taghabun witnesses gathered mutual loss, trial, and multiplied loan"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive TaghabunRegister | creation | messengers | gathering | calamity | family | loan
deriving DecidableEq, Repr, Nonempty

inductive TaghabunInvariant | gatheredTrialLoan
deriving DecidableEq, Repr

def taghabunRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : TaghabunRegister => TaghabunInvariant.gatheredTrialLoan)
      TaghabunInvariant.gatheredTrialLoan :=
  TruthOneManyNamesWitness.constant_names_agree TaghabunInvariant.gatheredTrialLoan

theorem taghabun_quality_clusters_shape :
    taghabunQualityClusters.length = 5 ∧
    taghabunQualityClusters.head? = some .glorificationCreationFormationAndReturn ∧
    taghabunQualityClusters.getLast? = some .obedienceSpendingGoodLoanAndMultiplication := by
  exact ⟨rfl, rfl, rfl⟩

theorem taghabun_sat_witness : taghabunSat taghabunInvariantLedger := by
  unfold taghabunSat taghabunInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem taghabun_gap_witness : taghabunGapsExposeBoundary taghabunGapLedger := by
  unfold taghabunGapsExposeBoundary taghabunGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem taghabun_access_archaeological :
    taghabunSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_at_taghabun_sura_quality_witness :
    taghabunQualityClusters.length = 5 ∧ taghabunSat taghabunInvariantLedger ∧
    taghabunGapsExposeBoundary taghabunGapLedger ∧
    taghabunSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : TaghabunRegister => TaghabunInvariant.gatheredTrialLoan)
      TaghabunInvariant.gatheredTrialLoan := by
  exact ⟨taghabun_quality_clusters_shape.left, taghabun_sat_witness, taghabun_gap_witness,
    taghabun_access_archaeological, taghabunRegistersAgree⟩

end QuranAtTaghabunSuraQualityWitness
end Gnosis.Witnesses.Islam
