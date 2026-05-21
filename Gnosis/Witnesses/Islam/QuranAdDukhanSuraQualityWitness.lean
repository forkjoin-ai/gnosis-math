import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAdDukhanSuraQualityWitness

/-!
# Quran 44, Ad-Dukhan / Smoke -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:12902-12980`.

This complete sura witness covers Quran 44:1-59.

Ad-Dukhan is the decisive-night-and-smoke witness: Scripture sent down on a
blessed night, every wise matter determined, smoke as punishment sign, Pharaoh's
trial pattern, sea crossing, inherited gardens lost, Zaqqum, and the secure
place of the mindful as the counter-form of judgment.

No `sorry`, no new `axiom`.
-/

inductive DukhanQualityCluster
  | blessedNightAndWiseCommand
  | smokeWarningAndRejectedMessenger
  | pharaohTrialAndSeaDeliverance
  | inheritedLossAndNoWeepingSky
  | zaqqumJudgmentAndSecureMindfulPlace
deriving DecidableEq, Repr

def dukhanQualityClusters : List DukhanQualityCluster :=
  [ .blessedNightAndWiseCommand
  , .smokeWarningAndRejectedMessenger
  , .pharaohTrialAndSeaDeliverance
  , .inheritedLossAndNoWeepingSky
  , .zaqqumJudgmentAndSecureMindfulPlace
  ]

structure DukhanInvariantLedger where
  revelationArrivesByBlessedDetermination : Bool := true
  warningCanTakeVisibleSmokeForm : Bool := true
  tyrantPowerFailsAtTheSea : Bool := true
  worldlyGardensCanBeTransferredAway : Bool := true
  mindfulSecurityAnswersJudgment : Bool := true
deriving DecidableEq, Repr

def dukhanInvariantLedger : DukhanInvariantLedger := {}

def dukhanSat (l : DukhanInvariantLedger) : Prop :=
  l.revelationArrivesByBlessedDetermination = true ∧
  l.warningCanTakeVisibleSmokeForm = true ∧
  l.tyrantPowerFailsAtTheSea = true ∧
  l.worldlyGardensCanBeTransferredAway = true ∧
  l.mindfulSecurityAnswersJudgment = true

structure DukhanGapLedger where
  messengerIsDismissedAsTaughtMadman : Bool := true
  reliefPromptsReturnToDenial : Bool := true
  pharaohClaimsExaltedImmunity : Bool := true
  zaqqumFeedsTheSinful : Bool := true
  waitAndTheyWaitClosesTheWarning : Bool := true
deriving DecidableEq, Repr

def dukhanGapLedger : DukhanGapLedger := {}

def dukhanGapsExposeBoundary (g : DukhanGapLedger) : Prop :=
  g.messengerIsDismissedAsTaughtMadman = true ∧
  g.reliefPromptsReturnToDenial = true ∧
  g.pharaohClaimsExaltedImmunity = true ∧
  g.zaqqumFeedsTheSinful = true ∧
  g.waitAndTheyWaitClosesTheWarning = true

def dukhanSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 44 / Ad-Dukhan witnesses determined revelation, smoke warning, and secure judgment"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive DukhanRegister | night | smoke | pharaoh | sea | inheritance | judgment
deriving DecidableEq, Repr, Nonempty

inductive DukhanInvariant | decisiveWarningAndSecureReturn
deriving DecidableEq, Repr

def dukhanRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : DukhanRegister => DukhanInvariant.decisiveWarningAndSecureReturn)
      DukhanInvariant.decisiveWarningAndSecureReturn :=
  TruthOneManyNamesWitness.constant_names_agree DukhanInvariant.decisiveWarningAndSecureReturn

theorem dukhan_quality_clusters_shape :
    dukhanQualityClusters.length = 5 ∧
    dukhanQualityClusters.head? = some .blessedNightAndWiseCommand ∧
    dukhanQualityClusters.getLast? = some .zaqqumJudgmentAndSecureMindfulPlace := by
  exact ⟨rfl, rfl, rfl⟩

theorem dukhan_sat_witness : dukhanSat dukhanInvariantLedger := by
  unfold dukhanSat dukhanInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem dukhan_gap_witness : dukhanGapsExposeBoundary dukhanGapLedger := by
  unfold dukhanGapsExposeBoundary dukhanGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem dukhan_access_archaeological :
    dukhanSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_ad_dukhan_sura_quality_witness :
    dukhanQualityClusters.length = 5 ∧
    dukhanSat dukhanInvariantLedger ∧
    dukhanGapsExposeBoundary dukhanGapLedger ∧
    dukhanSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : DukhanRegister => DukhanInvariant.decisiveWarningAndSecureReturn)
      DukhanInvariant.decisiveWarningAndSecureReturn := by
  exact ⟨dukhan_quality_clusters_shape.left, dukhan_sat_witness, dukhan_gap_witness,
    dukhan_access_archaeological, dukhanRegistersAgree⟩

end QuranAdDukhanSuraQualityWitness
end Gnosis.Witnesses.Islam
