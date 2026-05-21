import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlLaylSuraQualityWitness

/-! # Quran 92, Al-Layl / Night -- Complete Sura Quality Witness

Source anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:16012-16042`.
Covers Quran 92:1-21: night/day and male/female oaths, divergent striving,
stingy self-sufficiency, and giving for the Most High's face. No `sorry`, no new `axiom`. -/

inductive LaylCluster | pairedOaths | divergentStriving | givingForMostHigh
deriving DecidableEq, Repr
def laylClusters : List LaylCluster := [.pairedOaths, .divergentStriving, .givingForMostHigh]
structure LaylLedger where
  strivingSeparatesEaseFromHardship : Bool := true
  guidanceAndHereafterBelongToGod : Bool := true
  givingForGodsFacePurifies : Bool := true
deriving DecidableEq, Repr
def laylLedger : LaylLedger := {}
def laylSat (l : LaylLedger) : Prop :=
  l.strivingSeparatesEaseFromHardship = true ∧ l.guidanceAndHereafterBelongToGod = true ∧
  l.givingForGodsFacePurifies = true
structure LaylGap where
  stinginessClaimsSelfSufficiency : Bool := true
  wealthCannotSaveAtFall : Bool := true
  blazingFireReceivesDenial : Bool := true
deriving DecidableEq, Repr
def laylGap : LaylGap := {}
def laylGaps (g : LaylGap) : Prop :=
  g.stinginessClaimsSelfSufficiency = true ∧ g.wealthCannotSaveAtFall = true ∧
  g.blazingFireReceivesDenial = true
def laylAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 92 / Al-Layl witnesses divergent striving and purified giving"
    positiveSamples := [1, 2, 3], negativeSamples := [4, 5, 6] }
inductive LaylRegister | night | striving | giving | fire deriving DecidableEq, Repr, Nonempty
inductive LaylInvariant | strivingGiftSeparation deriving DecidableEq, Repr
def laylRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : LaylRegister => LaylInvariant.strivingGiftSeparation)
      LaylInvariant.strivingGiftSeparation :=
  TruthOneManyNamesWitness.constant_names_agree LaylInvariant.strivingGiftSeparation
theorem quran_al_layl_sura_quality_witness :
    laylClusters.length = 3 ∧ laylSat laylLedger ∧ laylGaps laylGap ∧
    laylAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : LaylRegister => LaylInvariant.strivingGiftSeparation)
      LaylInvariant.strivingGiftSeparation := by
  unfold laylSat laylLedger laylGaps laylGap
  exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, laylRegistersAgree⟩

end QuranAlLaylSuraQualityWitness
end Gnosis.Witnesses.Islam
