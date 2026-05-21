import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansTruthTravailWitness

/-!
# Galatians 4:12-20 -- Truth-Speaking, Exclusion Zeal, and Travail

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93820-93836`.

Paul contrasts their first reception of his embodied weakness with the later
social capture mechanism: exclusionary zeal manufactures dependence. The
counter-witness is birth-labor until Christ is formed in them.

No `sorry`, no new `axiom`.
-/

structure FirstReception where
  paulBeseechesMutualIdentification : Bool := true
  gospelPreachedThroughInfirmity : Bool := true
  fleshTemptationNotDespised : Bool := true
  receivedAsAngelAndChristJesus : Bool := true
  formerBlessednessRemembered : Bool := true
  eyesWouldHaveBeenGiven : Bool := true
deriving DecidableEq, Repr

def firstReception : FirstReception := {}

def embodiedReceptionWitness (r : FirstReception) : Prop :=
  r.paulBeseechesMutualIdentification = true ∧
  r.gospelPreachedThroughInfirmity = true ∧
  r.fleshTemptationNotDespised = true ∧
  r.receivedAsAngelAndChristJesus = true ∧
  r.formerBlessednessRemembered = true ∧
  r.eyesWouldHaveBeenGiven = true

structure ExclusionZealTravail where
  truthSpeakerTreatedAsEnemy : Bool := true
  zealouslyAffectedButNotWell : Bool := true
  exclusionManufacturesDependence : Bool := true
  goodZealDistinguished : Bool := true
  travailUntilChristFormed : Bool := true
  voiceChangeDesiredInDoubt : Bool := true
deriving DecidableEq, Repr

def exclusionZealTravail : ExclusionZealTravail := {}

def travailAgainstCapture (t : ExclusionZealTravail) : Prop :=
  t.truthSpeakerTreatedAsEnemy = true ∧
  t.zealouslyAffectedButNotWell = true ∧
  t.exclusionManufacturesDependence = true ∧
  t.goodZealDistinguished = true ∧
  t.travailUntilChristFormed = true ∧
  t.voiceChangeDesiredInDoubt = true

theorem galatians_embodied_reception :
    embodiedReceptionWitness firstReception := by
  unfold embodiedReceptionWitness firstReception
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_travail_against_capture :
    travailAgainstCapture exclusionZealTravail := by
  unfold travailAgainstCapture exclusionZealTravail
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_truth_travail_witness :
    embodiedReceptionWitness firstReception ∧
    travailAgainstCapture exclusionZealTravail := by
  exact ⟨galatians_embodied_reception,
    galatians_travail_against_capture⟩

end GalatiansTruthTravailWitness
end Gnosis.Witnesses.Bible.Galatians
