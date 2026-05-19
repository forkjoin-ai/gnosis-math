import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Gnostic
namespace GospelThomasInterpretationKingdomWitness

/-!
# Gospel of Thomas -- Interpretation and Nonlocal Kingdom

Source text: `docs/ebooks/source-texts/gospel-of-thomas.txt`;
text anchor `docs/ebooks/source-texts/gospel-of-thomas.txt:10-50`.

Sat/unseen reading:

Thomas begins by making interpretation itself salvific. The kingdom is not a
sky/sea coordinate that lets birds or fish precede the seeker; it is inside and
outside. Self-knowledge converts poverty into sonship, while hidden things become
plain.

Gap / counterproof:

External localization of the kingdom is a false map. If the kingdom is only in
the sky or sea, nonhuman creatures beat the seeker there; therefore the map is
wrong.

No `sorry`, no new `axiom`.
-/

structure InterpretationPath where
  secretSayings : Bool
  interpretationFound : Bool
  noDeath : Bool
  seekUntilFind : Bool
  troubleAstonishmentRuleAll : Bool
deriving DecidableEq, Repr

def thomasInterpretationPath : InterpretationPath where
  secretSayings := true
  interpretationFound := true
  noDeath := true
  seekUntilFind := true
  troubleAstonishmentRuleAll := true

def interpretationBreaksDeath (p : InterpretationPath) : Prop :=
  p.secretSayings = true ∧
  p.interpretationFound = true ∧
  p.noDeath = true ∧
  p.seekUntilFind = true ∧
  p.troubleAstonishmentRuleAll = true

structure KingdomMapCounterproof where
  notSkyOnly : Bool
  notSeaOnly : Bool
  insideYou : Bool
  outsideYou : Bool
  selfKnowledgeKnown : Bool
  ignoranceIsPoverty : Bool
deriving DecidableEq, Repr

def thomasKingdomMapCounterproof : KingdomMapCounterproof where
  notSkyOnly := true
  notSeaOnly := true
  insideYou := true
  outsideYou := true
  selfKnowledgeKnown := true
  ignoranceIsPoverty := true

def externalKingdomMapFails (m : KingdomMapCounterproof) : Prop :=
  m.notSkyOnly = true ∧
  m.notSeaOnly = true ∧
  m.insideYou = true ∧
  m.outsideYou = true ∧
  m.selfKnowledgeKnown = true ∧
  m.ignoranceIsPoverty = true

structure ManifestHidden where
  recognizeInSight : Bool
  hiddenPlain : Bool
  liesRejected : Bool
  hatedActsRejected : Bool
  coveredUncovered : Bool
deriving DecidableEq, Repr

def thomasManifestHidden : ManifestHidden where
  recognizeInSight := true
  hiddenPlain := true
  liesRejected := true
  hatedActsRejected := true
  coveredUncovered := true

def hiddenBecomesManifest (h : ManifestHidden) : Prop :=
  h.recognizeInSight = true ∧
  h.hiddenPlain = true ∧
  h.liesRejected = true ∧
  h.hatedActsRejected = true ∧
  h.coveredUncovered = true

theorem thomas_interpretation_breaks_death :
    interpretationBreaksDeath thomasInterpretationPath := by
  unfold interpretationBreaksDeath thomasInterpretationPath
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_external_map_fails :
    externalKingdomMapFails thomasKingdomMapCounterproof := by
  unfold externalKingdomMapFails thomasKingdomMapCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_hidden_manifest :
    hiddenBecomesManifest thomasManifestHidden := by
  unfold hiddenBecomesManifest thomasManifestHidden
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_interpretation_recovery :
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom :=
  Gnosis.GnosisTriptychBraid.two_step_recovery

theorem gospel_thomas_interpretation_kingdom_witness :
    interpretationBreaksDeath thomasInterpretationPath ∧
    externalKingdomMapFails thomasKingdomMapCounterproof ∧
    hiddenBecomesManifest thomasManifestHidden ∧
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom := by
  exact ⟨thomas_interpretation_breaks_death,
    thomas_external_map_fails,
    thomas_hidden_manifest,
    thomas_interpretation_recovery⟩

end GospelThomasInterpretationKingdomWitness
end Gnosis.Witnesses.Gnostic
