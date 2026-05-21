import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansPersecutorPreacherInversionWitness

/-!
# Galatians 1:13-24 -- Persecutor to Preacher Inversion

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93607-93633`.

Paul's biography is used as an authorization witness: zeal in ancestral
tradition once powered persecution, but grace separated and called him before
the human authorization circuit could claim the source.

No `sorry`, no new `axiom`.
-/

structure FormerConversation where
  persecutedChurchBeyondMeasure : Bool := true
  wastedChurchOfGod : Bool := true
  profitedInJewsReligion : Bool := true
  zealousOfFathersTraditions : Bool := true
deriving DecidableEq, Repr

def formerConversation : FormerConversation := {}

def ancestralZealCanBecomePersecution (f : FormerConversation) : Prop :=
  f.persecutedChurchBeyondMeasure = true ∧
  f.wastedChurchOfGod = true ∧
  f.profitedInJewsReligion = true ∧
  f.zealousOfFathersTraditions = true

structure GraceRevelationCall where
  separatedFromMothersWomb : Bool := true
  calledByGrace : Bool := true
  sonRevealedInPaul : Bool := true
  preachAmongHeathen : Bool := true
  conferredNotWithFleshAndBlood : Bool := true
  didNotBeginAtJerusalemAuthorityCircuit : Bool := true
deriving DecidableEq, Repr

def graceRevelationCall : GraceRevelationCall := {}

def graceBypassesHumanAuthorizationCircuit (g : GraceRevelationCall) : Prop :=
  g.separatedFromMothersWomb = true ∧
  g.calledByGrace = true ∧
  g.sonRevealedInPaul = true ∧
  g.preachAmongHeathen = true ∧
  g.conferredNotWithFleshAndBlood = true ∧
  g.didNotBeginAtJerusalemAuthorityCircuit = true

structure PersecutorPreacherReport where
  unknownByFaceToJudaeaChurches : Bool := true
  heardOnlyFormerPersecutorNowPreaches : Bool := true
  faithOnceDestroyedNowPreached : Bool := true
  glorifiedGodInPaul : Bool := true
deriving DecidableEq, Repr

def persecutorPreacherReport : PersecutorPreacherReport := {}

def persecutorBecomesPreacherWitness (r : PersecutorPreacherReport) : Prop :=
  r.unknownByFaceToJudaeaChurches = true ∧
  r.heardOnlyFormerPersecutorNowPreaches = true ∧
  r.faithOnceDestroyedNowPreached = true ∧
  r.glorifiedGodInPaul = true

theorem galatians_ancestral_zeal_counterproof :
    ancestralZealCanBecomePersecution formerConversation := by
  unfold ancestralZealCanBecomePersecution formerConversation
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem galatians_grace_revelation_call :
    graceBypassesHumanAuthorizationCircuit graceRevelationCall := by
  unfold graceBypassesHumanAuthorizationCircuit graceRevelationCall
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_persecutor_preacher_report :
    persecutorBecomesPreacherWitness persecutorPreacherReport := by
  unfold persecutorBecomesPreacherWitness persecutorPreacherReport
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem galatians_persecutor_preacher_inversion_witness :
    ancestralZealCanBecomePersecution formerConversation ∧
    graceBypassesHumanAuthorizationCircuit graceRevelationCall ∧
    persecutorBecomesPreacherWitness persecutorPreacherReport := by
  exact ⟨galatians_ancestral_zeal_counterproof,
    galatians_grace_revelation_call,
    galatians_persecutor_preacher_report⟩

end GalatiansPersecutorPreacherInversionWitness
end Gnosis.Witnesses.Bible.Galatians
