import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlMujadilaSuraQualityWitness

/-!
# Quran 58, Al-Mujadila / The Dispute -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:14245-14321`.

This complete sura witness covers Quran 58:1-22.

Al-Mujadila is the heard-complaint-and-secret-counsel witness. God hears the
woman disputing about zihar; pagan divorce speech is repaired by expiation;
secret counsels are audited; gatherings must make room; private consultation
with the Messenger is disciplined by charity; false oaths shelter opposition;
and the party of God is marked by allegiance that cannot prefer hostile kinship.

No `sorry`, no new `axiom`.
-/

inductive MujadilaQualityCluster
  | heardDisputeAndZiharRepair
  | secretCounselAuditAndResurrectionDisclosure
  | gatheringRoomAndRaisedKnowledge
  | messengerConsultationCharityAndObedience
  | falseOathsHostileKinshipAndPartyOfGod
deriving DecidableEq, Repr

def mujadilaQualityClusters : List MujadilaQualityCluster :=
  [ .heardDisputeAndZiharRepair
  , .secretCounselAuditAndResurrectionDisclosure
  , .gatheringRoomAndRaisedKnowledge
  , .messengerConsultationCharityAndObedience
  , .falseOathsHostileKinshipAndPartyOfGod
  ]

structure MujadilaInvariantLedger where
  complaintIsHeardByGod : Bool := true
  harmfulSpeechRequiresRepair : Bool := true
  secretCounselIsNeverUnwitnessed : Bool := true
  knowledgeAndFaithRaiseRank : Bool := true
  allegianceDefinesPartyBoundary : Bool := true
deriving DecidableEq, Repr

def mujadilaInvariantLedger : MujadilaInvariantLedger := {}

def mujadilaSat (l : MujadilaInvariantLedger) : Prop :=
  l.complaintIsHeardByGod = true ∧
  l.harmfulSpeechRequiresRepair = true ∧
  l.secretCounselIsNeverUnwitnessed = true ∧
  l.knowledgeAndFaithRaiseRank = true ∧
  l.allegianceDefinesPartyBoundary = true

structure MujadilaGapLedger where
  ziharSpeechPretendsToChangeKinship : Bool := true
  secretCounselCanConspireInSin : Bool := true
  falseGreetingsAndOathsConcealHostility : Bool := true
  wealthAndChildrenCannotShieldOpposition : Bool := true
  hostileKinshipCannotOverrideFaithfulAllegiance : Bool := true
deriving DecidableEq, Repr

def mujadilaGapLedger : MujadilaGapLedger := {}

def mujadilaGapsExposeBoundary (g : MujadilaGapLedger) : Prop :=
  g.ziharSpeechPretendsToChangeKinship = true ∧
  g.secretCounselCanConspireInSin = true ∧
  g.falseGreetingsAndOathsConcealHostility = true ∧
  g.wealthAndChildrenCannotShieldOpposition = true ∧
  g.hostileKinshipCannotOverrideFaithfulAllegiance = true

def mujadilaSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 58 / Al-Mujadila witnesses heard complaint, secret counsel audit, and allegiance boundary"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive MujadilaRegister | complaint | repair | counsel | gathering | consultation | allegiance
deriving DecidableEq, Repr, Nonempty

inductive MujadilaInvariant | heardRepairAllegiance
deriving DecidableEq, Repr

def mujadilaRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : MujadilaRegister => MujadilaInvariant.heardRepairAllegiance)
      MujadilaInvariant.heardRepairAllegiance :=
  TruthOneManyNamesWitness.constant_names_agree MujadilaInvariant.heardRepairAllegiance

theorem mujadila_quality_clusters_shape :
    mujadilaQualityClusters.length = 5 ∧
    mujadilaQualityClusters.head? = some .heardDisputeAndZiharRepair ∧
    mujadilaQualityClusters.getLast? = some .falseOathsHostileKinshipAndPartyOfGod := by
  exact ⟨rfl, rfl, rfl⟩

theorem mujadila_sat_witness : mujadilaSat mujadilaInvariantLedger := by
  unfold mujadilaSat mujadilaInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem mujadila_gap_witness : mujadilaGapsExposeBoundary mujadilaGapLedger := by
  unfold mujadilaGapsExposeBoundary mujadilaGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem mujadila_access_archaeological :
    mujadilaSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_mujadila_sura_quality_witness :
    mujadilaQualityClusters.length = 5 ∧
    mujadilaSat mujadilaInvariantLedger ∧
    mujadilaGapsExposeBoundary mujadilaGapLedger ∧
    mujadilaSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : MujadilaRegister => MujadilaInvariant.heardRepairAllegiance)
      MujadilaInvariant.heardRepairAllegiance := by
  exact ⟨mujadila_quality_clusters_shape.left, mujadila_sat_witness, mujadila_gap_witness,
    mujadila_access_archaeological, mujadilaRegistersAgree⟩

end QuranAlMujadilaSuraQualityWitness
end Gnosis.Witnesses.Islam
