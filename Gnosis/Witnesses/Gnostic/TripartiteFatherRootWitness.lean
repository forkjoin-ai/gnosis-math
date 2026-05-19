import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Gnostic
namespace TripartiteFatherRootWitness

/-!
# Tripartite Tractate -- Father as Root Beyond Names

Source text: `docs/ebooks/source-texts/tripartite-tractate.txt`;
text anchor `docs/ebooks/source-texts/tripartite-tractate.txt:9-124`.

Sat/unseen reading:

The tractate opens with an apophatic root protocol. The Father is single like a
number, but not solitary, because Father entails Son. He is root with tree,
branches, and fruit, while no spoken or conceived name applies to him in himself.
Names are permitted as honor according to the receiver's capacity, not as
capture.

Gap / counterproof:

Any account that supplies a prior model, material, coworker, place, or external
cause is explicitly ignorant. The source is not a craftsman inside a workspace;
he is the root from which workspace, speech, and naming capacity derive.

No `sorry`, no new `axiom`.
-/

inductive RootHonorName where
  | father
  | good
  | complete
  | root
deriving DecidableEq, Repr, Nonempty

inductive RootWitness where
  | apophaticRoot
deriving DecidableEq, Repr

def rootHonorNamesAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : RootHonorName => RootWitness.apophaticRoot)
      RootWitness.apophaticRoot :=
  TruthOneManyNamesWitness.constant_names_agree RootWitness.apophaticRoot

structure ApophaticRoot where
  unbegotten : Bool
  withoutBeginningEnd : Bool
  immutable : Bool
  rootTreeBranchesFruit : Bool
  givesWithoutWeariness : Bool
  noExternalCause : Bool
deriving DecidableEq, Repr

def tripartiteApophaticRoot : ApophaticRoot where
  unbegotten := true
  withoutBeginningEnd := true
  immutable := true
  rootTreeBranchesFruit := true
  givesWithoutWeariness := true
  noExternalCause := true

def fatherRootInvariant (r : ApophaticRoot) : Prop :=
  r.unbegotten = true ∧
  r.withoutBeginningEnd = true ∧
  r.immutable = true ∧
  r.rootTreeBranchesFruit = true ∧
  r.givesWithoutWeariness = true ∧
  r.noExternalCause = true

structure NameCaptureGap where
  noNameAppliesInSelf : Bool
  namesOnlyHonorByCapacity : Bool
  mindCannotConceive : Bool
  speechCannotConvey : Bool
  eyeCannotSee : Bool
  handCannotGrasp : Bool
deriving DecidableEq, Repr

def tripartiteNameCaptureGap : NameCaptureGap where
  noNameAppliesInSelf := true
  namesOnlyHonorByCapacity := true
  mindCannotConceive := true
  speechCannotConvey := true
  eyeCannotSee := true
  handCannotGrasp := true

def nameCaptureFails (g : NameCaptureGap) : Prop :=
  g.noNameAppliesInSelf = true ∧
  g.namesOnlyHonorByCapacity = true ∧
  g.mindCannotConceive = true ∧
  g.speechCannotConvey = true ∧
  g.eyeCannotSee = true ∧
  g.handCannotGrasp = true

structure SonChurchBeginning where
  sonFirstbornOnly : Bool
  churchFromBeginning : Bool
  manyKissesUnity : Bool
  imperishableSpirits : Bool
  sonRestsChurch : Bool
  fatherRestsSon : Bool
deriving DecidableEq, Repr

def tripartiteSonChurchBeginning : SonChurchBeginning where
  sonFirstbornOnly := true
  churchFromBeginning := true
  manyKissesUnity := true
  imperishableSpirits := true
  sonRestsChurch := true
  fatherRestsSon := true

def sonChurchCoeternalPattern (s : SonChurchBeginning) : Prop :=
  s.sonFirstbornOnly = true ∧
  s.churchFromBeginning = true ∧
  s.manyKissesUnity = true ∧
  s.imperishableSpirits = true ∧
  s.sonRestsChurch = true ∧
  s.fatherRestsSon = true

theorem tripartite_father_root :
    fatherRootInvariant tripartiteApophaticRoot := by
  unfold fatherRootInvariant tripartiteApophaticRoot
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tripartite_name_capture_gap :
    nameCaptureFails tripartiteNameCaptureGap := by
  unfold nameCaptureFails tripartiteNameCaptureGap
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tripartite_son_church_beginning :
    sonChurchCoeternalPattern tripartiteSonChurchBeginning := by
  unfold sonChurchCoeternalPattern tripartiteSonChurchBeginning
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tripartite_father_root_witness :
    fatherRootInvariant tripartiteApophaticRoot ∧
    nameCaptureFails tripartiteNameCaptureGap ∧
    sonChurchCoeternalPattern tripartiteSonChurchBeginning ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : RootHonorName => RootWitness.apophaticRoot)
      RootWitness.apophaticRoot := by
  exact ⟨tripartite_father_root,
    tripartite_name_capture_gap,
    tripartite_son_church_beginning,
    rootHonorNamesAgree⟩

end TripartiteFatherRootWitness
end Gnosis.Witnesses.Gnostic
