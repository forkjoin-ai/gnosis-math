import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Gnostic
namespace TripartiteAeonicExtensionWitness

/-!
# Tripartite Tractate -- Aeonic Extension Without Separation

Source text: `docs/ebooks/source-texts/tripartite-tractate.txt`;
text anchor `docs/ebooks/source-texts/tripartite-tractate.txt:125-359`.

Sat/unseen reading:

Aeonic emanation is extension, not severance. The Father is spring, root, body,
and unity whose streams, branches, members, aeons, and names remain partitioned
in an indivisible way. Multiplicity is legitimate when it is harmonious
extension from the one, not cast-off independence.

Gap / counterproof:

Names become false when they imply separation. The Son bears all names without
being divided into them; the aeons are many names of one Father, not independent
origins.

No `sorry`, no new `axiom`.
-/

inductive AeonicName where
  | spring
  | root
  | body
  | aeon
deriving DecidableEq, Repr, Nonempty

inductive AeonicTruth where
  | indivisibleExtension
deriving DecidableEq, Repr

def aeonicNamesAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AeonicName => AeonicTruth.indivisibleExtension)
      AeonicTruth.indivisibleExtension :=
  TruthOneManyNamesWitness.constant_names_agree AeonicTruth.indivisibleExtension

structure SeededAeons where
  fatherThoughtAsPlace : Bool
  aeonsAsSeedFetusWord : Bool
  nameFatherGivenByVoice : Bool
  searchForSource : Bool
  faultlessnessWithheldWithoutEnvy : Bool
  sonLightReceivableByCapacity : Bool
deriving DecidableEq, Repr

def tripartiteSeededAeons : SeededAeons where
  fatherThoughtAsPlace := true
  aeonsAsSeedFetusWord := true
  nameFatherGivenByVoice := true
  searchForSource := true
  faultlessnessWithheldWithoutEnvy := true
  sonLightReceivableByCapacity := true

def aeonsGrowByCapacity (a : SeededAeons) : Prop :=
  a.fatherThoughtAsPlace = true ∧
  a.aeonsAsSeedFetusWord = true ∧
  a.nameFatherGivenByVoice = true ∧
  a.searchForSource = true ∧
  a.faultlessnessWithheldWithoutEnvy = true ∧
  a.sonLightReceivableByCapacity = true

structure SingleNameTotalities where
  allNamesWithoutFalsification : Bool
  formOfFormless : Bool
  wordOfUnutterable : Bool
  unityOfMixedTotalities : Bool
  notDividedIntoNames : Bool
  whollyHimselfEveryOne : Bool
deriving DecidableEq, Repr

def tripartiteSingleNameTotalities : SingleNameTotalities where
  allNamesWithoutFalsification := true
  formOfFormless := true
  wordOfUnutterable := true
  unityOfMixedTotalities := true
  notDividedIntoNames := true
  whollyHimselfEveryOne := true

def singleNameContainsMany (s : SingleNameTotalities) : Prop :=
  s.allNamesWithoutFalsification = true ∧
  s.formOfFormless = true ∧
  s.wordOfUnutterable = true ∧
  s.unityOfMixedTotalities = true ∧
  s.notDividedIntoNames = true ∧
  s.whollyHimselfEveryOne = true

structure ExtensionAnalogy where
  emanationNotSeparation : Bool
  springStreamsCanals : Bool
  rootBranchesFruit : Bool
  bodyMembersIndivisible : Bool
  unityAndMultiplicity : Bool
  smallGreatNamesByCapacity : Bool
deriving DecidableEq, Repr

def tripartiteExtensionAnalogy : ExtensionAnalogy where
  emanationNotSeparation := true
  springStreamsCanals := true
  rootBranchesFruit := true
  bodyMembersIndivisible := true
  unityAndMultiplicity := true
  smallGreatNamesByCapacity := true

def extensionWithoutSeparation (e : ExtensionAnalogy) : Prop :=
  e.emanationNotSeparation = true ∧
  e.springStreamsCanals = true ∧
  e.rootBranchesFruit = true ∧
  e.bodyMembersIndivisible = true ∧
  e.unityAndMultiplicity = true ∧
  e.smallGreatNamesByCapacity = true

theorem tripartite_aeons_grow_by_capacity :
    aeonsGrowByCapacity tripartiteSeededAeons := by
  unfold aeonsGrowByCapacity tripartiteSeededAeons
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tripartite_single_name_many :
    singleNameContainsMany tripartiteSingleNameTotalities := by
  unfold singleNameContainsMany tripartiteSingleNameTotalities
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tripartite_extension_without_separation :
    extensionWithoutSeparation tripartiteExtensionAnalogy := by
  unfold extensionWithoutSeparation tripartiteExtensionAnalogy
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tripartite_aeonic_extension_witness :
    aeonsGrowByCapacity tripartiteSeededAeons ∧
    singleNameContainsMany tripartiteSingleNameTotalities ∧
    extensionWithoutSeparation tripartiteExtensionAnalogy ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AeonicName => AeonicTruth.indivisibleExtension)
      AeonicTruth.indivisibleExtension := by
  exact ⟨tripartite_aeons_grow_by_capacity,
    tripartite_single_name_many,
    tripartite_extension_without_separation,
    aeonicNamesAgree⟩

end TripartiteAeonicExtensionWitness
end Gnosis.Witnesses.Gnostic
