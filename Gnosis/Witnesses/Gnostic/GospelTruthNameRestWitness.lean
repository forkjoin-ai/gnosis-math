import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Gnostic
namespace GospelTruthNameRestWitness

/-!
# Gospel of Truth -- Real Name and Resting Root

Source text: `docs/ebooks/source-texts/gospel-of-truth.txt`;
text anchor `docs/ebooks/source-texts/gospel-of-truth.txt:276-360`.

Sat/unseen reading:

The closing movement radicalizes the name doctrine: the real name is not drawn
from lexicons or common naming. It is the Son as pronounced name of the Father,
and the emanations return to their roots as their own place of rest.

Gap / counterproof:

Borrowed names and external labels cannot carry the real name. A thing that does
not exist has no name; a thing that exists with its name is known from its root.

No `sorry`, no new `axiom`.
-/

inductive ClosingNameIndex where
  | father
  | son
  | root
deriving DecidableEq, Repr, Nonempty

inductive ClosingNameTruth where
  | realName
deriving DecidableEq, Repr

def closingNamesAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : ClosingNameIndex => ClosingNameTruth.realName)
      ClosingNameTruth.realName :=
  TruthOneManyNamesWitness.constant_names_agree ClosingNameTruth.realName

theorem closing_name_unique (w : ClosingNameTruth)
    (hw :
      TruthOneManyNamesWitness.manyNamesAgree
        (fun _ : ClosingNameIndex => ClosingNameTruth.realName)
        w) :
    ClosingNameTruth.realName = w :=
  TruthOneManyNamesWitness.unique_witness_of_many_names
    (fun _ : ClosingNameIndex => ClosingNameTruth.realName)
    ClosingNameTruth.realName
    w
    closingNamesAgree
    hw

structure RealNameProtocol where
  sonIsFatherName : Bool
  nameInvisible : Bool
  notFromLexicons : Bool
  notBorrowed : Bool
  pronouncedByPerfectOne : Bool
  compassionFindsNameInFather : Bool
deriving DecidableEq, Repr

def gospelRealNameProtocol : RealNameProtocol where
  sonIsFatherName := true
  nameInvisible := true
  notFromLexicons := true
  notBorrowed := true
  pronouncedByPerfectOne := true
  compassionFindsNameInFather := true

def realNameIsNotExternalLabel (p : RealNameProtocol) : Prop :=
  p.sonIsFatherName = true ∧
  p.nameInvisible = true ∧
  p.notFromLexicons = true ∧
  p.notBorrowed = true ∧
  p.pronouncedByPerfectOne = true ∧
  p.compassionFindsNameInFather = true

structure RootRestReturn where
  speaksFromOrigin : Bool
  hastensToReturn : Bool
  ownPlaceIsPleroma : Bool
  rootsInFather : Bool
  rootLiftsUpward : Bool
  headIsRest : Bool
deriving DecidableEq, Repr

def gospelRootRestReturn : RootRestReturn where
  speaksFromOrigin := true
  hastensToReturn := true
  ownPlaceIsPleroma := true
  rootsInFather := true
  rootLiftsUpward := true
  headIsRest := true

def rootReturnsToRest (r : RootRestReturn) : Prop :=
  r.speaksFromOrigin = true ∧
  r.hastensToReturn = true ∧
  r.ownPlaceIsPleroma = true ∧
  r.rootsInFather = true ∧
  r.rootLiftsUpward = true ∧
  r.headIsRest = true

structure BlessedPlace where
  noHades : Bool
  noEnvyMoaningDeath : Bool
  restInTheOneWhoRests : Bool
  notSearchingForTruth : Bool
  fatherInThemAndTheyInFather : Bool
  nothingLacking : Bool
  perfectLightSeed : Bool
deriving DecidableEq, Repr

def gospelBlessedPlace : BlessedPlace where
  noHades := true
  noEnvyMoaningDeath := true
  restInTheOneWhoRests := true
  notSearchingForTruth := true
  fatherInThemAndTheyInFather := true
  nothingLacking := true
  perfectLightSeed := true

def restBeyondSearch (b : BlessedPlace) : Prop :=
  b.noHades = true ∧
  b.noEnvyMoaningDeath = true ∧
  b.restInTheOneWhoRests = true ∧
  b.notSearchingForTruth = true ∧
  b.fatherInThemAndTheyInFather = true ∧
  b.nothingLacking = true ∧
  b.perfectLightSeed = true

theorem gospel_real_name_protocol :
    realNameIsNotExternalLabel gospelRealNameProtocol := by
  unfold realNameIsNotExternalLabel gospelRealNameProtocol
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gospel_root_rest_return :
    rootReturnsToRest gospelRootRestReturn := by
  unfold rootReturnsToRest gospelRootRestReturn
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gospel_blessed_place :
    restBeyondSearch gospelBlessedPlace := by
  unfold restBeyondSearch gospelBlessedPlace
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gospel_truth_name_rest_witness :
    realNameIsNotExternalLabel gospelRealNameProtocol ∧
    rootReturnsToRest gospelRootRestReturn ∧
    restBeyondSearch gospelBlessedPlace ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : ClosingNameIndex => ClosingNameTruth.realName)
      ClosingNameTruth.realName := by
  exact ⟨gospel_real_name_protocol,
    gospel_root_rest_return,
    gospel_blessed_place,
    closingNamesAgree⟩

end GospelTruthNameRestWitness
end Gnosis.Witnesses.Gnostic
