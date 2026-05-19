import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Gnostic
namespace GospelPhilipNameForgeryWitness

/-!
# Gospel of Philip -- Name Forgery and Living Name

Source text: `docs/ebooks/source-texts/gospel-of-philip.txt`;
text anchor `docs/ebooks/source-texts/gospel-of-philip.txt:36-62`.

Sat/unseen reading:

Philip opens a more dangerous name theory than a simple "many names, one
truth" pluralism. Names are necessary because truth teaches the one through many
interfaces, but worldly names are also the attack surface: archons can move good
names onto non-good things and bind the free agent through that counterfeit
mapping.

Invariant:

  * worldly opposites dissolve back to origin;
  * names heard in the world can divert thought from correct to incorrect;
  * the Father's name is known by those who have it but is not spoken;
  * truth brings names into the world for our sake;
  * truth is one, many, and teaches the one through many in love.

Gap / counterproof:

  * a name can be semantically hostile even when it sounds holy;
  * archon name-forgery tries to turn the free one into a slave;
  * therefore lexical piety is not Sat unless the name assignment agrees with
    the living witness.

Projection:

  * `TruthOneManyNamesWitness.manyNamesAgree` supplies the positive criterion:
    many names are legitimate only when they agree on one witness;
  * the counterfeit map is recorded separately as an antitheorem, not admitted
    as a second truth.

No `sorry`, no new `axiom`.
-/

inductive PhilipName where
  | father
  | son
  | light
  | resurrection
deriving DecidableEq, Repr, Nonempty

inductive PhilipTruth where
  | livingWitness
deriving DecidableEq, Repr

def legitimatePhilipNames :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : PhilipName => PhilipTruth.livingWitness)
      PhilipTruth.livingWitness :=
  TruthOneManyNamesWitness.constant_names_agree PhilipTruth.livingWitness

theorem philip_living_name_unique (w : PhilipTruth)
    (hw :
      TruthOneManyNamesWitness.manyNamesAgree
        (fun _ : PhilipName => PhilipTruth.livingWitness)
        w) :
    PhilipTruth.livingWitness = w :=
  TruthOneManyNamesWitness.unique_witness_of_many_names
    (fun _ : PhilipName => PhilipTruth.livingWitness)
    PhilipTruth.livingWitness
    w
    legitimatePhilipNames
    hw

structure WorldlyNameHazard where
  worldlyNamesDeceive : Bool
  divertsCorrectToIncorrect : Bool
  holyWordsCanMislead : Bool
  aeonNameNotWorldlyName : Bool
deriving DecidableEq, Repr

def philipWorldlyNameHazard : WorldlyNameHazard where
  worldlyNamesDeceive := true
  divertsCorrectToIncorrect := true
  holyWordsCanMislead := true
  aeonNameNotWorldlyName := true

def namesAreAttackSurface (h : WorldlyNameHazard) : Prop :=
  h.worldlyNamesDeceive = true ∧
  h.divertsCorrectToIncorrect = true ∧
  h.holyWordsCanMislead = true ∧
  h.aeonNameNotWorldlyName = true

structure TruthNameInterface where
  truthBroughtNamesForUs : Bool
  cannotLearnWithoutNames : Bool
  truthOneThing : Bool
  truthManyThings : Bool
  teachesOneThroughManyInLove : Bool
deriving DecidableEq, Repr

def philipTruthNameInterface : TruthNameInterface where
  truthBroughtNamesForUs := true
  cannotLearnWithoutNames := true
  truthOneThing := true
  truthManyThings := true
  teachesOneThroughManyInLove := true

def namesCanTeachWhenAligned (i : TruthNameInterface) : Prop :=
  i.truthBroughtNamesForUs = true ∧
  i.cannotLearnWithoutNames = true ∧
  i.truthOneThing = true ∧
  i.truthManyThings = true ∧
  i.teachesOneThroughManyInLove = true

structure ArchonNameForgery where
  sawKinshipWithGood : Bool
  tookGoodNames : Bool
  assignedToNotGood : Bool
  deceivesThroughNames : Bool
  bindsFreeAsSlave : Bool
deriving DecidableEq, Repr

def philipArchonNameForgery : ArchonNameForgery where
  sawKinshipWithGood := true
  tookGoodNames := true
  assignedToNotGood := true
  deceivesThroughNames := true
  bindsFreeAsSlave := true

def counterfeitNamesAreNotSat (f : ArchonNameForgery) : Prop :=
  f.sawKinshipWithGood = true ∧
  f.tookGoodNames = true ∧
  f.assignedToNotGood = true ∧
  f.deceivesThroughNames = true ∧
  f.bindsFreeAsSlave = true

theorem philip_names_are_attack_surface :
    namesAreAttackSurface philipWorldlyNameHazard := by
  unfold namesAreAttackSurface philipWorldlyNameHazard
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem philip_names_teach_when_aligned :
    namesCanTeachWhenAligned philipTruthNameInterface := by
  unfold namesCanTeachWhenAligned philipTruthNameInterface
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem philip_name_forgery_counterproof :
    counterfeitNamesAreNotSat philipArchonNameForgery := by
  unfold counterfeitNamesAreNotSat philipArchonNameForgery
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Master witness: Philip does not license naive name-pluralism. Many names are
valid when they converge on the living witness; counterfeit name assignment is
the hostile case and becomes an antitheorem against lexical piety. -/
theorem gospel_philip_name_forgery_witness :
    namesAreAttackSurface philipWorldlyNameHazard ∧
    namesCanTeachWhenAligned philipTruthNameInterface ∧
    counterfeitNamesAreNotSat philipArchonNameForgery ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : PhilipName => PhilipTruth.livingWitness)
      PhilipTruth.livingWitness := by
  exact ⟨philip_names_are_attack_surface,
    philip_names_teach_when_aligned,
    philip_name_forgery_counterproof,
    legitimatePhilipNames⟩

end GospelPhilipNameForgeryWitness
end Gnosis.Witnesses.Gnostic
