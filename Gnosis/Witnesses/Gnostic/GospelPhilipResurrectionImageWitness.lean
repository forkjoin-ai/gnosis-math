import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Gnostic
namespace GospelPhilipResurrectionImageWitness

/-!
# Gospel of Philip -- Resurrection Before Death and Image Becoming

Source text: `docs/ebooks/source-texts/gospel-of-philip.txt`;
text anchor `docs/ebooks/source-texts/gospel-of-philip.txt:92-188`.

Sat/unseen reading:

Philip reverses ordinary resurrection timing: one rises first, then dies. The
body is not dismissed as trash; the soul is a precious thing in a contemptible
container, and whatever language one uses about rising is still spoken from the
flesh. The deeper rule is image-becoming: what one truly sees in the Aeon, one
becomes.

Gap / counterproof:

Nakedness is misdiagnosed. Those who wear flesh are naked; those who unclothe
are not. Likewise, ordinary sight sees without becoming, but Aeon sight changes
the observer into the seen.

No `sorry`, no new `axiom`.
-/

structure ResurrectionTiming where
  risesBeforeDeath : Bool
  deathAfterResurrection : Bool
  valuableSoulInLowBody : Bool
  fleshWordSpiritBlood : Bool
  nothingSaidOutsideFlesh : Bool
deriving DecidableEq, Repr

def philipResurrectionTiming : ResurrectionTiming where
  risesBeforeDeath := true
  deathAfterResurrection := true
  valuableSoulInLowBody := true
  fleshWordSpiritBlood := true
  nothingSaidOutsideFlesh := true

def resurrectionIsPriorAcquisition (r : ResurrectionTiming) : Prop :=
  r.risesBeforeDeath = true ∧
  r.deathAfterResurrection = true ∧
  r.valuableSoulInLowBody = true ∧
  r.fleshWordSpiritBlood = true ∧
  r.nothingSaidOutsideFlesh = true

structure VisibilityBecoming where
  seesSpiritBecomesSpirit : Bool
  seesChristBecomesChrist : Bool
  seesFatherBecomesFather : Bool
  seesSelfThere : Bool
  whatYouSeeYouBecome : Bool
deriving DecidableEq, Repr

def philipVisibilityBecoming : VisibilityBecoming where
  seesSpiritBecomesSpirit := true
  seesChristBecomesChrist := true
  seesFatherBecomesFather := true
  seesSelfThere := true
  whatYouSeeYouBecome := true

def aeonSightTransforms (v : VisibilityBecoming) : Prop :=
  v.seesSpiritBecomesSpirit = true ∧
  v.seesChristBecomesChrist = true ∧
  v.seesFatherBecomesFather = true ∧
  v.seesSelfThere = true ∧
  v.whatYouSeeYouBecome = true

structure ImageAccess where
  waterFirePurify : Bool
  visibleByVisible : Bool
  hiddenByHidden : Bool
  appearsAsReceivable : Bool
  disciplesMadeGreatToSeeGreatness : Bool
deriving DecidableEq, Repr

def philipImageAccess : ImageAccess where
  waterFirePurify := true
  visibleByVisible := true
  hiddenByHidden := true
  appearsAsReceivable := true
  disciplesMadeGreatToSeeGreatness := true

def accessRequiresMatchedCapacity (a : ImageAccess) : Prop :=
  a.waterFirePurify = true ∧
  a.visibleByVisible = true ∧
  a.hiddenByHidden = true ∧
  a.appearsAsReceivable = true ∧
  a.disciplesMadeGreatToSeeGreatness = true

theorem philip_resurrection_prior :
    resurrectionIsPriorAcquisition philipResurrectionTiming := by
  unfold resurrectionIsPriorAcquisition philipResurrectionTiming
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem philip_aeon_sight_transforms :
    aeonSightTransforms philipVisibilityBecoming := by
  unfold aeonSightTransforms philipVisibilityBecoming
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem philip_access_capacity :
    accessRequiresMatchedCapacity philipImageAccess := by
  unfold accessRequiresMatchedCapacity philipImageAccess
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem philip_image_recovery_shape :
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom :=
  Gnosis.GnosisTriptychBraid.two_step_recovery

theorem gospel_philip_resurrection_image_witness :
    resurrectionIsPriorAcquisition philipResurrectionTiming ∧
    aeonSightTransforms philipVisibilityBecoming ∧
    accessRequiresMatchedCapacity philipImageAccess ∧
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom := by
  exact ⟨philip_resurrection_prior,
    philip_aeon_sight_transforms,
    philip_access_capacity,
    philip_image_recovery_shape⟩

end GospelPhilipResurrectionImageWitness
end Gnosis.Witnesses.Gnostic
