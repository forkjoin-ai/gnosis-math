import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Gnostic
namespace GospelThomasPearlImageWitness

/-!
# Gospel of Thomas -- Pearl, Rejected Stone, and Concealed Light

Source text: `docs/ebooks/source-texts/gospel-of-thomas.txt`;
text anchor `docs/ebooks/source-texts/gospel-of-thomas.txt:246-350`.

Sat/unseen reading:

Thomas's middle-late cluster makes value legible through rejection and concealment:
the rejected stone is cornerstone, the pearl is bought by selling the lesser
inventory, and the manifest image hides the light in it. The world/body is not
the final object; it is the discovered corpse/body whose recognition places the
knower above the world.

Gap / counterproof:

Commerce, clothing, visible kinship, and external readings of sky/earth are bad
sensors when they displace the living moment.

No `sorry`, no new `axiom`.
-/

structure RejectedValue where
  rejectedStoneCornerstone : Bool
  pearlAloneBought : Bool
  enduringTreasure : Bool
  merchantsDoNotEnter : Bool
  richRenouncesWorld : Bool
deriving DecidableEq, Repr

def thomasRejectedValue : RejectedValue where
  rejectedStoneCornerstone := true
  pearlAloneBought := true
  enduringTreasure := true
  merchantsDoNotEnter := true
  richRenouncesWorld := true

def rejectedValueIsCorner (v : RejectedValue) : Prop :=
  v.rejectedStoneCornerstone = true ∧
  v.pearlAloneBought = true ∧
  v.enduringTreasure = true ∧
  v.merchantsDoNotEnter = true ∧
  v.richRenouncesWorld = true

structure ConcealedLightImage where
  lightAboveAll : Bool
  allFromAndToLight : Bool
  woodStonePresence : Bool
  imageManifestLightConcealed : Bool
  preexistentImagesBearWeight : Bool
deriving DecidableEq, Repr

def thomasConcealedLightImage : ConcealedLightImage where
  lightAboveAll := true
  allFromAndToLight := true
  woodStonePresence := true
  imageManifestLightConcealed := true
  preexistentImagesBearWeight := true

def concealedLightWithinImages (i : ConcealedLightImage) : Prop :=
  i.lightAboveAll = true ∧
  i.allFromAndToLight = true ∧
  i.woodStonePresence = true ∧
  i.imageManifestLightConcealed = true ∧
  i.preexistentImagesBearWeight = true

structure MomentReadingGap where
  fineGarmentsBlind : Bool
  visibleKinshipDisplaced : Bool
  skyEarthRead : Bool
  presentOneNotRead : Bool
  momentUnread : Bool
deriving DecidableEq, Repr

def thomasMomentReadingGap : MomentReadingGap where
  fineGarmentsBlind := true
  visibleKinshipDisplaced := true
  skyEarthRead := true
  presentOneNotRead := true
  momentUnread := true

def externalReadingMissesMoment (g : MomentReadingGap) : Prop :=
  g.fineGarmentsBlind = true ∧
  g.visibleKinshipDisplaced = true ∧
  g.skyEarthRead = true ∧
  g.presentOneNotRead = true ∧
  g.momentUnread = true

theorem thomas_rejected_value_corner :
    rejectedValueIsCorner thomasRejectedValue := by
  unfold rejectedValueIsCorner thomasRejectedValue
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_concealed_light_image :
    concealedLightWithinImages thomasConcealedLightImage := by
  unfold concealedLightWithinImages thomasConcealedLightImage
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_external_reading_gap :
    externalReadingMissesMoment thomasMomentReadingGap := by
  unfold externalReadingMissesMoment thomasMomentReadingGap
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_pearl_centroid :
    Gnosis.GnosisTriptychBraid.cycleSum = Gnosis.GnosisTriptychBraid.truth :=
  Gnosis.GnosisTriptychBraid.cycle_sum_zero

theorem gospel_thomas_pearl_image_witness :
    rejectedValueIsCorner thomasRejectedValue ∧
    concealedLightWithinImages thomasConcealedLightImage ∧
    externalReadingMissesMoment thomasMomentReadingGap ∧
    Gnosis.GnosisTriptychBraid.cycleSum = Gnosis.GnosisTriptychBraid.truth := by
  exact ⟨thomas_rejected_value_corner,
    thomas_concealed_light_image,
    thomas_external_reading_gap,
    thomas_pearl_centroid⟩

end GospelThomasPearlImageWitness
end Gnosis.Witnesses.Gnostic
