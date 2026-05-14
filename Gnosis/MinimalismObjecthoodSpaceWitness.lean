/-
  MinimalismObjecthoodSpaceWitness.lean
  =====================================

  Minimalism / literalist objecthood as a witness for meaning distributed across
  object, viewer, space, light, and material.

  Historical floor: in the mid-1960s, artists such as Donald Judd and Robert
  Morris made simple geometric objects with little visible artist's touch:
  boxes, stacks, slabs, industrial materials, serial forms. Michael Fried's
  "Art and Objecthood" attacked this literalist tendency as theatrical: the work
  needed the viewer's duration, movement, and surrounding room to complete it.
  The minimalist defense treated that dependence as the point: remove emotion,
  genius, and pictorial illusion so space, light, material, and bodily encounter
  become visible.

  Formal reading in this repository:

  * Fried sees a real hazard: `theatricalObjectDependsOnViewerDuration`.
  * Minimalism sees a real disclosure: `literalMaterialRevealsSpaceLight`.
  * Fried fails as total theory if `selfContainedArtworkClaimsExhaustion`.
  * Minimalism fails as total theory if `emotionlessObjectClaimsExhaustion`.
  * the bridge is `installationFeelingInSpace`: the question shifts from only
    "what does this mean?" to "what state does this object produce in this space?"

  This file does not adjudicate Fried or Minimalism. It names the categorical
  transition from autonomous picture/object to spatial encounter while retaining
  the failure modes on both sides.

  Repo cousins: `GreenbergRosenbergAbstractExpressionismWitness` (surface/action
  non-collapse); `DuchampRetinalTrapWitness` (object/status bit);
  `DisegnoColoreWitness` (literal color/light); `AboriginalSonglineInterfaceWitness`
  (relation-bearing interface vs coordinate capture); `TopologicalCinema`
  (framed perception as topology).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace MinimalismObjecthoodSpaceWitness

/-- Tag: literalist object depends on viewer duration / movement / room. -/
abbrev theatricalObjectDependsOnViewerDuration (claim : Prop) : Prop :=
  claim

/-- Tag: true art claimed as self-contained presentness. -/
abbrev selfContainedArtworkClaimsExhaustion (claim : Prop) : Prop :=
  claim

/-- Tag: literal material reveals space and light. -/
abbrev literalMaterialRevealsSpaceLight (claim : Prop) : Prop :=
  claim

/-- Tag: removal of touch / genius / emotion claims to exhaust the work. -/
abbrev emotionlessObjectClaimsExhaustion (claim : Prop) : Prop :=
  claim

/-- Tag: installation art shifts meaning into embodied feeling in space. -/
abbrev installationFeelingInSpace (claim : Prop) : Prop :=
  claim

/--
  Fried bundle: theatrical dependence plus self-contained-art demand.
-/
structure FriedObjecthoodWitness (theatrical selfContained : Prop) where
  theatricality : theatricalObjectDependsOnViewerDuration theatrical
  presentnessDemand : selfContainedArtworkClaimsExhaustion selfContained

theorem fried_objecthood_conjuncts
    (T S : Prop) (w : FriedObjecthoodWitness T S) : T ∧ S :=
  And.intro w.theatricality w.presentnessDemand

def buildFriedObjecthoodWitness
    (T S : Prop) (hT : T) (hS : S) : FriedObjecthoodWitness T S :=
  ⟨hT, hS⟩

/--
  Minimalist bundle: material/space/light disclosure plus anti-expression overreach.
-/
structure MinimalistDefenseWitness (material antiExpression : Prop) where
  spaceLight : literalMaterialRevealsSpaceLight material
  emotionlessTotality : emotionlessObjectClaimsExhaustion antiExpression

theorem minimalist_defense_conjuncts
    (M A : Prop) (w : MinimalistDefenseWitness M A) : M ∧ A :=
  And.intro w.spaceLight w.emotionlessTotality

def buildMinimalistDefenseWitness
    (M A : Prop) (hM : M) (hA : A) : MinimalistDefenseWitness M A :=
  ⟨hM, hA⟩

/--
  Bridge bundle: the spatial encounter is real, but neither Fried's
  self-contained presentness nor minimalist anti-expression exhausts the work.
-/
structure MinimalismInstallationBridge
    (theatrical selfContained material antiExpression installation : Prop) where
  fried : FriedObjecthoodWitness theatrical selfContained
  minimalist : MinimalistDefenseWitness material antiExpression
  spatialShift : installationFeelingInSpace installation

theorem minimalism_installation_bridge_conjuncts
    (T S M A I : Prop) (w : MinimalismInstallationBridge T S M A I) :
    T ∧ S ∧ M ∧ A ∧ I :=
  And.intro w.fried.theatricality
    (And.intro w.fried.presentnessDemand
      (And.intro w.minimalist.spaceLight
        (And.intro w.minimalist.emotionlessTotality w.spatialShift)))

def buildMinimalismInstallationBridge
    (T S M A I : Prop) (hT : T) (hS : S) (hM : M) (hA : A) (hI : I) :
    MinimalismInstallationBridge T S M A I :=
  ⟨buildFriedObjecthoodWitness T S hT hS, buildMinimalistDefenseWitness M A hM hA, hI⟩

end MinimalismObjecthoodSpaceWitness
