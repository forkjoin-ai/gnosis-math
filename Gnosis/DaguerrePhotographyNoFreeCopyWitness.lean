import Init

/-
  DaguerrePhotographyNoFreeCopyWitness.lean
  ========================================

  Louis Daguerre's public daguerreotype reveal (1839) as an art-theory witness:
  the panic that photography would kill painting, and the counter-claim that
  photographic art is not raw mechanical copying, and digital existence is not
  meaninglessness.

  Historical floor: the Delaroche line "from today, painting is dead" is often
  reported in this debate, but attribution and wording are scholarship-sensitive.
  This file treats it as the operator tag for an anxiety: if a machine can record
  appearances, then painting loses its recorder monopoly.

  Formal reading in this repository:

  * the critic's error maps to `mechanicalCopyKillsPainting`: confusing
    resemblance capture with the whole artistic function.
  * the defender's reply maps to `existenceCreatesDeletionLiability`: lighting,
    composition, timing, chemistry, subject choice, presentation, storage, and
    deletion risk cross a visibility/status boundary. The daguerreotype is not
    just a free duplicate.
  * the value claim maps to `mustBeDeletedThereforeValuable`: if a mark, plate,
    file, or record must be deleted, then its existence has causal weight. The
    deletion obligation is the witness that it was not meaningless.
  * the art-historical result maps to `paintingFreedFromRecorderDuty`: once
    photography owns a large part of recorder work, painting can move toward
    impression, abstraction, and concept without pretending its value was only
    mimetic accuracy.

  Cost boundary: this does NOT contradict `CopyStoreEraseCostStructure`, where
  raw fork-copy is free. The daguerreotype-as-art claim is not raw fork-copy; it
  is measurement plus storage plus public status assignment plus possible
  deletion liability. For that reason it sits nearer `NoCloningTaxEqualsBuleCost`
  and `DuchampRetinalTrapWitness`: the thing becomes art by paying framing /
  selection / persistence / institution-visible costs. Nothing digital is
  meaningless merely because it is digital; if it persists enough to require
  deletion, it already has operational value.

  Repo cousins: `DuchampRetinalTrapWitness` (art not exhausted by retinal
  surface); `DisegnoColoreWitness` (design / light registers); `CopyStoreEraseCostStructure`
  (copy/store/erase cost split); `NoCloningTaxEqualsBuleCost` (status-changing
  measurement has positive bule cost); `MagritteTreacheryOfImagesWitness`
  (image is not the object).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace DaguerrePhotographyNoFreeCopyWitness

/-- Tag: critic panic that mechanical resemblance makes painting obsolete. -/
abbrev mechanicalCopyKillsPainting (claim : Prop) : Prop :=
  claim

/-- Tag: resemblance capture is narrower than artistic value. -/
abbrev recorderFunctionNotWholeArt (claim : Prop) : Prop :=
  claim

/-- Tag: existence creates deletion liability; persistence is not nothing. -/
abbrev existenceCreatesDeletionLiability (claim : Prop) : Prop :=
  claim

/-- Tag: the need to delete a record witnesses value through causal weight. -/
abbrev mustBeDeletedThereforeValuable (claim : Prop) : Prop :=
  claim

/-- Tag: photographic presentation crosses a public status boundary. -/
abbrev photographAsStatusChangingMeasurement (claim : Prop) : Prop :=
  claim

/-- Tag: painting is released from recorder duty toward impression / abstraction. -/
abbrev paintingFreedFromRecorderDuty (claim : Prop) : Prop :=
  claim

/--
  Critic bundle: the panic and its narrowing assumption.
-/
structure PhotographyPanicWitness (death recorder : Prop) where
  deathCry : mechanicalCopyKillsPainting death
  narrowedArt : recorderFunctionNotWholeArt recorder

theorem panic_conjuncts (D R : Prop) (w : PhotographyPanicWitness D R) : D ∧ R :=
  And.intro w.deathCry w.narrowedArt

def buildPanicWitness (D R : Prop) (hD : D) (hR : R) : PhotographyPanicWitness D R :=
  ⟨hD, hR⟩

/--
  Defender bundle: photographic art pays persistence/deletion and status costs.
-/
structure PhotographicArtWitness (liability status : Prop) where
  deletionLiability : existenceCreatesDeletionLiability liability
  statusCrossing : photographAsStatusChangingMeasurement status

theorem photographic_art_conjuncts (S T : Prop) (w : PhotographicArtWitness S T) :
    S ∧ T :=
  And.intro w.deletionLiability w.statusCrossing

def buildPhotographicArtWitness (S T : Prop) (hS : S) (hT : T) :
    PhotographicArtWitness S T :=
  ⟨hS, hT⟩

/--
  Value bundle: if the record must be deleted, its existence carried value.
-/
structure DeletionValueWitness (value : Prop) where
  valuable : mustBeDeletedThereforeValuable value

/--
  Result bundle: photography changes painting's job without killing painting.
-/
structure PaintingAfterPhotographyWitness (freedom : Prop) where
  released : paintingFreedFromRecorderDuty freedom

/--
  Full bridge: panic + defender reply + deletion-value claim + downstream release of painting.
-/
structure DaguerreBridgeWitness (death recorder liability status value freedom : Prop) where
  critic : PhotographyPanicWitness death recorder
  defender : PhotographicArtWitness liability status
  deletionValue : DeletionValueWitness value
  result : PaintingAfterPhotographyWitness freedom

theorem daguerre_bridge_conjuncts
    (D R L T V F : Prop) (w : DaguerreBridgeWitness D R L T V F) :
    D ∧ R ∧ L ∧ T ∧ V ∧ F :=
  And.intro w.critic.deathCry
    (And.intro w.critic.narrowedArt
      (And.intro w.defender.deletionLiability
        (And.intro w.defender.statusCrossing
          (And.intro w.deletionValue.valuable w.result.released))))

def buildDaguerreBridge
    (D R L T V F : Prop) (hD : D) (hR : R) (hL : L) (hT : T) (hV : V) (hF : F) :
    DaguerreBridgeWitness D R L T V F :=
  ⟨buildPanicWitness D R hD hR, buildPhotographicArtWitness L T hL hT, ⟨hV⟩, ⟨hF⟩⟩

end DaguerrePhotographyNoFreeCopyWitness
