/-
  DuchampRetinalTrapWitness.lean
  ==============================

  Marcel Duchamp — retinal painting as trap; readymade pivot; Fountain
  (1917, submitted to Society of Independent Artists as “R. Mutt” — one standard
  dating / pseudonym hook). Hard-culture subversion (in-repo English): a Stirnerite
  wipe of the museum in the conceptual register (`StirnerEgoAndOwnWitness` —
  not a claim Duchamp read Stirner; a kinship tag on refusing a spook
  called “Art-for-the-eye” as supreme).

  The retinal trap: art billed as for the eye — color, form, beauty
  as terminal — reduced here to a low-level biological reflex; the pivot
  denies that aesthetic pixels exhaust art’s type.

  Readymade thesis (prose): “Art” is not a physical property of the
  object but a status bit flipped by agent authority (curator /
  institution / context): the factory urinal stays porcelain; the gallery
  frame supplies the type constructor you dispute in your own metaphysics.

  Repo cousins: `BalthusGeometricStasisWitness` (inframince / infrathin metaphor
  for inner/outer partition — painting floor, not Duchamp’s coin definition);
  `MagritteTreacheryOfImagesWitness` (label ≠ object — cousin on
  sign vs thing); `StirnerEgoAndOwnWitness` (spook cut — kin on museum
  sovereignty); `MarcuseOneDimensionalManWitness` (commodity soul — tension);
  `BaudrillardSimulacraSimulationWitness` (context-led hyperreal); `MachiavelliPrinceOughtIsWitness`
  (Is of power / who names what counts — distant kin to who flips
  the status bit); `ElGrecoElasticRealWitness` (retinal pressure — opposite
  pole: sacred stretch vs Duchamp’s anti-retinal flat).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace DuchampRetinalTrapWitness

/-- Tag: retinal trap — art reduced to eye-service (color / form / beauty as trap). -/
abbrev retinalTrap (claim : Prop) : Prop :=
  claim

/-- Tag: Stirnerite wipe of museum spook-sovereignty (you discharge the analogy). -/
abbrev stirneriteMuseumWipe (claim : Prop) : Prop :=
  claim

/-- Tag: art as status bit / institutional type stamp, not intrinsic matter. -/
abbrev artAsAgentFlippedStatusBit (claim : Prop) : Prop :=
  claim

/-- Tag: readymade — factory object (urinal) without studio hand magic. -/
abbrev readymadeFactoryObject (claim : Prop) : Prop :=
  claim

/-- Tag: context (gallery / signature / submission) creates the Art type. -/
abbrev contextCreatesArtType (claim : Prop) : Prop :=
  claim

/--
  Retinal bundle: trap named + wipe of eye-sovereignty — two tags.
-/
structure AntiRetinalWitness (trap wipe : Prop) where
  trapNamed : retinalTrap trap
  museumWipe : stirneriteMuseumWipe wipe

theorem anti_retinal_conjuncts (T W : Prop) (w : AntiRetinalWitness T W) : T ∧ W :=
  And.intro w.trapNamed w.museumWipe

def buildAntiRetinalWitness (T W : Prop) (hT : T) (hW : W) : AntiRetinalWitness T W :=
  ⟨hT, hW⟩

/--
  Fountain / readymade bundle: factory thing + context supplies Art type.
-/
structure FountainReadymadeWitness (factory context : Prop) where
  porcelain : readymadeFactoryObject factory
  frameFlipsType : contextCreatesArtType context

theorem fountain_conjuncts (F C : Prop) (w : FountainReadymadeWitness F C) : F ∧ C :=
  And.intro w.porcelain w.frameFlipsType

def buildFountainWitness (F C : Prop) (hF : F) (hC : C) : FountainReadymadeWitness F C :=
  ⟨hF, hC⟩

/--
  Status-bit thesis alone (when you want agent authority without the urinal story).
-/
structure StatusBitWitness (bit : Prop) where
  flipped : artAsAgentFlippedStatusBit bit

end DuchampRetinalTrapWitness
