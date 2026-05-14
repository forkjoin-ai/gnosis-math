/-
  DeathOfAuthorInstitutionalCritiqueWitness.lean
  =================================================

  Roland Barthes / "Death of the Author" as a postmodern meaning-ownership
  witness: the artist's intent no longer closes the work, but viewer sovereignty
  can also become a totalizing myth if it denies the institution that frames
  reception.

  Historical floor: by the late 1960s, debates around authorship and reception
  challenged the traditional view that a work's meaning is unlocked by the
  artist's biography and intention. The postmodern turn relocates meaning into
  the reader/viewer and their cultural, gendered, historical, and institutional
  position. Institutional Critique follows by asking who installed the frame,
  who guards the archive, who writes the wall text, and who gets admitted as
  viewer or artist.

  Formal reading in this repository:

  * traditional author sovereignty maps to `artistIntentClaimsMeaningOwnership`.
  * post-completion reception maps to `viewerContextProducesMeaning`.
  * authorial exhaustion fails as `artistBiographyClaimsExhaustion`.
  * viewer-only exhaustion fails as `viewerSovereigntyClaimsExhaustion`.
  * institutional critique maps to `institutionFramesMeaningPower`.
  * the bridge is `meaningSurvivesAuthorAsRelation`: meaning persists after
    completion as a relation among work, viewer, culture, history, and frame.

  This file does not prove a theory of Barthes, hermeneutics, or museums. It
  names the categorical failure: no single owner closes meaning after the work
  enters public circulation.

  Repo cousins: `DuchampRetinalTrapWitness` (institutional status bit);
  `MagritteTreacheryOfImagesWitness` (sign vs object); `BorgesOnExactitudeInScienceWitness`
  (model/meaning pathology); `AboriginalSonglineInterfaceWitness` (relation-bearing
  interface); `BeninBronzeArchiveFailureWitness` (archive without context);
  `PopArtDisruptionInformationWitness` (boundary disruption as knowledge).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace DeathOfAuthorInstitutionalCritiqueWitness

/-- Tag: artist intent claims ownership of the work's meaning. -/
abbrev artistIntentClaimsMeaningOwnership (claim : Prop) : Prop :=
  claim

/-- Tag: artist biography is treated as the exhaustive key to the work. -/
abbrev artistBiographyClaimsExhaustion (claim : Prop) : Prop :=
  claim

/-- Tag: viewer context produces meaning after completion. -/
abbrev viewerContextProducesMeaning (claim : Prop) : Prop :=
  claim

/-- Tag: viewer sovereignty claims to exhaust meaning on its own. -/
abbrev viewerSovereigntyClaimsExhaustion (claim : Prop) : Prop :=
  claim

/-- Tag: museum/gallery/archive frame participates in meaning and power. -/
abbrev institutionFramesMeaningPower (claim : Prop) : Prop :=
  claim

/-- Tag: meaning survives author as relation, not as a single owned payload. -/
abbrev meaningSurvivesAuthorAsRelation (claim : Prop) : Prop :=
  claim

/--
  Traditional bundle: authorial intent plus biographical key.
-/
structure AuthorSovereigntyWitness (intent biography : Prop) where
  intentOwns : artistIntentClaimsMeaningOwnership intent
  biographyKey : artistBiographyClaimsExhaustion biography

theorem author_sovereignty_conjuncts
    (I B : Prop) (w : AuthorSovereigntyWitness I B) : I ∧ B :=
  And.intro w.intentOwns w.biographyKey

def buildAuthorSovereigntyWitness
    (I B : Prop) (hI : I) (hB : B) : AuthorSovereigntyWitness I B :=
  ⟨hI, hB⟩

/--
  Postmodern reception bundle: viewer context plus viewer-sovereignty overreach.
-/
structure ViewerReceptionWitness (context sovereignty : Prop) where
  contextMakes : viewerContextProducesMeaning context
  viewerTotality : viewerSovereigntyClaimsExhaustion sovereignty

theorem viewer_reception_conjuncts
    (C S : Prop) (w : ViewerReceptionWitness C S) : C ∧ S :=
  And.intro w.contextMakes w.viewerTotality

def buildViewerReceptionWitness
    (C S : Prop) (hC : C) (hS : S) : ViewerReceptionWitness C S :=
  ⟨hC, hS⟩

/--
  Institution bundle: the frame itself carries meaning-power.
-/
structure InstitutionalCritiqueWitness (frame : Prop) where
  institutionFrame : institutionFramesMeaningPower frame

/--
  Bridge bundle: author, viewer, and institution are all visible, while meaning
  is not owned by any one of them as an exhaustive source.
-/
structure DeathOfAuthorBridge
    (intent biography context sovereignty institution relation : Prop) where
  author : AuthorSovereigntyWitness intent biography
  viewer : ViewerReceptionWitness context sovereignty
  critique : InstitutionalCritiqueWitness institution
  relationalMeaning : meaningSurvivesAuthorAsRelation relation

theorem death_of_author_bridge_conjuncts
    (I B C S F R : Prop) (w : DeathOfAuthorBridge I B C S F R) :
    I ∧ B ∧ C ∧ S ∧ F ∧ R :=
  And.intro w.author.intentOwns
    (And.intro w.author.biographyKey
      (And.intro w.viewer.contextMakes
        (And.intro w.viewer.viewerTotality
          (And.intro w.critique.institutionFrame w.relationalMeaning))))

def buildDeathOfAuthorBridge
    (I B C S F R : Prop)
    (hI : I) (hB : B) (hC : C) (hS : S) (hF : F) (hR : R) :
    DeathOfAuthorBridge I B C S F R :=
  ⟨buildAuthorSovereigntyWitness I B hI hB,
    buildViewerReceptionWitness C S hC hS,
    ⟨hF⟩,
    hR⟩

end DeathOfAuthorInstitutionalCritiqueWitness
