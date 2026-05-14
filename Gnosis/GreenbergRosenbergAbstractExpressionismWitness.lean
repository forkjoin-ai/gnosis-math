/-
  GreenbergRosenbergAbstractExpressionismWitness.lean
  ===================================================

  Abstract Expressionism criticism as a witness for two partial truths and two
  total-theory failures: Clement Greenberg's formalism and Harold Rosenberg's
  action painting.

  Historical floor: Greenberg's formalist pressure treats painting as most
  honest when it admits its medium: flat support, surface, paint, optical
  organization, and refusal of theatrical story or illusionistic window.
  Rosenberg's action-painting pressure treats the canvas as an arena of action:
  the work is not only an image but the trace of physical decision, risk,
  struggle, and movement.

  Formal reading in this repository:

  * Greenberg sees a real constraint: `mediumPurityExposesFlatness`.
  * Rosenberg sees a real trace: `canvasArenaRecordsAction`.
  * Greenberg fails as total theory when `formalismClaimsExhaustion`.
  * Rosenberg fails as total theory when `actionMythClaimsExhaustion`.
  * the honest bridge is `surfaceAndActionDoNotCollapse`: finished surface and
    recorded action are distinct but composable registers.

  Machine-failure reading: the critic becomes a machine when a useful register
  is promoted into an exhaustive ontology. Medium purity can reject lived action;
  heroic action can hide surface, color, material constraint, and viewer-facing
  composition. The witness keeps both partial truths and both failure modes
  visible.

  Repo cousins: `DisegnoColoreWitness` (construction vs literal color/light);
  `DuchampRetinalTrapWitness` (retinal surface as disputed target);
  `DaguerrePhotographyNoFreeCopyWitness` (painting released from recorder duty);
  `BaconVelazquezPopeStudiesWitness` (body under pressure);
  `DaliParanoiacCriticalWitness` (methodical delirium / trace discipline).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace GreenbergRosenbergAbstractExpressionismWitness

/-- Tag: painting admits flat support / surface instead of false window depth. -/
abbrev mediumPurityExposesFlatness (claim : Prop) : Prop :=
  claim

/-- Tag: paint as paint; material surface is not merely a vehicle for story. -/
abbrev paintMaterialityIsLoadBearing (claim : Prop) : Prop :=
  claim

/-- Tag: the canvas is an arena in which action occurred. -/
abbrev canvasArenaRecordsAction (claim : Prop) : Prop :=
  claim

/-- Tag: gesture / movement / risk leave a temporal trace in the artifact. -/
abbrev gestureLeavesTemporalTrace (claim : Prop) : Prop :=
  claim

/-- Wrong move: medium formalism claims to exhaust the painting. -/
abbrev formalismClaimsExhaustion (claim : Prop) : Prop :=
  claim

/-- Wrong move: heroic action myth claims to exhaust the painting. -/
abbrev actionMythClaimsExhaustion (claim : Prop) : Prop :=
  claim

/-- Bridge: surface-form and action-trace are distinct registers, not one identity. -/
abbrev surfaceAndActionDoNotCollapse (claim : Prop) : Prop :=
  claim

/--
  Greenberg bundle: medium purity + paint materiality.
-/
structure FormalismWitness (flatness materiality : Prop) where
  surface : mediumPurityExposesFlatness flatness
  paint : paintMaterialityIsLoadBearing materiality

theorem formalism_conjuncts (F M : Prop) (w : FormalismWitness F M) : F ∧ M :=
  And.intro w.surface w.paint

def buildFormalismWitness (F M : Prop) (hF : F) (hM : M) : FormalismWitness F M :=
  ⟨hF, hM⟩

/--
  Rosenberg bundle: canvas as arena + gesture as temporal trace.
-/
structure ActionPaintingWitness (arena trace : Prop) where
  actionSite : canvasArenaRecordsAction arena
  movementTrace : gestureLeavesTemporalTrace trace

theorem action_painting_conjuncts (A T : Prop) (w : ActionPaintingWitness A T) : A ∧ T :=
  And.intro w.actionSite w.movementTrace

def buildActionPaintingWitness (A T : Prop) (hA : A) (hT : T) :
    ActionPaintingWitness A T :=
  ⟨hA, hT⟩

/--
  Failure bundle: each critic becomes wrong only when a partial register is
  promoted to an exhaustive theory.
-/
structure TotalTheoryFailureWitness (formalismTotal actionTotal : Prop) where
  greenbergOverreach : formalismClaimsExhaustion formalismTotal
  rosenbergOverreach : actionMythClaimsExhaustion actionTotal

theorem total_theory_failure_conjuncts
    (F A : Prop) (w : TotalTheoryFailureWitness F A) : F ∧ A :=
  And.intro w.greenbergOverreach w.rosenbergOverreach

def buildTotalTheoryFailureWitness (F A : Prop) (hF : F) (hA : A) :
    TotalTheoryFailureWitness F A :=
  ⟨hF, hA⟩

/--
  Bridge bundle: finished surface and recorded action are both visible, without
  reducing one to the other; the two totalizing readings are tracked as failure
  modes, not accepted as conclusions.
-/
structure AbstractExpressionismBridge
    (flatness materiality arena trace formalismTotal actionTotal distinction : Prop) where
  formalism : FormalismWitness flatness materiality
  action : ActionPaintingWitness arena trace
  failures : TotalTheoryFailureWitness formalismTotal actionTotal
  notCollapsed : surfaceAndActionDoNotCollapse distinction

theorem abstract_expressionism_bridge_conjuncts
    (F M A T GF RA D : Prop) (w : AbstractExpressionismBridge F M A T GF RA D) :
    F ∧ M ∧ A ∧ T ∧ GF ∧ RA ∧ D :=
  And.intro w.formalism.surface
    (And.intro w.formalism.paint
      (And.intro w.action.actionSite
        (And.intro w.action.movementTrace
          (And.intro w.failures.greenbergOverreach
            (And.intro w.failures.rosenbergOverreach w.notCollapsed)))))

def buildAbstractExpressionismBridge
    (F M A T GF RA D : Prop)
    (hF : F) (hM : M) (hA : A) (hT : T) (hGF : GF) (hRA : RA) (hD : D) :
    AbstractExpressionismBridge F M A T GF RA D :=
  ⟨buildFormalismWitness F M hF hM,
    buildActionPaintingWitness A T hA hT,
    buildTotalTheoryFailureWitness GF RA hGF hRA,
    hD⟩

end GreenbergRosenbergAbstractExpressionismWitness
