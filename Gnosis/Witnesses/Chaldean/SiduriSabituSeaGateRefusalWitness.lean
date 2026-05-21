import Gnosis.Witnesses.Chaldean.IshtarSevenGateRegaliaBodyWitness
import Gnosis.Witnesses.Chaldean.UddusunamirSphinxHadesGateWitness
import Gnosis.Witnesses.Chaldean.WatersOfDeathCrossingWitness

namespace Gnosis.Witnesses.Chaldean
namespace SiduriSabituSeaGateRefusalWitness

/-!
# Siduri-Sabitu Sea-Gate Refusal Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Tablet X,
Izdubar at the sea-coast before the Urhamsi boatman route opens.

This witness isolates the threshold before the death-water crossing. Izdubar
arrives at the sea-coast after jewel-tree wandering. Siduri and Sabitu dwell in
the land beside the sea. Izdubar is visibly afflicted: disease, illness, divine
brand, shame of face, and desire for the distant path. Sabitu sees from afar,
ponders, resolves, judges the message, and shuts her place and gate.

That closure is not decorative refusal. It prevents direct passage by an
unrepaired seeker and forces the route into mediated navigation through
Urhamsi. Gatekeeping here is diagnostic: the boundary reads the body before it
opens the path.

No `sorry`, no new `axiom`.
-/

structure DiseasedSeekerAtSea where
  reachesSeaCoast : Bool := true
  stripesOfAffliction : Bool := true
  struckWithDisease : Bool := true
  illnessCoversBody : Bool := true
  brandOfGodsMarked : Bool := true
  shameOfFace : Bool := true
  faceSetToDistantPath : Bool := true
deriving DecidableEq, Repr

def diseasedSeekerAtSea : DiseasedSeekerAtSea := {}

def diseasedSeekerExposesBoundaryNeed (d : DiseasedSeekerAtSea) : Prop :=
  d.reachesSeaCoast = true ∧
  d.stripesOfAffliction = true ∧
  d.struckWithDisease = true ∧
  d.illnessCoversBody = true ∧
  d.brandOfGodsMarked = true ∧
  d.shameOfFace = true ∧
  d.faceSetToDistantPath = true

structure FemaleSeaGatePair where
  siduriNamed : Bool := true
  sabituNamed : Bool := true
  dwellBesideSea : Bool := true
  boundaryBeforeBoatman : Bool := true
  shoreThresholdPair : Bool := true
deriving DecidableEq, Repr

def femaleSeaGatePair : FemaleSeaGatePair := {}

def siduriSabituShoreThreshold (f : FemaleSeaGatePair) : Prop :=
  f.siduriNamed = true ∧
  f.sabituNamed = true ∧
  f.dwellBesideSea = true ∧
  f.boundaryBeforeBoatman = true ∧
  f.shoreThresholdPair = true

structure SabituDiagnosticClosure where
  seesFromAfar : Bool := true
  pondersInternally : Bool := true
  makesResolution : Bool := true
  asksWhatMessage : Bool := true
  noUprightOneLinePreserved : Bool := true
  shutsPlace : Bool := true
  shutsGate : Bool := true
  izdubarHearsClosure : Bool := true
deriving DecidableEq, Repr

def sabituDiagnosticClosure : SabituDiagnosticClosure := {}

def diagnosticGateClosure (s : SabituDiagnosticClosure) : Prop :=
  s.seesFromAfar = true ∧
  s.pondersInternally = true ∧
  s.makesResolution = true ∧
  s.asksWhatMessage = true ∧
  s.noUprightOneLinePreserved = true ∧
  s.shutsPlace = true ∧
  s.shutsGate = true ∧
  s.izdubarHearsClosure = true

structure RefusalRedirectsToBoatman where
  directGatePassageRefused : Bool := true
  izdubarChallengesClosure : Bool := true
  followingLostLinesBridgeToUrhamsi : Bool := true
  urhamsiBoatmanAppearsNext : Bool := true
  journeyByWaterBeginsAfterGateRefusal : Bool := true
deriving DecidableEq, Repr

def refusalRedirectsToBoatman : RefusalRedirectsToBoatman := {}

def refusalForcesMediatedCrossing (r : RefusalRedirectsToBoatman) : Prop :=
  r.directGatePassageRefused = true ∧
  r.izdubarChallengesClosure = true ∧
  r.followingLostLinesBridgeToUrhamsi = true ∧
  r.urhamsiBoatmanAppearsNext = true ∧
  r.journeyByWaterBeginsAfterGateRefusal = true

theorem siduri_diseased_seeker_exposes_boundary_need :
    diseasedSeekerExposesBoundaryNeed diseasedSeekerAtSea := by
  unfold diseasedSeekerExposesBoundaryNeed diseasedSeekerAtSea
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem siduri_sabitu_shore_threshold :
    siduriSabituShoreThreshold femaleSeaGatePair := by
  unfold siduriSabituShoreThreshold femaleSeaGatePair
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem sabitu_diagnostic_gate_closure :
    diagnosticGateClosure sabituDiagnosticClosure := by
  unfold diagnosticGateClosure sabituDiagnosticClosure
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem siduri_refusal_forces_mediated_crossing :
    refusalForcesMediatedCrossing refusalRedirectsToBoatman := by
  unfold refusalForcesMediatedCrossing refusalRedirectsToBoatman
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem siduri_inherits_waters_sea_gate :
    WatersOfDeathCrossingWitness.seaGateBlocksUnmediatedPassage
      WatersOfDeathCrossingWitness.seaGateRefusal ∧
    diagnosticGateClosure sabituDiagnosticClosure ∧
    refusalForcesMediatedCrossing refusalRedirectsToBoatman := by
  exact ⟨WatersOfDeathCrossingWitness.waters_sea_gate_blocks_unmediated_passage,
    sabitu_diagnostic_gate_closure,
    siduri_refusal_forces_mediated_crossing⟩

theorem siduri_contrasts_hades_gate_opening :
    UddusunamirSphinxHadesGateWitness.sphinxOpensUnderworldGate
      UddusunamirSphinxHadesGateWitness.uddusunamirSphinx ∧
    diagnosticGateClosure sabituDiagnosticClosure := by
  exact ⟨UddusunamirSphinxHadesGateWitness.uddusunamir_sphinx_opens_underworld_gate,
    sabitu_diagnostic_gate_closure⟩

theorem siduri_inherits_body_gate_diagnostics :
    IshtarSevenGateRegaliaBodyWitness.gateIndexedBodyLedger
      IshtarSevenGateRegaliaBodyWitness.bodyLedgerGateProtocol ∧
    diseasedSeekerExposesBoundaryNeed diseasedSeekerAtSea := by
  exact ⟨IshtarSevenGateRegaliaBodyWitness.ishtar_gate_indexed_body_ledger,
    siduri_diseased_seeker_exposes_boundary_need⟩

theorem siduri_sabitu_sea_gate_refusal_witness :
    diseasedSeekerExposesBoundaryNeed diseasedSeekerAtSea ∧
    siduriSabituShoreThreshold femaleSeaGatePair ∧
    diagnosticGateClosure sabituDiagnosticClosure ∧
    refusalForcesMediatedCrossing refusalRedirectsToBoatman := by
  exact ⟨siduri_diseased_seeker_exposes_boundary_need,
    siduri_sabitu_shore_threshold,
    sabitu_diagnostic_gate_closure,
    siduri_refusal_forces_mediated_crossing⟩

end SiduriSabituSeaGateRefusalWitness
end Gnosis.Witnesses.Chaldean
