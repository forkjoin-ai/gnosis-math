import Gnosis.CadmusDragonTeethWitness
import Gnosis.GreekMonsterErrorPrimitivesWitness
import Gnosis.Witnesses.Chaldean.KarkartiamatDragonSeaMonsterWitness

namespace Gnosis.Witnesses.Folklore
namespace SaintGeorgeDragonTributeWitness

/-!
# Saint George Dragon Tribute Witness

Saint George is useful because the dragon has become civic machinery. The
monster does not merely block a spring or appear as sea-chaos. It imposes a
recurring tribute schedule on the city, converts communal output into threat
maintenance, and finally asks for the royal child. The saintly act breaks the
recurrence instead of optimizing it.

This is a folklore witness, not a historical source claim. It formalizes the
standard dragon-slayer topology: city under recurrence, selected victim,
mounted boundary intervention, dragon subdual, and public coherence after the
loop breaks.

No `sorry`, no new `axiom`.
-/

structure TributeLoopCity where
  dragonThreatAtBoundary : Bool := true
  cityPaysRecurringTribute : Bool := true
  outputFedBackIntoThreat : Bool := true
  lotteryOrSelectionMechanism : Bool := true
  royalHouseEventuallyExposed : Bool := true
deriving DecidableEq, Repr

def tributeLoopCity : TributeLoopCity := {}

def cityCapturedByTributeLoop (c : TributeLoopCity) : Prop :=
  c.dragonThreatAtBoundary = true ∧
  c.cityPaysRecurringTribute = true ∧
  c.outputFedBackIntoThreat = true ∧
  c.lotteryOrSelectionMechanism = true ∧
  c.royalHouseEventuallyExposed = true

structure HostageBoundary where
  maidenOrPrincessSelected : Bool := true
  visibleTerminalOutput : Bool := true
  innocenceUsedAsPayment : Bool := true
  localContractAcceptedUntilInterrupted : Bool := true
deriving DecidableEq, Repr

def hostageBoundary : HostageBoundary := {}

def hostageMarksLoopTerminal (h : HostageBoundary) : Prop :=
  h.maidenOrPrincessSelected = true ∧
  h.visibleTerminalOutput = true ∧
  h.innocenceUsedAsPayment = true ∧
  h.localContractAcceptedUntilInterrupted = true

structure SaintlyIntervention where
  mountedBoundaryAgent : Bool := true
  refusesTributeContract : Bool := true
  subduesOrSlaysDragon : Bool := true
  returnsThreatToPublicView : Bool := true
  breaksRecurrenceRatherThanOptimizingIt : Bool := true
deriving DecidableEq, Repr

def saintlyIntervention : SaintlyIntervention := {}

def tributeLoopBreaker (s : SaintlyIntervention) : Prop :=
  s.mountedBoundaryAgent = true ∧
  s.refusesTributeContract = true ∧
  s.subduesOrSlaysDragon = true ∧
  s.returnsThreatToPublicView = true ∧
  s.breaksRecurrenceRatherThanOptimizingIt = true

structure PostCombatAssembly where
  cityWitnessesDragonDefeat : Bool := true
  publicCoherenceRestored : Bool := true
  conversionOrOathCanBindAssembly : Bool := true
  tributeScheduleTerminated : Bool := true
deriving DecidableEq, Repr

def postCombatAssembly : PostCombatAssembly := {}

def assemblyCoherenceAfterDragon (a : PostCombatAssembly) : Prop :=
  a.cityWitnessesDragonDefeat = true ∧
  a.publicCoherenceRestored = true ∧
  a.conversionOrOathCanBindAssembly = true ∧
  a.tributeScheduleTerminated = true

structure DragonFolkloreDiscipline where
  laterChristianCarrier : Bool := true
  doesNotGovernChaldeanSource : Bool := true
  sharesBoundaryOperatorShape : Bool := true
  preservesTributeSpecificity : Bool := true
deriving DecidableEq, Repr

def dragonFolkloreDiscipline : DragonFolkloreDiscipline := {}

def comparativeDiscipline (d : DragonFolkloreDiscipline) : Prop :=
  d.laterChristianCarrier = true ∧
  d.doesNotGovernChaldeanSource = true ∧
  d.sharesBoundaryOperatorShape = true ∧
  d.preservesTributeSpecificity = true

theorem saint_george_city_captured_by_tribute_loop :
    cityCapturedByTributeLoop tributeLoopCity := by
  unfold cityCapturedByTributeLoop tributeLoopCity
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem saint_george_hostage_marks_loop_terminal :
    hostageMarksLoopTerminal hostageBoundary := by
  unfold hostageMarksLoopTerminal hostageBoundary
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem saint_george_breaks_tribute_loop :
    tributeLoopBreaker saintlyIntervention := by
  unfold tributeLoopBreaker saintlyIntervention
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem saint_george_restores_assembly_coherence :
    assemblyCoherenceAfterDragon postCombatAssembly := by
  unfold assemblyCoherenceAfterDragon postCombatAssembly
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem saint_george_comparative_discipline :
    comparativeDiscipline dragonFolkloreDiscipline := by
  unfold comparativeDiscipline dragonFolkloreDiscipline
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem saint_george_crosses_to_chaldean_dragon_without_flattening :
    comparativeDiscipline dragonFolkloreDiscipline ∧
    Chaldean.KarkartiamatDragonSeaMonsterWitness.dragonActsAsBoundaryOperator
      Chaldean.KarkartiamatDragonSeaMonsterWitness.dragonBoundaryOperator ∧
    Chaldean.KarkartiamatDragonSeaMonsterWitness.seaDragonCarriesFallVector
      Chaldean.KarkartiamatDragonSeaMonsterWitness.dragonFallVector := by
  exact ⟨saint_george_comparative_discipline,
    Chaldean.KarkartiamatDragonSeaMonsterWitness.karkartiamat_acts_as_boundary_operator,
    Chaldean.KarkartiamatDragonSeaMonsterWitness.karkartiamat_carries_fall_vector⟩

theorem saint_george_dragon_tribute_witness :
    cityCapturedByTributeLoop tributeLoopCity ∧
    hostageMarksLoopTerminal hostageBoundary ∧
    tributeLoopBreaker saintlyIntervention ∧
    assemblyCoherenceAfterDragon postCombatAssembly ∧
    comparativeDiscipline dragonFolkloreDiscipline := by
  exact ⟨saint_george_city_captured_by_tribute_loop,
    saint_george_hostage_marks_loop_terminal,
    saint_george_breaks_tribute_loop,
    saint_george_restores_assembly_coherence,
    saint_george_comparative_discipline⟩

end SaintGeorgeDragonTributeWitness
end Gnosis.Witnesses.Folklore
