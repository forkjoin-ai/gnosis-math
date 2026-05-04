import Gnosis.FailureDurability
import Gnosis.GossipProtocol
import Gnosis.GodFormula

namespace Gnosis

/-!
Init-only gossip-SIR queue kernel bridge.

Local `EpidemiologySIR` namespace mirrors the gossip identity for
recovered/active populations. Rates are `Nat`-valued; geometric
contraction rate is the pair `(3, 4)`.
-/

namespace EpidemiologySIR

structure SIRSetup where
  totalPopulation : Nat
  activeInfected : Nat
  recoveredPopulation : Nat
  hConservation : recoveredPopulation + activeInfected = totalPopulation

-- godWeight comes from `Gnosis.GodFormula`; resolved by the enclosing namespace.

theorem recovery_identity (setup : SIRSetup) :
    godWeight setup.totalPopulation setup.activeInfected =
      setup.recoveredPopulation + 1 := by
  unfold godWeight
  have hLe : setup.activeInfected ≤ setup.totalPopulation := by
    rw [← setup.hConservation]
    exact Nat.le_add_left _ _
  rw [Nat.min_eq_left hLe]
  rw [← setup.hConservation]
  simp

end EpidemiologySIR

def gossipFailureBudget (setup : GossipProtocol.GossipSetup) : Nat :=
  setup.susceptibleNodes

def gossipReplicaCount (setup : GossipProtocol.GossipSetup) : Nat :=
  2 * gossipFailureBudget setup + 1

theorem gossip_interpretation_strict_majority
    (setup : GossipProtocol.GossipSetup) :
    2 * gossipFailureBudget setup < gossipReplicaCount setup := by
  unfold gossipReplicaCount
  exact Nat.lt_succ_self _

structure QueueBoundaryWitnessNat_GossipEpidemiologyQueueKernelBridge where
  beta1 : Nat
  capacity : Nat
  arrivalRate : Nat
  serviceRate : Nat

theorem gossip_susceptible_yields_unit_queue_boundary
    (setup : GossipProtocol.GossipSetup) :
    godWeight setup.totalNodes setup.susceptibleNodes =
      setup.infectedNodes + 1 ∧
    ∃ boundary : QueueBoundaryWitnessNat_GossipEpidemiologyQueueKernelBridge,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = gossipFailureBudget setup ∧
      boundary.serviceRate =
        quorumSize (gossipReplicaCount setup) (gossipFailureBudget setup) := by
  refine ⟨GossipProtocol.infection_identity setup, ?_⟩
  refine ⟨{
    beta1 := 0
    capacity := 1
    arrivalRate := gossipFailureBudget setup
    serviceRate := quorumSize (gossipReplicaCount setup) (gossipFailureBudget setup)
  }, rfl, rfl, rfl, rfl⟩

def sirFailureBudget (setup : EpidemiologySIR.SIRSetup) : Nat :=
  setup.activeInfected

def sirReplicaCount (setup : EpidemiologySIR.SIRSetup) : Nat :=
  2 * sirFailureBudget setup + 1

theorem sir_interpretation_strict_majority
    (setup : EpidemiologySIR.SIRSetup) :
    2 * sirFailureBudget setup < sirReplicaCount setup := by
  unfold sirReplicaCount
  exact Nat.lt_succ_self _

theorem sir_active_infected_yields_unit_queue_boundary
    (setup : EpidemiologySIR.SIRSetup) :
    godWeight setup.totalPopulation setup.activeInfected =
      setup.recoveredPopulation + 1 ∧
    ∃ boundary : QueueBoundaryWitnessNat_GossipEpidemiologyQueueKernelBridge,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = sirFailureBudget setup ∧
      boundary.serviceRate =
        quorumSize (sirReplicaCount setup) (sirFailureBudget setup) := by
  refine ⟨EpidemiologySIR.recovery_identity setup, ?_⟩
  refine ⟨{
    beta1 := 0
    capacity := 1
    arrivalRate := sirFailureBudget setup
    serviceRate := quorumSize (sirReplicaCount setup) (sirFailureBudget setup)
  }, rfl, rfl, rfl, rfl⟩

def gossipSirFailureBudget
    (gossip : GossipProtocol.GossipSetup) (sir : EpidemiologySIR.SIRSetup) : Nat :=
  gossipFailureBudget gossip + sirFailureBudget sir

def gossipSirReplicaCount
    (gossip : GossipProtocol.GossipSetup) (sir : EpidemiologySIR.SIRSetup) : Nat :=
  2 * gossipSirFailureBudget gossip sir + 1

theorem gossip_sir_interpretation_strict_majority
    (gossip : GossipProtocol.GossipSetup) (sir : EpidemiologySIR.SIRSetup) :
    2 * gossipSirFailureBudget gossip sir < gossipSirReplicaCount gossip sir := by
  unfold gossipSirReplicaCount
  exact Nat.lt_succ_self _

theorem gossip_sir_budget_yields_unit_queue_boundary
    (gossip : GossipProtocol.GossipSetup) (sir : EpidemiologySIR.SIRSetup) :
    godWeight gossip.totalNodes gossip.susceptibleNodes =
      gossip.infectedNodes + 1 ∧
    godWeight sir.totalPopulation sir.activeInfected =
      sir.recoveredPopulation + 1 ∧
    gossipSirFailureBudget gossip sir = gossip.susceptibleNodes + sir.activeInfected ∧
    ∃ boundary : QueueBoundaryWitnessNat_GossipEpidemiologyQueueKernelBridge,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = gossipSirFailureBudget gossip sir ∧
      boundary.serviceRate =
        quorumSize (gossipSirReplicaCount gossip sir) (gossipSirFailureBudget gossip sir) := by
  refine ⟨GossipProtocol.infection_identity gossip,
          EpidemiologySIR.recovery_identity sir, rfl, ?_⟩
  refine ⟨{
    beta1 := 0
    capacity := 1
    arrivalRate := gossipSirFailureBudget gossip sir
    serviceRate :=
      quorumSize (gossipSirReplicaCount gossip sir) (gossipSirFailureBudget gossip sir)
  }, rfl, rfl, rfl, rfl⟩

theorem gossip_sir_budget_does_not_force_beta1_equals_budget
    (gossip : GossipProtocol.GossipSetup) (sir : EpidemiologySIR.SIRSetup)
    (hBudgetPos : 0 < gossipSirFailureBudget gossip sir) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat_GossipEpidemiologyQueueKernelBridge,
        boundary.arrivalRate = gossipSirFailureBudget gossip sir →
        boundary.serviceRate =
          quorumSize (gossipSirReplicaCount gossip sir) (gossipSirFailureBudget gossip sir) →
        boundary.beta1 = gossipSirFailureBudget gossip sir) := by
  intro hForces
  rcases gossip_sir_budget_yields_unit_queue_boundary gossip sir with
    ⟨_hG, _hS, _hB, boundary, hBetaZero, _hCap, hArr, hSrv⟩
  have hEq : boundary.beta1 = gossipSirFailureBudget gossip sir := hForces boundary hArr hSrv
  rw [hBetaZero] at hEq
  exact Nat.lt_irrefl 0 (hEq ▸ hBudgetPos)

structure GeometricErgodicityRateNat_GossipEpidemiologyQueueKernelBridge where
  numerator : Nat
  denominator : Nat
  initialBound : Nat
  hRateLtOne : numerator < denominator
  hDenomPos : 0 < denominator
  hInitialBoundPos : 0 < initialBound

def gossipSirGeometricRate
    (gossip : GossipProtocol.GossipSetup) (sir : EpidemiologySIR.SIRSetup) :
    GeometricErgodicityRateNat_GossipEpidemiologyQueueKernelBridge :=
  { numerator := 3
    denominator := 4
    initialBound := gossipSirFailureBudget gossip sir + 1
    hRateLtOne := by decide
    hDenomPos := by decide
    hInitialBoundPos := Nat.succ_pos _ }

theorem gossip_sir_budget_yields_geometric_rate_certificate
    (gossip : GossipProtocol.GossipSetup) (sir : EpidemiologySIR.SIRSetup) :
    godWeight gossip.totalNodes gossip.susceptibleNodes =
      gossip.infectedNodes + 1 ∧
    godWeight sir.totalPopulation sir.activeInfected =
      sir.recoveredPopulation + 1 ∧
    ∃ rate : GeometricErgodicityRateNat_GossipEpidemiologyQueueKernelBridge,
      rate = gossipSirGeometricRate gossip sir ∧
      rate.initialBound = gossipSirFailureBudget gossip sir + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨GossipProtocol.infection_identity gossip,
          EpidemiologySIR.recovery_identity sir, ?_⟩
  refine ⟨gossipSirGeometricRate gossip sir, rfl, rfl, rfl, rfl,
          (gossipSirGeometricRate gossip sir).hRateLtOne,
          (gossipSirGeometricRate gossip sir).hInitialBoundPos⟩

end Gnosis
