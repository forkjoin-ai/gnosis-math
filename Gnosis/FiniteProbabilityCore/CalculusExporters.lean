import Gnosis.FiniteProbabilityCore.SnowshoeCompletedCovers

namespace Gnosis
namespace FiniteProbabilityCore
/-! ## Observer-pattern process adapters -/

def processOfResidual
    (channel : FiniteProbabilityChannel)
    (residual : Nat) : FiniteProbabilityProcess :=
  { input := channel.input
    output := channel.output
    massLoss := channel.lostMass
    residual := channel.lostMass + residual
    balance := channel.balance
    lossCovered := Nat.le_add_right channel.lostMass residual }

theorem process_of_residual_residual_eq
    (channel : FiniteProbabilityChannel)
    (residual : Nat) :
    (processOfResidual channel residual).residual =
      channel.lostMass + residual := rfl

def FiniteStochasticKernel.toProcess
    (kernel : FiniteStochasticKernel)
    (residual : Nat) : FiniteProbabilityProcess :=
  processOfResidual kernel.toChannel residual

theorem finite_stochastic_kernel_process_residual_eq
    (kernel : FiniteStochasticKernel)
    (residual : Nat) :
    (kernel.toProcess residual).residual =
      kernelRowsLostMass kernel.rows + residual := rfl

def queueProcess
    (channel : FiniteProbabilityChannel)
    (state : QueueResidualState) : FiniteProbabilityProcess :=
  processOfResidual channel (queueResidual state ())

theorem queue_process_residual_eq
    (channel : FiniteProbabilityChannel)
    (state : QueueResidualState) :
    (queueProcess channel state).residual =
      channel.lostMass + queueResidual state () := rfl

def thermodynamicProcess
    (channel : FiniteProbabilityChannel)
    (state : ThermodynamicResidualState) : FiniteProbabilityProcess :=
  processOfResidual channel (thermodynamicResidual state ())

theorem thermodynamic_process_residual_eq
    (channel : FiniteProbabilityChannel)
    (state : ThermodynamicResidualState) :
    (thermodynamicProcess channel state).residual =
      channel.lostMass + thermodynamicResidual state () := rfl

def meshRoutingProcess
    (channel : FiniteProbabilityChannel)
    (state : MeshRoutingResidualState) : FiniteProbabilityProcess :=
  processOfResidual channel (meshRoutingResidual state ())

theorem mesh_routing_process_residual_eq
    (channel : FiniteProbabilityChannel)
    (state : MeshRoutingResidualState) :
    (meshRoutingProcess channel state).residual =
      channel.lostMass + meshRoutingResidual state () := rfl

def attentionProcess
    (channel : FiniteProbabilityChannel)
    (state : AttentionResidualState) : FiniteProbabilityProcess :=
  processOfResidual channel (attentionResidual state ())

theorem attention_process_residual_eq
    (channel : FiniteProbabilityChannel)
    (state : AttentionResidualState) :
    (attentionProcess channel state).residual =
      channel.lostMass + attentionResidual state () := rfl

def finiteApproximationProcess
    (channel : FiniteProbabilityChannel)
    (state : FiniteApproximationResidualState) : FiniteProbabilityProcess :=
  processOfResidual channel (finiteApproximationResidual state ())

theorem finite_approximation_process_residual_eq
    (channel : FiniteProbabilityChannel)
    (state : FiniteApproximationResidualState) :
    (finiteApproximationProcess channel state).residual =
      channel.lostMass + finiteApproximationResidual state () := rfl

end FiniteProbabilityCore
end Gnosis
