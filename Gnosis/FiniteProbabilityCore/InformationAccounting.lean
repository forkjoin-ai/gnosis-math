import Gnosis.FiniteProbabilityCore.ProcessChains

namespace Gnosis
namespace FiniteProbabilityCore
/-! ## Finite information accounting -/

def distributionMassScore
    (distribution : FiniteDistribution) : Nat :=
  distribution.totalMass

def processVisibleInformation
    (process : FiniteProbabilityProcess) : Nat :=
  distributionMassScore process.output

def processShadowInformation
    (process : FiniteProbabilityProcess) : Nat :=
  process.residual

def processAccountedInformation
    (process : FiniteProbabilityProcess) : Nat :=
  processVisibleInformation process + processShadowInformation process

def kernelVisibleInformation
    (kernel : FiniteStochasticKernel) : Nat :=
  distributionMassScore kernel.output

def kernelShadowInformation
    (kernel : FiniteStochasticKernel) : Nat :=
  kernel.lostMass

def kernelAccountedInformation
    (kernel : FiniteStochasticKernel) : Nat :=
  kernelVisibleInformation kernel + kernelShadowInformation kernel

theorem kernel_accounted_information_eq_input
    (kernel : FiniteStochasticKernel) :
    kernelAccountedInformation kernel =
      distributionMassScore kernel.input := by
  unfold kernelAccountedInformation kernelVisibleInformation
  unfold kernelShadowInformation distributionMassScore
  exact finite_stochastic_kernel_balance kernel

theorem process_visible_plus_loss_eq_input
    (process : FiniteProbabilityProcess) :
    processVisibleInformation process + process.massLoss =
      distributionMassScore process.input := by
  unfold processVisibleInformation distributionMassScore
  exact process.balance

theorem process_visible_information_le_input
    (process : FiniteProbabilityProcess) :
    processVisibleInformation process ≤ distributionMassScore process.input := by
  unfold processVisibleInformation distributionMassScore
  exact process_output_mass_le_input process

theorem process_shadow_covers_loss
    (process : FiniteProbabilityProcess) :
    process.massLoss ≤ processShadowInformation process := by
  unfold processShadowInformation
  exact process.lossCovered

theorem process_input_information_le_accounted
    (process : FiniteProbabilityProcess) :
    distributionMassScore process.input ≤
      processAccountedInformation process := by
  unfold processAccountedInformation
  rw [← process_visible_plus_loss_eq_input process]
  exact Nat.add_le_add_left process.lossCovered
    (processVisibleInformation process)

theorem composite_process_shadow_adds
    (composite : ProcessComposite) :
    processShadowInformation composite.toProcess =
      processShadowInformation composite.first +
        processShadowInformation composite.second := rfl

theorem composite_process_accounted_information_adds
    (composite : ProcessComposite) :
    processAccountedInformation composite.toProcess =
      processVisibleInformation composite.toProcess +
        processShadowInformation composite.first +
        processShadowInformation composite.second := by
  unfold processAccountedInformation
  rw [composite_process_shadow_adds]
  exact Eq.symm (Nat.add_assoc
    (processVisibleInformation composite.toProcess)
    (processShadowInformation composite.first)
    (processShadowInformation composite.second))

theorem process_chain_shadow_eq_folded_residual
    (chain : FiniteProbabilityProcessChain) :
    probabilityResidual chain.residualState () =
      processListResidual chain.processes := by
  rw [process_chain_residual_state_eq_residual, chain.residualAccounts]

theorem process_chain_information_loss_covers_mass_loss
    (chain : FiniteProbabilityProcessChain) :
    chain.massLoss ≤ probabilityResidual chain.residualState () := by
  rw [process_chain_residual_state_eq_residual]
  exact process_chain_loss_covered_by_residual chain

theorem process_chain_input_information_le_accounted
    (chain : FiniteProbabilityProcessChain) :
    distributionMassScore chain.input ≤
      distributionMassScore chain.output + chain.residual := by
  unfold distributionMassScore
  rw [← chain.balance]
  exact Nat.add_le_add_left
    (process_chain_loss_covered_by_residual chain)
    chain.output.totalMass

theorem finite_data_processing_process
    (process : FiniteProbabilityProcess) :
    distributionMassScore process.input ≤
      processVisibleInformation process + processShadowInformation process :=
  process_input_information_le_accounted process

theorem finite_data_processing_kernel
    (kernel : FiniteStochasticKernel) :
    distributionMassScore kernel.input =
      kernelVisibleInformation kernel + kernelShadowInformation kernel := by
  exact (kernel_accounted_information_eq_input kernel).symm

end FiniteProbabilityCore
end Gnosis
