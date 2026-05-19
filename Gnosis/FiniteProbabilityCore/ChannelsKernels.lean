import Gnosis.FiniteProbabilityCore.Core

namespace Gnosis
namespace FiniteProbabilityCore
/-! ## Finite probability channels -/

structure FiniteProbabilityChannel where
  input : FiniteDistribution
  output : FiniteDistribution
  lostMass : Nat
  balance : output.totalMass + lostMass = input.totalMass
  deriving Repr

theorem channel_output_mass_le_input
    (channel : FiniteProbabilityChannel) :
    channel.output.totalMass ≤ channel.input.totalMass := by
  rw [← channel.balance]
  exact Nat.le_add_right channel.output.totalMass channel.lostMass

theorem channel_loss_mass_le_input
    (channel : FiniteProbabilityChannel) :
    channel.lostMass ≤ channel.input.totalMass := by
  rw [← channel.balance]
  exact Nat.le_add_left channel.lostMass channel.output.totalMass

theorem channel_loss_zero_output_eq_input
    (channel : FiniteProbabilityChannel)
    (hzero : channel.lostMass = 0) :
    channel.output.totalMass = channel.input.totalMass := by
  rw [← channel.balance, hzero, Nat.add_zero]

def losslessChannel
    (distribution : FiniteDistribution) : FiniteProbabilityChannel :=
  { input := distribution
    output := distribution
    lostMass := 0
    balance := by simp }

theorem lossless_channel_output_eq_input
    (distribution : FiniteDistribution) :
    (losslessChannel distribution).output.totalMass =
      (losslessChannel distribution).input.totalMass := rfl

def channelResidualState
    (channel : FiniteProbabilityChannel) : ProbabilityResidualState :=
  { unobservedMass := channel.lostMass
    truncatedMass := 0
    coarseningDebt := 0 }

theorem channel_residual_eq_lost_mass
    (channel : FiniteProbabilityChannel) :
    probabilityResidual (channelResidualState channel) () =
      channel.lostMass := by
  simp [probabilityResidual, channelResidualState]

theorem channel_no_hidden_defect
    (channel : FiniteProbabilityChannel)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : channel.lostMass ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote (channelResidualState channel) ())
      observer depth := by
  apply probability_no_hidden_defect
  · rwa [channel_residual_eq_lost_mass]
  · exact hcovers
  · exact hbudget

structure ChannelComposite where
  first : FiniteProbabilityChannel
  second : FiniteProbabilityChannel
  connects : first.output.totalMass = second.input.totalMass
  deriving Repr

def ChannelComposite.totalLostMass
    (composite : ChannelComposite) : Nat :=
  composite.first.lostMass + composite.second.lostMass

theorem composite_loss_covers_first
    (composite : ChannelComposite) :
    composite.first.lostMass ≤ composite.totalLostMass := by
  unfold ChannelComposite.totalLostMass
  exact Nat.le_add_right composite.first.lostMass composite.second.lostMass

theorem composite_loss_covers_second
    (composite : ChannelComposite) :
    composite.second.lostMass ≤ composite.totalLostMass := by
  unfold ChannelComposite.totalLostMass
  exact Nat.le_add_left composite.second.lostMass composite.first.lostMass

def ChannelComposite.toChannel
    (composite : ChannelComposite) : FiniteProbabilityChannel :=
  { input := composite.first.input
    output := composite.second.output
    lostMass := composite.totalLostMass
    balance := by
      unfold ChannelComposite.totalLostMass
      rw [← composite.first.balance]
      rw [composite.connects]
      rw [← composite.second.balance]
      rw [Nat.add_assoc]
      rw [Nat.add_comm composite.second.lostMass composite.first.lostMass] }

theorem composite_channel_loss_adds
    (composite : ChannelComposite) :
    composite.toChannel.lostMass =
      composite.first.lostMass + composite.second.lostMass := rfl

/-! ## Row-wise finite stochastic kernels -/

structure FiniteKernelRow where
  inputMass : Nat
  outputWeights : List Nat
  lostMass : Nat
  balance : sumNat outputWeights + lostMass = inputMass
  deriving Repr

def FiniteKernelRow.outputMass
    (row : FiniteKernelRow) : Nat :=
  sumNat row.outputWeights

theorem kernel_row_output_mass_le_input
    (row : FiniteKernelRow) :
    row.outputMass ≤ row.inputMass := by
  unfold FiniteKernelRow.outputMass
  rw [← row.balance]
  exact Nat.le_add_right (sumNat row.outputWeights) row.lostMass

theorem kernel_row_loss_le_input
    (row : FiniteKernelRow) :
    row.lostMass ≤ row.inputMass := by
  rw [← row.balance]
  exact Nat.le_add_left row.lostMass (sumNat row.outputWeights)

def kernelRowsInputMass : List FiniteKernelRow → Nat
  | [] => 0
  | row :: rest => row.inputMass + kernelRowsInputMass rest

def kernelRowsOutputMass : List FiniteKernelRow → Nat
  | [] => 0
  | row :: rest => row.outputMass + kernelRowsOutputMass rest

def kernelRowsLostMass : List FiniteKernelRow → Nat
  | [] => 0
  | row :: rest => row.lostMass + kernelRowsLostMass rest

theorem kernel_rows_balance
    (rows : List FiniteKernelRow) :
    kernelRowsOutputMass rows + kernelRowsLostMass rows =
      kernelRowsInputMass rows := by
  induction rows with
  | nil =>
      simp [kernelRowsOutputMass, kernelRowsLostMass, kernelRowsInputMass]
  | cons row rest ih =>
      unfold kernelRowsOutputMass kernelRowsLostMass kernelRowsInputMass
      unfold FiniteKernelRow.outputMass
      rw [← Nat.add_assoc]
      rw [Nat.add_right_comm (sumNat row.outputWeights)]
      rw [Nat.add_assoc]
      rw [row.balance]
      rw [ih]

structure FiniteStochasticKernel where
  input : FiniteDistribution
  output : FiniteDistribution
  rows : List FiniteKernelRow
  inputAccounts : kernelRowsInputMass rows = input.totalMass
  outputAccounts : kernelRowsOutputMass rows = output.totalMass
  deriving Repr

def FiniteStochasticKernel.lostMass
    (kernel : FiniteStochasticKernel) : Nat :=
  kernelRowsLostMass kernel.rows

theorem finite_stochastic_kernel_balance
    (kernel : FiniteStochasticKernel) :
    kernel.output.totalMass + kernel.lostMass =
      kernel.input.totalMass := by
  unfold FiniteStochasticKernel.lostMass
  rw [← kernel.outputAccounts]
  rw [← kernel.inputAccounts]
  exact kernel_rows_balance kernel.rows

def FiniteStochasticKernel.toChannel
    (kernel : FiniteStochasticKernel) : FiniteProbabilityChannel :=
  { input := kernel.input
    output := kernel.output
    lostMass := kernel.lostMass
    balance := finite_stochastic_kernel_balance kernel }

theorem finite_stochastic_kernel_channel_loss_eq_rows
    (kernel : FiniteStochasticKernel) :
    kernel.toChannel.lostMass = kernelRowsLostMass kernel.rows := rfl
end FiniteProbabilityCore
end Gnosis
