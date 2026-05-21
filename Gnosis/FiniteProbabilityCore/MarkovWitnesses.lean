import Gnosis.FiniteProbabilityCore.InformationAccounting

namespace Gnosis
namespace FiniteProbabilityCore
/-! ## Kernel chains and finite Markov witnesses -/

structure KernelComposite where
  first : FiniteStochasticKernel
  second : FiniteStochasticKernel
  connects : first.output.totalMass = second.input.totalMass
  deriving Repr

def KernelComposite.channelComposite
    (composite : KernelComposite) : ChannelComposite :=
  { first := composite.first.toChannel
    second := composite.second.toChannel
    connects := composite.connects }

def KernelComposite.toChannel
    (composite : KernelComposite) : FiniteProbabilityChannel :=
  composite.channelComposite.toChannel

theorem composite_kernel_loss_adds
    (composite : KernelComposite) :
    composite.toChannel.lostMass =
      composite.first.lostMass + composite.second.lostMass := rfl

def KernelComposite.toProcess
    (composite : KernelComposite)
    (residual : Nat) : FiniteProbabilityProcess :=
  { input := composite.first.input
    output := composite.second.output
    massLoss := composite.toChannel.lostMass
    residual := composite.toChannel.lostMass + residual
    balance := composite.toChannel.balance
    lossCovered := Nat.le_add_right composite.toChannel.lostMass residual }

theorem composite_kernel_process_residual_eq
    (composite : KernelComposite)
    (residual : Nat) :
    (composite.toProcess residual).residual =
      composite.first.lostMass + composite.second.lostMass + residual := by
  unfold KernelComposite.toProcess
  change composite.toChannel.lostMass + residual =
    composite.first.lostMass + composite.second.lostMass + residual
  rw [composite_kernel_loss_adds]

theorem composite_kernel_process_data_processing
    (composite : KernelComposite)
    (residual : Nat) :
    distributionMassScore composite.first.input ≤
      processVisibleInformation (composite.toProcess residual) +
        processShadowInformation (composite.toProcess residual) :=
  finite_data_processing_process (composite.toProcess residual)

def kernelListLostMass : List FiniteStochasticKernel → Nat
  | [] => 0
  | kernel :: rest => kernel.lostMass + kernelListLostMass rest

def kernelListVisibleInformation : List FiniteStochasticKernel → Nat
  | [] => 0
  | kernel :: rest =>
      kernelVisibleInformation kernel + kernelListVisibleInformation rest

def kernelListAccountedInformation : List FiniteStochasticKernel → Nat
  | [] => 0
  | kernel :: rest =>
      kernelAccountedInformation kernel + kernelListAccountedInformation rest

theorem kernel_list_lost_mass_append
    (left right : List FiniteStochasticKernel) :
    kernelListLostMass (left ++ right) =
      kernelListLostMass left + kernelListLostMass right := by
  induction left with
  | nil => simp [kernelListLostMass]
  | cons kernel rest ih =>
      simp [kernelListLostMass, ih, Nat.add_assoc]

theorem kernel_list_accounted_information_append
    (left right : List FiniteStochasticKernel) :
    kernelListAccountedInformation (left ++ right) =
      kernelListAccountedInformation left +
        kernelListAccountedInformation right := by
  induction left with
  | nil => simp [kernelListAccountedInformation]
  | cons kernel rest ih =>
      simp [kernelListAccountedInformation, ih, Nat.add_assoc]

structure FiniteMarkovWitness where
  kernels : List FiniteStochasticKernel
  shadowResidual : Nat
  deriving Repr

def FiniteMarkovWitness.totalShadow
    (witness : FiniteMarkovWitness) : Nat :=
  kernelListLostMass witness.kernels + witness.shadowResidual

def FiniteMarkovWitness.residualState
    (witness : FiniteMarkovWitness) : ProbabilityResidualState :=
  { unobservedMass := witness.totalShadow
    truncatedMass := 0
    coarseningDebt := 0 }

theorem finite_markov_residual_state_eq_shadow
    (witness : FiniteMarkovWitness) :
    probabilityResidual witness.residualState () =
      witness.totalShadow := by
  simp [FiniteMarkovWitness.residualState, probabilityResidual]

theorem finite_markov_kernel_loss_le_shadow
    (witness : FiniteMarkovWitness) :
    kernelListLostMass witness.kernels ≤ witness.totalShadow := by
  unfold FiniteMarkovWitness.totalShadow
  exact Nat.le_add_right
    (kernelListLostMass witness.kernels)
    witness.shadowResidual

def FiniteMarkovWitness.append
    (left right : FiniteMarkovWitness) : FiniteMarkovWitness :=
  { kernels := left.kernels ++ right.kernels
    shadowResidual := left.shadowResidual + right.shadowResidual }

theorem finite_markov_witness_append_total_shadow
    (left right : FiniteMarkovWitness) :
    (left.append right).totalShadow =
      left.totalShadow + right.totalShadow := by
  unfold FiniteMarkovWitness.append FiniteMarkovWitness.totalShadow
  rw [kernel_list_lost_mass_append]
  simp
  ac_rfl

theorem finite_markov_no_hidden_defect
    (witness : FiniteMarkovWitness)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : witness.totalShadow ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote witness.residualState ())
      observer depth := by
  apply probability_no_hidden_defect
  · rwa [finite_markov_residual_state_eq_shadow]
  · exact hcovers
  · exact hbudget

structure StationaryFiniteMarkovWitness where
  state : FiniteDistribution
  kernel : FiniteStochasticKernel
  stationaryMass : kernel.input.totalMass = state.totalMass ∧
    kernel.output.totalMass = state.totalMass
  shadowResidual : Nat
  deriving Repr

def StationaryFiniteMarkovWitness.totalShadow
    (witness : StationaryFiniteMarkovWitness) : Nat :=
  witness.kernel.lostMass + witness.shadowResidual

def StationaryFiniteMarkovWitness.toMarkovWitness
    (witness : StationaryFiniteMarkovWitness) : FiniteMarkovWitness :=
  { kernels := [witness.kernel]
    shadowResidual := witness.shadowResidual }

theorem stationary_finite_markov_shadow_eq_markov_shadow
    (witness : StationaryFiniteMarkovWitness) :
    witness.toMarkovWitness.totalShadow =
      witness.totalShadow := by
  simp [StationaryFiniteMarkovWitness.toMarkovWitness,
    StationaryFiniteMarkovWitness.totalShadow,
    FiniteMarkovWitness.totalShadow, kernelListLostMass]

theorem stationary_finite_markov_visible_mass_eq_state
    (witness : StationaryFiniteMarkovWitness) :
    kernelVisibleInformation witness.kernel =
      distributionMassScore witness.state := by
  unfold kernelVisibleInformation distributionMassScore
  exact witness.stationaryMass.2

theorem stationary_finite_markov_kernel_loss_zero
    (witness : StationaryFiniteMarkovWitness) :
    witness.kernel.lostMass = 0 := by
  have hbalance := finite_stochastic_kernel_balance witness.kernel
  have hinput := witness.stationaryMass.1
  have houtput := witness.stationaryMass.2
  rw [hinput, houtput] at hbalance
  grind

theorem stationary_finite_markov_total_shadow_eq_residual
    (witness : StationaryFiniteMarkovWitness) :
    witness.totalShadow = witness.shadowResidual := by
  unfold StationaryFiniteMarkovWitness.totalShadow
  rw [stationary_finite_markov_kernel_loss_zero witness]
  simp

theorem stationary_finite_markov_no_hidden_defect
    (witness : StationaryFiniteMarkovWitness)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : witness.totalShadow ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        witness.toMarkovWitness.residualState ())
      observer depth := by
  apply finite_markov_no_hidden_defect
  · rwa [stationary_finite_markov_shadow_eq_markov_shadow]
  · exact hcovers
  · exact hbudget

theorem pleroma_mattress_accounting
    (process : FiniteProbabilityProcess) :
    distributionMassScore process.input ≤
      processVisibleInformation process +
        processShadowInformation process :=
  finite_data_processing_process process

theorem pleroma_mattress_chain_accounting
    (chain : FiniteProbabilityProcessChain) :
    chain.massLoss ≤ probabilityResidual chain.residualState () :=
  process_chain_information_loss_covers_mass_loss chain
end FiniteProbabilityCore
end Gnosis
