import Gnosis.FiniteProbabilityCore.ChannelsKernels

namespace Gnosis
namespace FiniteProbabilityCore
/-! ## Finite probability programs -/

structure FiniteProbabilityProgram where
  channel : FiniteProbabilityChannel
  observerResidual : ProbabilityResidualState
  deriving Repr

def FiniteProbabilityProgram.input
    (program : FiniteProbabilityProgram) : FiniteDistribution :=
  program.channel.input

def FiniteProbabilityProgram.output
    (program : FiniteProbabilityProgram) : FiniteDistribution :=
  program.channel.output

def FiniteProbabilityProgram.totalResidual
    (program : FiniteProbabilityProgram) : Nat :=
  program.channel.lostMass + probabilityResidual program.observerResidual ()

def FiniteProbabilityProgram.residualState
    (program : FiniteProbabilityProgram) : ProbabilityResidualState :=
  { unobservedMass :=
      program.channel.lostMass + program.observerResidual.unobservedMass
    truncatedMass := program.observerResidual.truncatedMass
    coarseningDebt := program.observerResidual.coarseningDebt }

theorem program_residual_state_eq_total
    (program : FiniteProbabilityProgram) :
    probabilityResidual program.residualState () =
      program.totalResidual := by
  cases program with
  | mk channel observerResidual =>
      cases observerResidual
      simp [FiniteProbabilityProgram.residualState,
        FiniteProbabilityProgram.totalResidual, probabilityResidual,
        Nat.add_assoc]

theorem program_channel_loss_le_total_residual
    (program : FiniteProbabilityProgram) :
    program.channel.lostMass ≤ program.totalResidual := by
  unfold FiniteProbabilityProgram.totalResidual
  exact Nat.le_add_right
    program.channel.lostMass
    (probabilityResidual program.observerResidual ())

theorem program_observer_residual_le_total_residual
    (program : FiniteProbabilityProgram) :
    probabilityResidual program.observerResidual () ≤
      program.totalResidual := by
  unfold FiniteProbabilityProgram.totalResidual
  exact Nat.le_add_left
    (probabilityResidual program.observerResidual ())
    program.channel.lostMass

theorem program_no_hidden_defect
    (program : FiniteProbabilityProgram)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : program.totalResidual ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote program.residualState ())
      observer depth := by
  apply probability_no_hidden_defect
  · rwa [program_residual_state_eq_total]
  · exact hcovers
  · exact hbudget

def losslessProgram
    (distribution : FiniteDistribution)
    (observerResidual : ProbabilityResidualState) :
    FiniteProbabilityProgram :=
  { channel := losslessChannel distribution
    observerResidual := observerResidual }

theorem lossless_program_total_residual_eq_observer
    (distribution : FiniteDistribution)
    (observerResidual : ProbabilityResidualState) :
    (losslessProgram distribution observerResidual).totalResidual =
      probabilityResidual observerResidual () := by
  simp [losslessProgram, losslessChannel,
    FiniteProbabilityProgram.totalResidual]

def addProbabilityResidualState
    (left right : ProbabilityResidualState) : ProbabilityResidualState :=
  { unobservedMass := left.unobservedMass + right.unobservedMass
    truncatedMass := left.truncatedMass + right.truncatedMass
    coarseningDebt := left.coarseningDebt + right.coarseningDebt }

theorem add_probability_residual_state_eq_add
    (left right : ProbabilityResidualState) :
    probabilityResidual (addProbabilityResidualState left right) () =
      probabilityResidual left () + probabilityResidual right () := by
  cases left
  cases right
  simp [addProbabilityResidualState, probabilityResidual]
  omega

structure ProgramComposite where
  first : FiniteProbabilityProgram
  second : FiniteProbabilityProgram
  connects : first.output.totalMass = second.input.totalMass
  deriving Repr

def ProgramComposite.channelComposite
    (composite : ProgramComposite) : ChannelComposite :=
  { first := composite.first.channel
    second := composite.second.channel
    connects := composite.connects }

def ProgramComposite.toProgram
    (composite : ProgramComposite) : FiniteProbabilityProgram :=
  { channel := composite.channelComposite.toChannel
    observerResidual :=
      addProbabilityResidualState
        composite.first.observerResidual
        composite.second.observerResidual }

theorem composite_program_channel_loss_adds
    (composite : ProgramComposite) :
    composite.toProgram.channel.lostMass =
      composite.first.channel.lostMass + composite.second.channel.lostMass := rfl

theorem composite_program_observer_residual_adds
    (composite : ProgramComposite) :
    probabilityResidual composite.toProgram.observerResidual () =
      probabilityResidual composite.first.observerResidual () +
        probabilityResidual composite.second.observerResidual () := by
  exact add_probability_residual_state_eq_add
    composite.first.observerResidual
    composite.second.observerResidual

theorem composite_program_total_residual_adds
    (composite : ProgramComposite) :
    composite.toProgram.totalResidual =
      composite.first.totalResidual + composite.second.totalResidual := by
  unfold FiniteProbabilityProgram.totalResidual
  rw [composite_program_observer_residual_adds]
  rw [composite_program_channel_loss_adds]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_left_comm
    composite.second.channel.lostMass
    (probabilityResidual composite.first.observerResidual ())
    (probabilityResidual composite.second.observerResidual ())]

end FiniteProbabilityCore
end Gnosis
