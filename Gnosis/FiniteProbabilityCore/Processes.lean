import Gnosis.FiniteProbabilityCore.Programs

namespace Gnosis
namespace FiniteProbabilityCore
/-! ## Finite probability process contracts -/

structure FiniteProbabilityProcess where
  input : FiniteDistribution
  output : FiniteDistribution
  massLoss : Nat
  residual : Nat
  balance : output.totalMass + massLoss = input.totalMass
  lossCovered : massLoss ≤ residual
  deriving Repr

def FiniteProbabilityProcess.residualState
    (process : FiniteProbabilityProcess) : ProbabilityResidualState :=
  { unobservedMass := process.residual
    truncatedMass := 0
    coarseningDebt := 0 }

theorem process_residual_state_eq_residual
    (process : FiniteProbabilityProcess) :
    probabilityResidual process.residualState () =
      process.residual := by
  simp [FiniteProbabilityProcess.residualState, probabilityResidual]

def FiniteProbabilityProgram.toProcess
    (program : FiniteProbabilityProgram) : FiniteProbabilityProcess :=
  { input := program.input
    output := program.output
    massLoss := program.channel.lostMass
    residual := program.totalResidual
    balance := program.channel.balance
    lossCovered := program_channel_loss_le_total_residual program }

theorem program_process_residual_eq_total
    (program : FiniteProbabilityProgram) :
    program.toProcess.residual = program.totalResidual := rfl

theorem process_output_mass_le_input
    (process : FiniteProbabilityProcess) :
    process.output.totalMass ≤ process.input.totalMass := by
  rw [← process.balance]
  exact Nat.le_add_right process.output.totalMass process.massLoss

theorem process_mass_loss_le_input
    (process : FiniteProbabilityProcess) :
    process.massLoss ≤ process.input.totalMass := by
  rw [← process.balance]
  exact Nat.le_add_left process.massLoss process.output.totalMass

theorem process_no_hidden_defect
    (process : FiniteProbabilityProcess)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : process.residual ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote process.residualState ())
      observer depth := by
  apply probability_no_hidden_defect
  · rwa [process_residual_state_eq_residual]
  · exact hcovers
  · exact hbudget

structure ProcessComposite where
  first : FiniteProbabilityProcess
  second : FiniteProbabilityProcess
  connects : first.output.totalMass = second.input.totalMass
  deriving Repr

def ProcessComposite.toProcess
    (composite : ProcessComposite) : FiniteProbabilityProcess :=
  { input := composite.first.input
    output := composite.second.output
    massLoss := composite.first.massLoss + composite.second.massLoss
    residual := composite.first.residual + composite.second.residual
    balance := by
      rw [← composite.first.balance]
      rw [composite.connects]
      rw [← composite.second.balance]
      rw [Nat.add_assoc]
      rw [Nat.add_comm composite.second.massLoss composite.first.massLoss]
    lossCovered := by
      exact Nat.add_le_add
        composite.first.lossCovered
        composite.second.lossCovered }

theorem composite_process_mass_loss_adds
    (composite : ProcessComposite) :
    composite.toProcess.massLoss =
      composite.first.massLoss + composite.second.massLoss := rfl

theorem composite_process_residual_adds
    (composite : ProcessComposite) :
    composite.toProcess.residual =
      composite.first.residual + composite.second.residual := rfl

def identityProcess
    (distribution : FiniteDistribution) : FiniteProbabilityProcess :=
  { input := distribution
    output := distribution
    massLoss := 0
    residual := 0
    balance := by simp
    lossCovered := Nat.le_refl 0 }

theorem identity_process_visible_eq_input
    (distribution : FiniteDistribution) :
    (identityProcess distribution).output.totalMass =
      distribution.totalMass := rfl

theorem identity_process_shadow_zero
    (distribution : FiniteDistribution) :
    (identityProcess distribution).residual = 0 := rfl

theorem left_identity_process_residual
    (process : FiniteProbabilityProcess) :
    ({ first := identityProcess process.input
       second := process
       connects := rfl : ProcessComposite }).toProcess.residual =
      process.residual := by
  simp [ProcessComposite.toProcess, identityProcess]

theorem right_identity_process_residual
    (process : FiniteProbabilityProcess) :
    ({ first := process
       second := identityProcess process.output
       connects := rfl : ProcessComposite }).toProcess.residual =
      process.residual := by
  simp [ProcessComposite.toProcess, identityProcess]

structure ProcessTriple where
  first : FiniteProbabilityProcess
  second : FiniteProbabilityProcess
  third : FiniteProbabilityProcess
  connectsFirstSecond : first.output.totalMass = second.input.totalMass
  connectsSecondThird : second.output.totalMass = third.input.totalMass
  deriving Repr

def ProcessTriple.totalResidual
    (triple : ProcessTriple) : Nat :=
  triple.first.residual + triple.second.residual + triple.third.residual

def ProcessTriple.totalMassLoss
    (triple : ProcessTriple) : Nat :=
  triple.first.massLoss + triple.second.massLoss + triple.third.massLoss

theorem process_triple_loss_covered_by_residual
    (triple : ProcessTriple) :
    triple.totalMassLoss ≤ triple.totalResidual := by
  unfold ProcessTriple.totalMassLoss ProcessTriple.totalResidual
  exact Nat.add_le_add
    (Nat.add_le_add triple.first.lossCovered triple.second.lossCovered)
    triple.third.lossCovered

theorem process_triple_accounting
    (triple : ProcessTriple) :
    triple.third.output.totalMass + triple.totalMassLoss =
      triple.first.input.totalMass := by
  unfold ProcessTriple.totalMassLoss
  rw [← triple.first.balance]
  rw [triple.connectsFirstSecond]
  rw [← triple.second.balance]
  rw [triple.connectsSecondThird]
  rw [← triple.third.balance]
  omega

theorem process_triple_data_processing
    (triple : ProcessTriple) :
    triple.first.input.totalMass ≤
      triple.third.output.totalMass + triple.totalResidual := by
  rw [← process_triple_accounting triple]
  exact Nat.add_le_add_left
    (process_triple_loss_covered_by_residual triple)
    triple.third.output.totalMass

/-! ## Independent product processes -/

def productDistribution
    (left right : FiniteDistribution) : FiniteDistribution :=
  singletonDistribution
    (left.totalMass * right.totalMass)
    (Nat.mul_pos left.positiveTotal right.positiveTotal)

theorem product_distribution_total_mass_exact
    (left right : FiniteDistribution) :
    (productDistribution left right).totalMass =
      left.totalMass * right.totalMass :=
  singleton_distribution_total_mass
    (left.totalMass * right.totalMass)
    (Nat.mul_pos left.positiveTotal right.positiveTotal)

def independentProductProcess
    (left right : FiniteProbabilityProcess) : FiniteProbabilityProcess :=
  let inputMass := left.input.totalMass * right.input.totalMass
  let outputMass := left.output.totalMass * right.output.totalMass
  let houtput : outputMass ≤ inputMass :=
    Nat.mul_le_mul
      (process_output_mass_le_input left)
      (process_output_mass_le_input right)
  { input := productDistribution left.input right.input
    output := productDistribution left.output right.output
    massLoss := inputMass - outputMass
    residual := inputMass - outputMass
    balance := by
      rw [product_distribution_total_mass_exact]
      rw [product_distribution_total_mass_exact]
      exact Nat.add_sub_of_le houtput
    lossCovered := Nat.le_refl (inputMass - outputMass) }

theorem independent_product_process_residual_eq_loss
    (left right : FiniteProbabilityProcess) :
    (independentProductProcess left right).residual =
      (independentProductProcess left right).massLoss := rfl

theorem independent_product_process_input_mass
    (left right : FiniteProbabilityProcess) :
    (independentProductProcess left right).input.totalMass =
      left.input.totalMass * right.input.totalMass := by
  unfold independentProductProcess
  rw [product_distribution_total_mass_exact]

theorem independent_product_process_output_mass
    (left right : FiniteProbabilityProcess) :
    (independentProductProcess left right).output.totalMass =
      left.output.totalMass * right.output.totalMass := by
  unfold independentProductProcess
  rw [product_distribution_total_mass_exact]

end FiniteProbabilityCore
end Gnosis
