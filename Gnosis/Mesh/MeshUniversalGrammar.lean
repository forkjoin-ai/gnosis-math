import Init
import Gnosis.ArrowBuleDeficit

namespace Gnosis
namespace MeshUniversalGrammar

open ArrowBuleDeficit

inductive LingState
  | fluidArticulation    -- Fluent structural innovation
  | phoneticFriction     -- Dialect drift / isolation
  | fossilizedGrammar    -- Stable stationary distribution

inductive VocalForce
  | topologicalVacuum    -- Pure structural flow
  | articulationFriction -- Physical vocal tract constraints
  | pauliExclusion       -- Grammatical attractor / universal trap

def reduceLingState (s : LingState) : VocalForce :=
  match s with
  | LingState.fluidArticulation => VocalForce.topologicalVacuum
  | LingState.phoneticFriction => VocalForce.articulationFriction
  | LingState.fossilizedGrammar => VocalForce.pauliExclusion

theorem attractor_is_exclusion : reduceLingState LingState.fossilizedGrammar = VocalForce.pauliExclusion := rfl

structure GrammarKernel where
  isolationDrift : Nat
  biologicalConstraint : Nat
  validLang : isolationDrift + biologicalConstraint > 0

def isGrammarFossilized (k : GrammarKernel) : Prop :=
  k.biologicalConstraint > k.isolationDrift

def applyLanguageContact (k : GrammarKernel) (alpha : Nat) : GrammarKernel :=
  { isolationDrift := k.isolationDrift + alpha
    biologicalConstraint := k.biologicalConstraint
    validLang := by
      have h : 0 < k.isolationDrift + k.biologicalConstraint := k.validLang
      have h' : 0 < (k.isolationDrift + k.biologicalConstraint) + alpha :=
        Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h' }

theorem contact_breaks_fossilization (k : GrammarKernel) :
    ∃ (alpha : Nat), ¬ isGrammarFossilized (applyLanguageContact k alpha) := by
  refine ⟨k.biologicalConstraint, ?_⟩
  simp [isGrammarFossilized, applyLanguageContact]

end MeshUniversalGrammar
end Gnosis
