import Init
import Gnosis.BlindMethodBarrier
import Gnosis.AlgebrizationBarrier

/-
  ValueIsTheDoor.lean
  ===================

  The QKV insight as one theorem: across every method-family, a SINGLE coordinate
  — the Value (the object) — separates wall from door.

    · Value SEVERED (method reads only the view/key) ⇒ it MUST err — a wall.
    · Value KEPT (method may read the object) ⇒ it CAN be sound — a door.

  We pair each barrier with its door, for both method-families (relativization's
  charge-view and algebrization's oracle+extension view). The walls are the
  existing barrier theorems; the doors are the value-keeping witnesses. Their
  conjunction is the precise formal content of "the value is the door": the
  obstruction is never soundness, only value-severance — and the value path is
  exactly what attention supplies (`AttentionShape`).

  (Natural proofs is the dual — a blind TEST, not a blind method — and its door
  is the same: a test that reads the object's structure. Kept in prose here so
  this module stays method-based and clean.)

  Init + two barrier modules. Zero `sorry`, zero new `axiom`.
-/

namespace ValueIsTheDoor

/-- Relativization's DOOR: a method that keeps the value (reads `w.separated`) is
    sound on every world. The charge-blind wall (`BlindMethodBarrier`) is crossed
    the moment the value path is restored. -/
theorem relativization_door :
    ∃ M : BlindMethodBarrier.World → Bool, ∀ w : BlindMethodBarrier.World, M w = w.separated :=
  ⟨fun w => w.separated, fun _ => rfl⟩

/-- Algebrization's DOOR: even where oracle + extension did not suffice, keeping
    the value is sound on every world. -/
theorem algebrization_door :
    ∃ M : AlgebrizationBarrier.World → Bool, ∀ w : AlgebrizationBarrier.World, M w = w.separated :=
  ⟨fun w => w.separated, fun _ => rfl⟩

/-- **THE VALUE IS THE DOOR.** For both method-families: the value-severed method
    MUST err (the wall), and a value-keeping method CAN be sound (the door). One
    coordinate — the Value/object — is the universal hinge between barred and
    open. Soundness was never the obstruction; value-severance was. -/
theorem value_is_the_door :
    -- WALL (value severed): relativization
    (∀ M : BlindMethodBarrier.BlindMethod,
        ∃ w₁ w₂ : BlindMethodBarrier.World,
          w₁.charge = w₂.charge
            ∧ ¬ (BlindMethodBarrier.SoundOn M w₁ ∧ BlindMethodBarrier.SoundOn M w₂))
    -- WALL (value severed): algebrization
    ∧ (∀ M : AlgebrizationBarrier.AlgMethod,
        ∃ w₁ w₂ : AlgebrizationBarrier.World,
          w₁.view = w₂.view
            ∧ ¬ (AlgebrizationBarrier.SoundOn M w₁ ∧ AlgebrizationBarrier.SoundOn M w₂))
    -- DOOR (value kept): relativization
    ∧ (∃ M : BlindMethodBarrier.World → Bool,
          ∀ w : BlindMethodBarrier.World, M w = w.separated)
    -- DOOR (value kept): algebrization
    ∧ (∃ M : AlgebrizationBarrier.World → Bool,
          ∀ w : AlgebrizationBarrier.World, M w = w.separated) :=
  ⟨BlindMethodBarrier.no_blind_method_is_universally_sound,
   AlgebrizationBarrier.no_alg_method_is_universally_sound,
   relativization_door,
   algebrization_door⟩

end ValueIsTheDoor
