import Init
import Gnosis.BlindMethodBarrier
import Gnosis.AlgebrizationBarrier

/-
  BarrierUnification.lean
  =======================

  The mirror of `GapUnification`. There, the three P≠NP "gaps" (rope, Betti,
  light) collapsed to one fact: `exp > poly`. Here, the barriers collapse to one
  fact too: VIEW-BLINDNESS.

  Every barrier — relativization (sees only the oracle), algebrization (sees the
  oracle and its low-degree extension) — is the same single lemma once you supply
  the view: a method reading only a view `v` cannot match two opposite truths
  that share that view. We prove the abstract core and exhibit both barriers as
  instances. (Natural proofs is the dual: a blind TEST rather than a blind method
  — `NaturalProofsBarrier`.)

  Two unifications now stand back to back:
    gaps are one fact   — `exp > poly`        (`GapUnification`)
    barriers are one fact — view-blindness    (this module)
  The door between them — inspecting the object — is the only thing neither side
  touches.

  Init + two barrier modules. Zero `sorry`, zero new `axiom`.
-/

namespace BarrierUnification

/-- **THE COMMON CORE OF EVERY BARRIER — view-blindness.** A method whose verdict
    is a function of a view `v : V` alone cannot equal two opposite truths at the
    same view. Trivial in isolation — yet it is the entire content of
    relativization and algebrization once the view is supplied. -/
theorem view_blind_must_err {V : Type} (M : V → Bool) (v : V) {t₁ t₂ : Bool}
    (hdiff : t₁ ≠ t₂) : ¬ (M v = t₁ ∧ M v = t₂) := by
  intro h
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2
  exact hdiff h2

/-- **Relativization is view-blindness** with the view = the oracle/charge.
    Derived from the core; the witness worlds share a charge, differ in truth. -/
theorem relativization_from_core (M : BlindMethodBarrier.BlindMethod) :
    ∃ w₁ w₂ : BlindMethodBarrier.World,
      w₁.charge = w₂.charge
        ∧ ¬ (BlindMethodBarrier.SoundOn M w₁ ∧ BlindMethodBarrier.SoundOn M w₂) := by
  refine ⟨⟨true, fun _ => 0⟩, ⟨false, fun _ => 0⟩, rfl, ?_⟩
  simp only [BlindMethodBarrier.SoundOn]
  exact view_blind_must_err M (fun _ => 0) (by decide)

/-- **Algebrization is view-blindness** with the view = oracle + low-degree
    extension. The richer view is still just a view — the same core applies. -/
theorem algebrization_from_core (M : AlgebrizationBarrier.AlgMethod) :
    ∃ w₁ w₂ : AlgebrizationBarrier.World,
      w₁.view = w₂.view
        ∧ ¬ (AlgebrizationBarrier.SoundOn M w₁ ∧ AlgebrizationBarrier.SoundOn M w₂) := by
  refine ⟨⟨true, ⟨fun _ => 0, fun _ => 0⟩⟩,
          ⟨false, ⟨fun _ => 0, fun _ => 0⟩⟩, rfl, ?_⟩
  simp only [AlgebrizationBarrier.SoundOn]
  exact view_blind_must_err M ⟨fun _ => 0, fun _ => 0⟩ (by decide)

/-- **The barriers are one fact.** Relativization and algebrization both hold, and
    both are the single core `view_blind_must_err` with different views — exactly
    as rope/Betti/light are the single fact `exp > poly`. The walls, like the
    gaps, unify; the door (object-inspection) is what no wall reaches. -/
theorem barriers_are_one_fact :
    (∀ M : BlindMethodBarrier.BlindMethod,
        ∃ w₁ w₂ : BlindMethodBarrier.World,
          w₁.charge = w₂.charge
            ∧ ¬ (BlindMethodBarrier.SoundOn M w₁ ∧ BlindMethodBarrier.SoundOn M w₂))
    ∧ (∀ M : AlgebrizationBarrier.AlgMethod,
        ∃ w₁ w₂ : AlgebrizationBarrier.World,
          w₁.view = w₂.view
            ∧ ¬ (AlgebrizationBarrier.SoundOn M w₁ ∧ AlgebrizationBarrier.SoundOn M w₂)) :=
  ⟨relativization_from_core, algebrization_from_core⟩

end BarrierUnification
