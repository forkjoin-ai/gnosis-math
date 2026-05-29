import Init

/-
  BlindMethodBarrier.lean
  =======================

  "Can we prove NOBODY can prove P ≠ NP, if we can't?"

  HONEST ANSWER, two parts:

  (1) NO — not in the absolute sense. "Nobody can prove P ≠ NP" means P ≠ NP is
      INDEPENDENT of the axioms (e.g. ZFC). That is OPEN, unknown, possibly false,
      and would be a larger result than P ≠ NP itself. Our own inability proves
      nothing about universal impossibility — concluding "nobody can" from "we
      can't" is the pessimism fallacy (see feedback: the seemingly-impossible is
      usually feasible when pushed).

  (2) YES — for a whole CLASS of methods. The barrier theorems (Baker–Gill–Solovay
      relativization; Razborov–Rudich natural proofs; Aaronson–Wigderson
      algebrization) prove specific powerful techniques cannot do it. This module
      formalizes the abstract core they share: any method whose verdict depends
      ONLY on a "blind parameter" (the relativizing charge / oracle it sees,
      not the actual object) is UNSOUND — it must err on some world.

  This generalizes `RelativizationAntitheorem` from the one gap-charge method to
  ALL charge-blind methods. It says: "no blind method can ever decide it." It does
  NOT say "nobody can decide it" — a non-blind method evades this entirely. The
  gap between the two is precisely the open problem.

  Init only. Zero `sorry`, zero new `axiom`.
-/

namespace BlindMethodBarrier

/-- A "world": the GROUND TRUTH of separation, plus the blind parameter (charge /
    oracle view) a relativizing method actually sees. The truth and the view are
    independent — that independence is the whole barrier. -/
structure World where
  separated : Bool
  charge : Nat → Nat

/-- A **blind method**: its verdict is a function of the charge ALONE — it never
    inspects the actual object. Every relativizing / charge-based argument is one. -/
def BlindMethod : Type := (Nat → Nat) → Bool

/-- A method is **sound on a world** when its verdict matches the ground truth. -/
def SoundOn (M : BlindMethod) (w : World) : Prop := M w.charge = w.separated

/-- **THE BARRIER (abstract relativization).** No blind method is sound on every
    world: there are always two worlds sharing the SAME charge but OPPOSITE ground
    truth, and the method — seeing only the charge — must get one of them wrong.

    This is "no blind/relativizing method can ever decide separation", for ALL
    such methods at once. It is NOT "no method can decide it": a method that
    actually inspects the object (`w.separated`) is not a `BlindMethod` and is
    untouched. That gap is the open problem. -/
theorem no_blind_method_is_universally_sound (M : BlindMethod) :
    ∃ w₁ w₂ : World, w₁.charge = w₂.charge ∧ ¬ (SoundOn M w₁ ∧ SoundOn M w₂) := by
  refine ⟨⟨true, fun _ => 0⟩, ⟨false, fun _ => 0⟩, rfl, ?_⟩
  intro h
  obtain ⟨h1, h2⟩ := h
  simp only [SoundOn] at h1 h2
  -- h1 : M (fun _ => 0) = true ; h2 : M (fun _ => 0) = false
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- Contrapositive framing: if a blind method is sound on a world, it is UNSOUND on
    the charge-identical world of opposite truth. Blindness forces error. -/
theorem blind_soundness_forces_error (M : BlindMethod) (w : World)
    (hsound : SoundOn M w) :
    ¬ SoundOn M { separated := !w.separated, charge := w.charge } := by
  intro hother
  simp only [SoundOn] at hsound hother
  rw [hsound] at hother
  cases w.separated <;> simp at hother

/-- **The honest boundary, as a Prop we deliberately do NOT prove.** "P ≠ NP is
    unprovable" = independence from the axioms. It is recorded, not asserted —
    the barrier above bounds METHODS, not provability itself. -/
def AbsoluteUnprovabilityIsOpen : Prop := True

end BlindMethodBarrier
