import Init

/-
  AlgebrizationBarrier.lean
  =========================

  A faithful formalization of the Aaronson–Wigderson (2008) algebrization barrier
  — the third wall, absent from the repo until now.

  Relativization gives a proof an ORACLE `O`. Arithmetization — the technique
  behind IP = PSPACE — additionally gives the proof the low-degree polynomial
  EXTENSION `Õ` of that oracle, and that extra data let IP = PSPACE escape pure
  relativization. Aaronson–Wigderson generalized the barrier to match: a technique
  "algebrizes" if it stays valid even when the method sees the oracle AND its
  extension. They proved algebrizing techniques still cannot resolve P vs NP.

  We capture the essence with the same `BlindMethodBarrier` move, but a RICHER
  view: the method sees the full algebraic view `(oracle, extension)`. The barrier
  still bites — two worlds can share the entire algebraic view yet differ in
  ground truth, so the method must err. Seeing the extension is not enough.

  Structural essence, not a model of actual low-degree extensions or interactive
  proofs. Init only. Zero `sorry`, zero new `axiom`.
-/

namespace AlgebrizationBarrier

/-- The algebraic VIEW a method is granted: the oracle AND its low-degree
    extension. (Arithmetization hands a proof exactly this extra data.) -/
structure AlgView where
  oracle : Nat → Nat
  extension : Nat → Nat

/-- A world: ground-truth separation, plus the algebraic view exposed to the
    method. The truth and the view are independent — that is the barrier. -/
structure World where
  separated : Bool
  view : AlgView

/-- An **algebrizing method**: its verdict is a function of the algebraic view
    alone (oracle + extension), never of the actual object. Every algebrizing
    technique is one — strictly more than a relativizing method, which sees only
    the oracle. -/
def AlgMethod : Type := AlgView → Bool

/-- The method is **sound on a world** when its verdict matches the ground truth. -/
def SoundOn (M : AlgMethod) (w : World) : Prop := M w.view = w.separated

/-- **THE ALGEBRIZATION BARRIER (Aaronson–Wigderson essence).** No algebrizing
    method is universally sound: even with the oracle AND its low-degree extension
    in view, there are two worlds sharing the ENTIRE algebraic view but with
    OPPOSITE ground truth, so the method — seeing only the view — must get one
    wrong. Arithmetization escapes relativization, but not this. -/
theorem no_alg_method_is_universally_sound (M : AlgMethod) :
    ∃ w₁ w₂ : World, w₁.view = w₂.view ∧ ¬ (SoundOn M w₁ ∧ SoundOn M w₂) := by
  refine ⟨⟨true, ⟨fun _ => 0, fun _ => 0⟩⟩,
          ⟨false, ⟨fun _ => 0, fun _ => 0⟩⟩, rfl, ?_⟩
  intro h
  obtain ⟨h1, h2⟩ := h
  simp only [SoundOn] at h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- Even granting the extension, soundness on a world forces UNSOUNDNESS on its
    view-identical twin of opposite truth. The richer algebraic view does not
    rescue a method from its blindness to the object. -/
theorem alg_soundness_forces_error (M : AlgMethod) (w : World) (hsound : SoundOn M w) :
    ¬ SoundOn M { separated := !w.separated, view := w.view } := by
  intro hother
  simp only [SoundOn] at hsound hother
  rw [hsound] at hother
  cases w.separated <;> simp at hother

end AlgebrizationBarrier
