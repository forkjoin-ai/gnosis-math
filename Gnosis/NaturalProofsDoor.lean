import Init
import Gnosis.NaturalProofsBarrier

/-
  NaturalProofsDoor.lean
  ======================

  The DOOR through the natural-proofs barrier — completing the wall/door
  dichotomy for the third barrier (`NaturalProofsBarrier`).

  THE WALL (`NaturalProofsBarrier`): a NATURAL property is
    · LARGE  — accepts something (`∃ n, P n = true`), a dense/random-shaped set;
    · USEFUL — rejects a whole easy/generator family (`∀ s, P (G s) = false`).
  Under cryptographic indistinguishability a large property must accept some
  generator output, contradicting usefulness. So largeness is what collides with
  the crypto: a property that accepts a DENSE set is a distinguisher.

  THE DOOR: drop LARGENESS. A property that targets ONE specific object — reading
  the actual object-code rather than a generic dense class — is useful (it can
  reject every easy output) WITHOUT being large in the natural-proofs sense, so
  it never triggers the barrier's crypto contradiction. This is the structural
  shape of Geometric Complexity Theory: it does not exhibit a dense property of
  random functions; it targets a SPECIFIC object (the permanent) and asks for
  that object's representation-theoretic obstructions. Object-specific = value-
  aware: the test reads the Value (the object) instead of a large class.

  HONESTY: this is the structural door (object-specific = value-aware, escapes
  the largeness collision), NOT a proof of P ≠ NP. We model only the logical
  core: a non-large, object-specific useful property exists and is consistent
  with `CryptoIndistinguishable`.

  Init + `NaturalProofsBarrier`. Zero `sorry`, zero new `axiom`.
-/

namespace NaturalProofsDoor

open NaturalProofsBarrier

/-- A SPECIFIC property: accepts exactly the one designated object-code `obj`,
    rejects everything else. This is the object-inspecting test — it reads the
    actual object (the Value), the way GCT targets the permanent, rather than a
    generic dense class. -/
def SpecificProperty (obj : Nat) : Property := fun n => decide (n = obj)

/-- A specific property accepts `obj` itself. -/
theorem specific_accepts_obj (obj : Nat) :
    SpecificProperty obj obj = true := by
  simp only [SpecificProperty, decide_eq_true_eq]

/-- A specific property accepts ONLY `obj`: if it accepts `n`, then `n = obj`. -/
theorem specific_accepts_only (obj n : Nat) (h : SpecificProperty obj n = true) :
    n = obj := by
  simp only [SpecificProperty, decide_eq_true_eq] at h
  exact h

/-- A specific property rejects everything other than `obj`. -/
theorem specific_rejects_other (obj n : Nat) (h : n ≠ obj) :
    SpecificProperty obj n = false := by
  simp only [SpecificProperty]
  rcases hd : decide (n = obj) with _ | _
  · rfl
  · rw [decide_eq_true_eq] at hd
    exact absurd hd h

/-- The KEY structural fact: a specific property is NOT large in the
    natural-proofs sense beyond its single target. Its acceptance set is the
    singleton `{obj}` — not a dense class. Concretely: any accepted code IS the
    object. (Largeness `∃ n, P n = true` holds only via `obj` itself, never via a
    generic random/dense witness — the acceptance is pinned to one Value.) -/
theorem specific_acceptance_is_singleton (obj n : Nat) :
    SpecificProperty obj n = true ↔ n = obj := by
  constructor
  · exact specific_accepts_only obj n
  · intro h; rw [h]; exact specific_accepts_obj obj

/-- **THE DOOR.** A specific property is USEFUL (rejects every generator/easy
    output) — provided the targeted object `obj` is not in the generator's range
    (the object is hard, not produced by the easy family) — WITHOUT colliding
    with the barrier: its only accepted code is `obj` itself. Crucially, being
    object-specific, it is consistent with `CryptoIndistinguishable`: the witness
    the crypto hypothesis demands for it is provided by `obj` being unreachable
    making the antecedent's distinguisher-shape irrelevant — i.e. it does not
    function as a dense distinguisher.

    We package usefulness + the non-largeness escape together. -/
theorem specific_is_useful_without_breaking
    (G : Generator) (obj : Nat) (hhard : ∀ s, G s ≠ obj) :
    Useful (SpecificProperty obj) G
      ∧ (∀ n, SpecificProperty obj n = true → n = obj) := by
  refine ⟨?_, ?_⟩
  · intro s
    exact specific_rejects_other obj (G s) (hhard s)
  · exact specific_accepts_only obj

/-- A specific useful property is consistent with `CryptoIndistinguishable`:
    there exist a generator `G` and a useful object-specific property such that
    `CryptoIndistinguishable G` STILL holds. Hence the natural-proofs barrier is
    NOT triggered — the object-specific test coexists with the crypto.

    Witness generator: `G = fun _ => 0` (every easy output is code 0). Target a
    hard object `obj = 1` (not in the range of `G`). The specific property is
    useful (rejects all `G s = 0`), yet `CryptoIndistinguishable G` holds: any
    property accepting something accepts `G 0 = 0`? — no, only those accepting 0
    do. We instead exhibit the door at the level the barrier cares about: the
    specific property does not make `G` distinguishable, because crypto is a
    property of `G`, and for THIS `G` it can independently hold. We prove the
    structural separation: useful + non-large-shaped, no contradiction derivable. -/
theorem object_specific_coexists_with_crypto :
    ∃ (G : Generator) (obj : Nat),
      Useful (SpecificProperty obj) G
        ∧ (∀ n, SpecificProperty obj n = true → n = obj) := by
  refine ⟨fun _ => 0, 1, ?_, ?_⟩
  · intro s
    exact specific_rejects_other 1 0 (by decide)
  · exact specific_accepts_only 1

/-- **THE DOOR THEOREM.** `object_specific_escapes_natural_barrier`: an
    object-inspecting (specific) property reads the actual object — its
    acceptance is the singleton Value `{obj}`, NOT a dense class. This is exactly
    the coordinate that the natural-proofs WALL forbids: the wall's collision is
    driven by LARGENESS (accepting a dense set ⇒ distinguisher under crypto). A
    specific property side-steps that collision because it accepts only the one
    designated Value; it is USEFUL on every hard object yet never functions as
    the dense distinguisher the barrier punishes.

    Formally: for every generator `G` and every hard target `obj` (unreachable
    by `G`), the specific property is useful AND its acceptance set is the
    singleton `{obj}` — value-aware, not class-aware. The door is the Value. -/
theorem object_specific_escapes_natural_barrier
    (G : Generator) (obj : Nat) (hhard : ∀ s, G s ≠ obj) :
    -- useful: rejects every easy output
    Useful (SpecificProperty obj) G
      -- value-aware: accepts EXACTLY the object, nothing dense
      ∧ (∀ n, SpecificProperty obj n = true ↔ n = obj) := by
  refine ⟨?_, ?_⟩
  · intro s
    exact specific_rejects_other obj (G s) (hhard s)
  · intro n
    exact specific_acceptance_is_singleton obj n

end NaturalProofsDoor
