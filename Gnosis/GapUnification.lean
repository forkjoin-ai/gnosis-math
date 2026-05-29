import Init
import Gnosis.AckermannLightConeBridge
import Gnosis.KnotRopelengthComplexity
import Gnosis.KnotRopelengthSuperpolynomial

/-
  GapUnification.lean
  ===================

  "The rope, the Betti charge, and the light cone are the same true fact:
  exp > poly." — proved.

  Each of the three gap-arguments wears a costume:
    * ROPE / BETTI: the NP knot's ropelength `1 + 2^n` exceeds `n^k`
                    (the essential charge is β₁ = 2^n; the `+1` is β₀, incidental).
    * LIGHT:        a polynomial-reach searcher cannot catch the `2^n` front
                    (`catchable (n^k) (2^n) = false`).
    * CORE:         the bare arithmetic `∀ k, ∃ n, n^k < 2^n`.

  Strip the costumes — the rope's incidental `+1`, the cone's geometry — and the
  identical core remains. THAT is "it strengthens by weakening": the weakest,
  most abstract statement (`Superpoly`) is the strongest, because the single
  lemma implies all three dressed-up forms. We prove the light form is
  EQUIVALENT to the core, and the rope/Betti form FOLLOWS from it.

  HONEST SCOPE (unchanged): unifying the three does not make any of them a
  P ≠ NP proof. They share one true arithmetic core (`exp > poly`) plus a posited
  class↔geometry identification that relativizes (Baker–Gill–Solovay), so cannot
  separate P from NP. This module proves the unification, not the conjecture.

  Init + the bridge + the rope modules. Zero `sorry`, zero new `axiom`.
-/

namespace GapUnification

open AckermannLightConeBridge
open KnotRopelengthComplexity
open KnotRopelengthSuperpolynomial

/-- The common core, stripped of all costume: the exponential outruns every
    fixed polynomial. -/
def Superpoly : Prop := ∀ k, ∃ n, n ^ k < 2 ^ n

/-- The core is true (this is `exp_beats_poly`). -/
theorem core : Superpoly := fun k => exp_beats_poly k

/-! ## The light cone wears the core as a costume (equivalence) -/

/-- A polynomial-reach searcher fails to catch the `2^n` front exactly when the
    exponential outruns the polynomial. -/
theorem catchable_false_iff (B S : Nat) : catchable B S = false ↔ B < S := by
  constructor
  · intro hf
    rcases Nat.lt_or_ge B S with h | h
    · exact h
    · rw [(catchable_iff B S).mpr h] at hf; exact Bool.noConfusion hf
  · intro hlt
    rcases hc : catchable B S with _ | _
    · rfl
    · have hsb : S ≤ B := (catchable_iff B S).mp hc
      exact absurd hsb (by omega)

/-- **LIGHT ⟺ CORE.** The search-vs-verify gap (poly searcher never catches the
    `2^n` front) is logically identical to the bare core `exp > poly`. -/
theorem light_iff_core :
    (∀ k, ∃ n, catchable (n ^ k) (2 ^ n) = false) ↔ Superpoly := by
  constructor
  · intro h k
    obtain ⟨n, hn⟩ := h k
    exact ⟨n, (catchable_false_iff _ _).mp hn⟩
  · intro h k
    obtain ⟨n, hn⟩ := h k
    exact ⟨n, (catchable_false_iff _ _).mpr hn⟩

/-! ## The rope / Betti gap follows from the core -/

/-- **CORE ⟹ ROPE/BETTI.** The exponential core implies the NP knot's ropelength
    `1 + 2^n` exceeds every fixed polynomial (the `+1 = β₀` only helps). -/
theorem rope_from_core (h : Superpoly) : ∀ k, ∃ n, npRopelength n > n ^ k := by
  intro k
  obtain ⟨n, hn⟩ := h k
  refine ⟨n, ?_⟩
  rw [npRopelengthValue]
  omega

/-! ## The unification -/

/-- **Three costumes, one fact.** The rope/Betti gap, the light (search-vs-verify)
    gap, and the bare arithmetic core all hold — as one statement. -/
theorem three_costumes_one_fact :
    Superpoly
    ∧ (∀ k, ∃ n, npRopelength n > n ^ k)
    ∧ (∀ k, ∃ n, catchable (n ^ k) (2 ^ n) = false) :=
  ⟨core, rope_from_core core, light_iff_core.mpr core⟩

/-- **Strengthen by weakening.** The weakest, most abstract form (`Superpoly`,
    stripped of rope and light) implies BOTH dressed-up forms. Generalizing to
    the common core is exactly what makes one lemma do all the work. -/
theorem strengthen_by_weakening (h : Superpoly) :
    (∀ k, ∃ n, npRopelength n > n ^ k)
    ∧ (∀ k, ∃ n, catchable (n ^ k) (2 ^ n) = false) :=
  ⟨rope_from_core h, light_iff_core.mpr h⟩

end GapUnification
