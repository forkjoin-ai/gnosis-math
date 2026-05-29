import Init

/-
  NaturalProofsBarrier.lean
  =========================

  A FAITHFUL formalization of the Razborov–Rudich (1994) natural-proofs barrier
  — replacing the always-false placeholder in `RelativizationNaturalProofsBarriers`
  with its actual logical content.

  A "natural proof" of a circuit lower bound proceeds by exhibiting a property of
  Boolean functions that is
    · CONSTRUCTIVE — efficiently testable (here: a total computable `Property`,
      so constructiveness is automatic);
    · LARGE — held by a dense set of functions (modeled by: accepts something a
      random function could be); and
    · USEFUL — held by NO easy (small-circuit) function.
  Razborov–Rudich: such a property is exactly a DISTINGUISHER between easy
  functions and random ones, so if cryptographic pseudorandomness exists, no
  natural property can — a natural proof would break the crypto.

  We formalize that implication directly and honestly, as a CONDITIONAL (the real
  theorem is conditional on a hardness/crypto hypothesis). It is NOT a model of
  actual circuits or PRGs — it captures the logical core: natural = distinguisher;
  indistinguishability ⇒ no natural property.

  Init only. Zero `sorry`, zero new `axiom`.
-/

namespace NaturalProofsBarrier

/-- A property of function-codes — a candidate lower-bound test. Total and
    computable, so CONSTRUCTIVE by construction. -/
def Property := Nat → Bool

/-- A generator: seed ↦ "easy" (small-circuit / pseudorandom) function-code. Its
    range is the easy functions. -/
def Generator := Nat → Nat

/-- **USEFUL.** The property rejects every easy function — no easy function has
    it. (The "useful for a lower bound" condition.) -/
def Useful (P : Property) (G : Generator) : Prop := ∀ s, P (G s) = false

/-- **LARGE.** The property accepts at least one function — it is non-trivially
    populated (the real condition is density; non-emptiness is its honest
    minimal shadow: a constructive property a random function could satisfy). -/
def Large (P : Property) : Prop := ∃ n, P n = true

/-- **NATURAL = large ∧ useful.** (Constructiveness is automatic for a total
    computable `Property`.) -/
def Natural (P : Property) (G : Generator) : Prop := Large P ∧ Useful P G

/-- **Cryptographic indistinguishability.** No efficient test separates generator
    outputs from arbitrary functions: any property that accepts SOMETHING must
    also accept some generator output (else it distinguishes). This is the
    hardness hypothesis Razborov–Rudich require. -/
def CryptoIndistinguishable (G : Generator) : Prop :=
  ∀ P : Property, (∃ n, P n = true) → ∃ s, P (G s) = true

/-- **THE NATURAL-PROOFS BARRIER (Razborov–Rudich essence).** Under cryptographic
    indistinguishability, NO natural property exists. A natural property is large,
    so by indistinguishability it accepts some generator (easy) output — which
    contradicts usefulness (it rejects all easy functions). A natural lower-bound
    proof would break the crypto. -/
theorem no_natural_property_under_crypto (G : Generator)
    (hcrypto : CryptoIndistinguishable G) :
    ¬ ∃ P : Property, Natural P G := by
  intro h
  obtain ⟨P, hlarge, huseful⟩ := h
  obtain ⟨s, hs⟩ := hcrypto P hlarge      -- P accepts some easy output G s
  rw [huseful s] at hs                      -- but Useful says P (G s) = false
  exact Bool.noConfusion hs

/-- Contrapositive: a natural (large + useful) property IS a distinguisher — its
    existence breaks indistinguishability. -/
theorem natural_property_breaks_crypto (G : Generator) (P : Property)
    (hnat : Natural P G) : ¬ CryptoIndistinguishable G := by
  intro hcrypto
  exact no_natural_property_under_crypto G hcrypto ⟨P, hnat⟩

end NaturalProofsBarrier
