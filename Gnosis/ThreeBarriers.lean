import Init
import Gnosis.BlindMethodBarrier
import Gnosis.NaturalProofsBarrier
import Gnosis.AlgebrizationBarrier

/-
  ThreeBarriers.lean
  ==================

  The three classical barriers to P vs NP, now each FAITHFULLY formalized, bundled
  into one statement — the honest foundation under `PvsNPFrontier`'s wall W4.

    (1) RELATIVIZATION  — Baker–Gill–Solovay 1975 — `BlindMethodBarrier`:
        a method seeing only the oracle/charge must err.
    (2) NATURAL PROOFS  — Razborov–Rudich 1994 — `NaturalProofsBarrier`:
        under cryptographic indistinguishability, no natural (large+useful)
        property exists — it would be a distinguisher.
    (3) ALGEBRIZATION   — Aaronson–Wigderson 2008 — `AlgebrizationBarrier`:
        even seeing the oracle AND its low-degree extension, a method must err.

  THE COMMON ESSENCE. All three are one shape: a proof/method that is BLIND to the
  actual object — that factors through a generic view (an oracle, an oracle plus
  its extension, or a large constructive property) — cannot decide P vs NP. The
  more the method is allowed to see generically (oracle → +extension), the more
  techniques are barred; the natural-proofs wall bars the genericity of the test
  itself. Their SHARED escape is identical: inspect the object's own specific
  structure (its symmetry, circuits, proofs). That escape is exactly the door of
  `PvsNPFrontier.nonblind_method_can_be_sound`.

  Init + the three barrier modules. Zero `sorry`, zero new `axiom`.
-/

namespace ThreeBarriers

/-- **THE THREE WALLS — each faithfully proved, bundled.** Relativization and
    algebrization are unconditional (any view-blind method errs); natural proofs
    is conditional on a hardness hypothesis (`CryptoIndistinguishable`), as the
    real theorem is. Together they bound every known generic route to P vs NP. -/
theorem three_walls
    (G : NaturalProofsBarrier.Generator)
    (hcrypto : NaturalProofsBarrier.CryptoIndistinguishable G) :
    -- (1) RELATIVIZATION: no oracle-blind method is universally sound
    (∀ M : BlindMethodBarrier.BlindMethod,
        ∃ w₁ w₂ : BlindMethodBarrier.World,
          w₁.charge = w₂.charge
            ∧ ¬ (BlindMethodBarrier.SoundOn M w₁ ∧ BlindMethodBarrier.SoundOn M w₂))
    -- (2) NATURAL PROOFS: under crypto, no natural property exists
    ∧ (¬ ∃ P : NaturalProofsBarrier.Property, NaturalProofsBarrier.Natural P G)
    -- (3) ALGEBRIZATION: no (oracle+extension)-blind method is universally sound
    ∧ (∀ M : AlgebrizationBarrier.AlgMethod,
        ∃ w₁ w₂ : AlgebrizationBarrier.World,
          w₁.view = w₂.view
            ∧ ¬ (AlgebrizationBarrier.SoundOn M w₁ ∧ AlgebrizationBarrier.SoundOn M w₂)) :=
  ⟨BlindMethodBarrier.no_blind_method_is_universally_sound,
   NaturalProofsBarrier.no_natural_property_under_crypto G hcrypto,
   AlgebrizationBarrier.no_alg_method_is_universally_sound⟩

end ThreeBarriers
