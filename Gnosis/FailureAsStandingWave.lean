import Init

/-!
# FailureAsStandingWave — failure-driven theory as eigenmode dynamics

This module formalizes a hypothesis that emerged empirically from the
GKQ rank-K compression work (see `GKQHelixBandwidth.lean` Coda):

> The body of viable theory is a standing wave on claim-space, with
> Dirichlet boundary conditions imposed by falsified claims.

The physics analogy is exact. A standing wave in a bounded medium is
the set of solutions to a wave equation that must be zero at certain
fixed points (nodes). The shape of the wave is determined entirely by
*where it cannot exist*. The viable modes — the discrete set of
frequencies the system actually supports — emerge from the geometry
of the boundary, not from any "positive" specification of what the
wave should look like.

Same structure for a Popperian theory body. A claim space `C` is the
medium. The falsification set `F ⊂ C` is the boundary. A viable theory
is a function `T : C → Plausibility` that vanishes on `F` (you cannot
assign positive plausibility to a falsified claim) and is supported on
`C \ F`. The discrete set of "stable" theories — the ones that survive
all known no-go results — are the eigenmodes of a constraint operator
on this domain.

Two empirical anchors:
1. **gnosis-math is built on failure.** Every load-bearing theorem in
   `GKQHelixBandwidth` is a no-go result. The library teaches what
   doesn't work and why. This is the methodology *as* boundary-
   condition specification.
2. **Rank-K compression converges on negation.** GKQ rank-256 forced
   to discard everything but the most load-bearing dimension of LLM
   semantic space landed on `{not, Not, 合法, 不愿意}` —
   linguistic markers of negation, exclusion, "what is ruled out".
   The most information-dense axis of the model's distribution is
   the *boundary-marking* axis.

These two observations are the same observation, stated twice. The
information-theoretic kernel of a constraint-respecting system is the
specification of its boundaries.

Connection to existing infrastructure: gnosis distributed-inference
already has a `standing-wave-pca` tool that fits PCA modes to a
calibration corpus and ships only the modes that "stand" (survive
across the corpus). The naming wasn't decorative — that work was
finding the eigenmodes of the constraint operator induced by the
calibration prompts. This module names the broader pattern.
-/

namespace Gnosis
namespace FailureAsStandingWave

-- ══════════════════════════════════════════════════════════
-- SECTION 1 — Claim space and falsification boundaries
-- ══════════════════════════════════════════════════════════

/-- A discrete claim index. In a full theory each `Claim` would be a
    proposition; here we work with `Nat`-indexed surrogates so all
    membership questions stay decidable without Mathlib. -/
abbrev Claim := Nat

/-- A falsification boundary: a decidable membership test that says
    whether a given claim has been disproven by a counterexample. -/
structure FalsificationSet where
  isFalsified : Claim → Bool

/-- The viable predicate: a claim is viable iff it has not been
    falsified. By construction, viability is decidable. -/
def isViable (F : FalsificationSet) (c : Claim) : Bool :=
  ! F.isFalsified c

-- ══════════════════════════════════════════════════════════
-- SECTION 2 — Standing-wave modes on claim space
-- ══════════════════════════════════════════════════════════

/-- A standing-wave mode assigns a `Nat` amplitude (plausibility,
    attention weight, whatever) to each claim, subject to a Dirichlet
    boundary condition: amplitude must vanish on every falsified claim.

    Field `vanishesOnFalsified` enforces the BC at the type level.
    Any constructor of `StandingWaveMode F` ships a mathematical
    proof that the mode respects all of `F`'s no-go boundaries. -/
structure StandingWaveMode (F : FalsificationSet) where
  amplitude            : Claim → Nat
  vanishesOnFalsified  : ∀ c, F.isFalsified c = true → amplitude c = 0

/-- The trivial mode: uniformly zero. Always satisfies the BC. -/
def trivialMode (F : FalsificationSet) : StandingWaveMode F where
  amplitude _          := 0
  vanishesOnFalsified  := by intros _ _; rfl

/-- A mode is *supported* at claim `c` iff its amplitude there is
    positive. By the Dirichlet BC, support is necessarily a subset
    of the viable set. -/
def supportedAt (m : StandingWaveMode F) (c : Claim) : Bool :=
  decide (m.amplitude c > 0)

/-- **Theorem (support exclusion).** A standing-wave mode cannot be
    supported on a falsified claim. The negation axis IS the
    boundary; the mode lives in its complement. -/
theorem support_disjoint_from_falsifications
    (F : FalsificationSet) (m : StandingWaveMode F) (c : Claim)
    (hF : F.isFalsified c = true) : supportedAt m c = false := by
  have h0 : m.amplitude c = 0 := m.vanishesOnFalsified c hF
  simp [supportedAt, h0]

-- ══════════════════════════════════════════════════════════
-- SECTION 3 — Worked example: a 4-claim space with two falsifications
-- ══════════════════════════════════════════════════════════

/-- A concrete falsification set: claims 1 and 3 are disproven;
    claims 0 and 2 are viable. Mirrors a tiny theory with two no-go
    boundaries and two viable interior modes. -/
def exampleF : FalsificationSet where
  isFalsified
    | 1 => true
    | 3 => true
    | _ => false

/-- A nontrivial standing-wave mode on `exampleF`: amplitude 5 at
    claim 0, amplitude 7 at claim 2, zero elsewhere. Satisfies BCs
    at claims 1 and 3 (the falsified ones). -/
def exampleMode : StandingWaveMode exampleF where
  amplitude
    | 0 => 5
    | 2 => 7
    | _ => 0
  vanishesOnFalsified := by
    intro c hF
    -- exampleF marks 1 and 3 as falsified; mode is zero on both.
    cases c with
    | zero => simp_all [exampleF]
    | succ n =>
      cases n with
      | zero => rfl
      | succ m =>
        cases m with
        | zero => simp_all [exampleF]
        | succ k =>
          cases k with
          | zero => rfl
          | succ _ => rfl

/-- Witness: the example mode IS supported at claim 0 (its amplitude
    is 5 > 0). A nontrivial standing wave exists. -/
theorem example_mode_supported_at_zero :
    supportedAt exampleMode 0 = true := by decide

/-- Witness: the example mode is NOT supported at claim 1 (falsified
    boundary). The BC holds at the type level. -/
theorem example_mode_unsupported_at_one :
    supportedAt exampleMode 1 = false := by decide

-- ══════════════════════════════════════════════════════════
-- SECTION 4 — Empirical bridge to GKQHelixBandwidth
-- ══════════════════════════════════════════════════════════
-- Recorded link to the rank-K compression empirical finding.

/-- GKQ rank-256 Qwen-0.5B greedy attractor token under the
    "Capital of France" prompt (see `GKQHelixBandwidth.Section 6`).
    Carried here so this module can refer to it without re-stating. -/
def gkqAttractorTokenId : Nat := 537  -- " not"

/-- The empirical claim: rank-K compression of an LLM weight matrix
    converges, under forced compression, onto the linguistic boundary-
    marking tokens. This is the standing-wave fingerprint: the
    most-load-bearing axis of compressed semantic space is the
    falsification axis itself. -/
def gkqCompressionAxis : String := "negation-volition-legality"

/-- **Hypothesis (recorded, not yet formally proved).** When a
    compression scheme is forced past the rank threshold where
    argmax-fidelity breaks, the surviving axis is the one most
    correlated with the system's *constraint* set. For LLMs
    trained on natural language, the constraint set is implicit
    in the negation/legality vocabulary that marks "what is ruled
    out". GKQ's empirical convergence on this axis is the
    compression-side mirror of `gnosis-math`'s methodology-side
    convergence on no-go theorems. -/
def compression_failure_axis_equals_methodology_failure_axis : Bool := true

theorem fixed_point_recorded :
    compression_failure_axis_equals_methodology_failure_axis = true := by
  decide

end FailureAsStandingWave
end Gnosis
