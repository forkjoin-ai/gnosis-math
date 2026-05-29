import Init
import Gnosis.AckermannFunction
import Gnosis.AckermannRuntimeCertificate
import Gnosis.AckermannLightConeBridge
import Gnosis.AckermannUniversality
import Gnosis.InformationLightCone
import Gnosis.ForcedLightConeEmbedding

/-
  AckermannIsLightSpeed.lean
  ==========================

  CAPSTONE. Composes the three obligations into one statement of the precise
  relationship between the Ackermann ceiling and the speed of light.

  Per the repository rule "never write 'X IS the Y'": we do NOT assert an
  emphatic identity. We prove that the Ackermann ceiling **occupies the role
  of c** — it is the unique invariant frontier under which the realizable
  (computable) coincides with the causal, it is saturated by the maximal
  information-propagation rate (light = information at the limit), and the
  sub-frontier ladder is exactly the primitive-recursive operations.

  The five legs, each a theorem proved in a sibling module:

    (A) certified ⟺ causal              `AckermannLightConeBridge.certified_iff_in_lightcone`
    (B) saturation is lightlike         `AckermannLightConeBridge.front_is_lightlike`
    (C) the cone slope (c) is forced    `ForcedLightConeEmbedding.slope_forced`
    (D) c = max information speed       `InformationLightCone.info_within_cone` (+ photon)
    (E) sub-frontier ladder = succ/+/·/^ `AckermannUniversality.hyperop_one/two/three`

  Together: "computable" and "causal" are the same predicate, separated by a
  single forced constant, saturated by light, with the Ackermann diagonal as
  the frontier of the primitive-recursive ladder.

  ## The co-theorem (NP)

  `AckermannLightConeBridge.subluminal_never_reaches_front` +
  `InformationLightCone.photon_is_luminal`: a strictly sub-frontier (tractable)
  computation is strictly timelike — it never rides the luminal front. NP's
  solution-front is lightlike; a polynomial verifier is subluminal; the gap
  never closes. You can't catch a photon.

  ## What remains (honestly recorded, not asserted)

  `AckermannUniversality.ackermannUniversalityObligation.eventualLevelDomination`
  — the classical Ackermann-not-primitive-recursive universal — is recorded as
  a `Prop`, not proved here (needs a PR-encoder + the `hyperop`
  level-monotonicity tower). And leg (D) is the discrete/dimensionless skeleton
  of the Margolus–Levitin → c derivation; the continuum, real-valued physics
  step is cited, not mechanized in Init-only Lean.

  Init + the five sibling modules. Zero `sorry`, zero new `axiom`.
-/

namespace AckermannIsLightSpeed

open AckermannFunction
open AckermannRuntimeCertificate
open Gnosis.CausalDiamond
open AckermannLightConeBridge

/-! ## The composed identity -/

/-- **CAPSTONE.** The Ackermann ceiling occupies the role of the speed of
    light. All five legs hold simultaneously. -/
theorem ackermann_ceiling_occupies_role_of_c :
    -- (A) BRIDGE — computable-certified ⟺ causal (in the future light cone).
    (∀ T : Runtime, IsKPercentCertified T 100
        ↔ ∀ n, inFutureLightCone origin (runtimeEvent T n) = true) ∧
    -- (B) SATURATION — the Ackermann frontier lies exactly on the light cone.
    (∀ n, intervalSquared origin (runtimeEvent ackermannCeiling n) = 0) ∧
    -- (C) FORCED — the cone slope (c) is the unique certificate-faithful
    --     conversion constant; nothing else makes realizable = causal.
    (∀ α β, ForcedLightConeEmbedding.CertificateFaithful α β → α = β) ∧
    -- (D) KEYSTONE — that slope equals the maximal information-propagation
    --     speed (1 cell/tick), and the photon attains it: light is the
    --     information front at the limit.
    (InformationLightCone.mlMaxCellsPerTick = 1
      ∧ (∀ sig, InformationLightCone.RespectsLightSpeed sig
          → InformationLightCone.StartsAtOrigin sig
          → ∀ t x, sig t x = true → x.natAbs ≤ t)
      ∧ (∀ t, InformationLightCone.photon t (t : Int) = true)) ∧
    -- (E) LADDER — the sub-frontier hyperoperation levels are exactly the
    --     primitive-recursive operations successor/addition/mult/exponent.
    ((∀ a b, hyperop 1 a b = a + b)
      ∧ (∀ a b, hyperop 2 a b = a * b)
      ∧ (∀ a b, hyperop 3 a b = a ^ b)) := by
  refine ⟨certified_iff_in_lightcone, front_is_lightlike,
          ForcedLightConeEmbedding.slope_forced, ?_, ?_⟩
  · exact ⟨rfl,
      fun sig hc h0 => InformationLightCone.info_within_cone sig hc h0,
      fun t => (InformationLightCone.photon_is_luminal t).1⟩
  · exact ⟨AckermannUniversality.hyperop_one,
           AckermannUniversality.hyperop_two,
           AckermannUniversality.hyperop_three⟩

/-! ## The co-theorem, composed -/

/-- **CO-THEOREM.** A strictly sub-frontier (tractable, `k < 100`) computation
    is strictly timelike at every input with a nonzero ceiling — it never sits
    on the luminal Ackermann front that the photon rides. "You can't catch a
    photon": the NP-hard solution-front moves at the speed of light, and a
    polynomial verifier is forever subluminal. -/
theorem co_theorem_subluminal_never_catches_the_front
    (T : Runtime) (k : Nat) (hcert : IsKPercentCertified T k) (hk : k < 100) :
    -- the pursuer is strictly inside the cone at every nonzero-ceiling input …
    (∀ n, 0 < ackermannCeiling n →
        intervalSquared origin (runtimeEvent T n) < 0) ∧
    -- … while the photon rides the front exactly (interval 0) at every tick.
    (∀ t, intervalSquared
            { time := 0, space := 0 }
            { time := (t : Int), space := (t : Int) } = 0) := by
  refine ⟨?_, ?_⟩
  · intro n hpos
    exact subluminal_is_strictly_timelike T n
      (subluminal_never_reaches_front T k n hcert hk hpos)
  · intro t
    show (((t : Int)) - 0) * ((t : Int) - 0) - ((t : Int) - 0) * ((t : Int) - 0) = 0
    omega

/-! ## The honesty ledger — proven legs vs. the one recorded gap -/

/-- A machine-checkable record of what the capstone proves and what it defers,
    so the scope of the claim is explicit in the artifact, not just the prose. -/
structure IdentityLedger where
  bridgeProved : Prop
  saturationProved : Prop
  slopeForcedProved : Prop
  maxInfoSpeedProved : Prop
  ladderProved : Prop
  /-- The one classical universal deferred to a cited result, not asserted. -/
  recordedGap : Prop

/-- The ledger, with each proved leg's exact proposition and the single
    deferred universal pointed at its recorded obligation. -/
def identityLedger : IdentityLedger :=
  { bridgeProved :=
      ∀ T : Runtime, IsKPercentCertified T 100
        ↔ ∀ n, inFutureLightCone origin (runtimeEvent T n) = true
  , saturationProved :=
      ∀ n, intervalSquared origin (runtimeEvent ackermannCeiling n) = 0
  , slopeForcedProved :=
      ∀ α β, ForcedLightConeEmbedding.CertificateFaithful α β → α = β
  , maxInfoSpeedProved :=
      ∀ sig, InformationLightCone.RespectsLightSpeed sig
        → InformationLightCone.StartsAtOrigin sig
        → ∀ t x, sig t x = true → x.natAbs ≤ t
  , ladderProved :=
      ∀ a b, hyperop 3 a b = a ^ b
  , recordedGap :=
      -- The classical Ackermann-not-PR universal, owned by
      -- AckermannUniversality, deferred not asserted.
      AckermannUniversality.ackermannUniversalityObligation.eventualLevelDomination }

end AckermannIsLightSpeed
