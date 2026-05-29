import Init
import Gnosis.AckermannRuntimeCertificate
import Gnosis.AckermannLightConeBridge

/-
  ForcedLightConeEmbedding.lean
  =============================

  Obligation 1 of the "Ackermann ceiling occupies the role of c" program
  (see `AckermannLightConeBridge`, `AckermannIsLightSpeed`).

  ## The gap this closes

  `AckermannLightConeBridge` *chose* the coordinate map
  `runtimeEvent T n := { time := A(n), space := T(n) }`. A skeptic objects:
  the correspondence "certified ⟺ causal" holds only because of that
  hand-picked embedding; rescale space and time differently and it breaks,
  so nothing singles out the Ackermann ceiling as `c`.

  This module answers the objection. Consider the most general LINEAR
  rescaling of the embedding: temporal coordinate `α · ceiling`, spatial
  coordinate `β · steps`, for positive conversion constants `α, β`. Under
  this rescaling, cone membership reads `β · s ≤ α · c`. We prove:

      if  (β · s ≤ α · c  ⟺  s ≤ c)  for ALL step/ceiling values s, c,
      then  α = β.

  i.e. the ONLY rescaling under which causal-membership coincides with the
  100%-certificate is the one with equal scales — slope 1. The conversion
  constant is FORCED, not chosen. That is exactly what it means for the
  speed of light to be a *constant*: the cone slope is the unique value
  making "realizable" coincide with "causal." `c` is pinned by the FULL
  correspondence, both directions at once — the saturating runtime must be
  lightlike / in-cone (`s = c`, forcing `β ≤ α`) AND any over-ceiling runtime
  must be spacelike / out-of-cone (`s = c+1`, forcing `α ≤ β`). Either demand
  alone fixes only one inequality; together they fix the slope.

  Init + the certificate + the bridge. Zero `sorry`, zero new `axiom`.
-/

namespace ForcedLightConeEmbedding

open AckermannRuntimeCertificate
open Gnosis.CausalDiamond
open AckermannLightConeBridge

/-! ## The forcing lemma (pure arithmetic) -/

/-- A pair of positive conversion constants `(α, β)` is **certificate-faithful**
    when the rescaled cone predicate `β·s ≤ α·c` agrees with the bare
    certificate `s ≤ c` at every step count `s` and ceiling value `c`. -/
def CertificateFaithful (α β : Nat) : Prop :=
  ∀ s c, (β * s ≤ α * c ↔ s ≤ c)

/-- **OBLIGATION 1 (the slope is forced).** Any certificate-faithful rescaling
    has equal scales: `α = β`. The cone slope — the speed of light — is the
    unique conversion constant under which realizability coincides with
    causality. -/
theorem slope_forced (α β : Nat) (h : CertificateFaithful α β) : α = β := by
  -- (1) β ≥ 1, from the failing instance s = 1, c = 0.
  have hβ1 : 1 ≤ β := by
    have hf : ¬ (β * 1 ≤ α * 0) := mt (h 1 0).mp (by decide)
    omega
  -- (2) β ≤ α, from the holding instance s = 1, c = 1.
  have hβα : β ≤ α := by
    have := (h 1 1).mpr (Nat.le_refl 1)
    omega
  -- (3) α ≤ β, from the failing instance s = β+1, c = β.
  have hαβ : α ≤ β := by
    have hfail : ¬ (β * (β + 1) ≤ α * β) := mt (h (β + 1) β).mp (by omega)
    rcases Nat.lt_or_ge α (β + 1) with h' | h'
    · omega
    · exfalso
      have step : (β + 1) * β ≤ α * β := Nat.mul_le_mul h' (Nat.le_refl β)
      have hcon : β * (β + 1) ≤ α * β := by rw [Nat.mul_comm β (β + 1)]; exact step
      exact hfail hcon
  exact Nat.le_antisymm hαβ hβα

/-! ## The canonical scale is faithful — and unique

  The bridge's chosen embedding is the normalized representative `α = β = 1`:
  it is certificate-faithful, and by `slope_forced` it is (up to the common
  scale) the only faithful one. -/

/-- The canonical scale `α = β = 1` is certificate-faithful: this is the
    bridge's embedding, where cone membership is literally `s ≤ c`. -/
theorem canonical_scale_faithful : CertificateFaithful 1 1 := by
  intro s c
  constructor
  · intro h; omega
  · intro h; omega

/-- Any common scale `α = β = k` is faithful for `k ≥ 1` — the trivial gauge
    freedom (choice of units). Faithfulness fixes the slope (`α = β`); it does
    not fix the unit, exactly as `c = 1` is a choice of natural units. -/
theorem common_scale_faithful (k : Nat) (hk : 1 ≤ k) : CertificateFaithful k k := by
  intro s c
  constructor
  · intro h
    -- k*s ≤ k*c with k ≥ 1 ⇒ s ≤ c
    exact Nat.le_of_mul_le_mul_left h hk
  · intro h
    exact Nat.mul_le_mul_left k h

/-- **The uniqueness statement.** Every certificate-faithful rescaling is a
    pure-gauge multiple of the canonical bridge embedding: its two scales are
    equal. There is no faithful embedding with a slope other than the
    Ackermann-ceiling slope. The speed of light is forced. -/
theorem embedding_unique_up_to_gauge (α β : Nat)
    (h : CertificateFaithful α β) : α = β :=
  slope_forced α β h

/-- Tie-back to the bridge: under the canonical (forced) scale `α = β = 1`, a
    runtime stays in the future light cone at every input exactly when it is
    `IsKPercentCertified _ 100`. The faithful scale is canonical, and by
    `slope_forced` it is the unique slope. -/
theorem forced_scale_recovers_bridge (T : Runtime) :
    CertificateFaithful 1 1 ∧
    (IsKPercentCertified T 100
      ↔ ∀ n, inFutureLightCone origin (runtimeEvent T n) = true) :=
  ⟨canonical_scale_faithful, certified_iff_in_lightcone T⟩

end ForcedLightConeEmbedding
