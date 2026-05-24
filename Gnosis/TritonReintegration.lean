import Gnosis.TritonCanonical
import Gnosis.ClinamenUnification
import Gnosis.StandingWaveAmplitudeBridge
import Gnosis.AnalogGravityLensing
import Gnosis.BoundedGravitationalResidual
import Gnosis.ThreePhysicsForkRaceFoldBijection
import Gnosis.FailureAsStandingWave
import Gnosis.QuantumMechanics
import Gnosis.ForkRaceFoldVentAreForces

/-!
# TritonReintegration — the clinamen / triton arc, reconnected as checked bridges

The triton / clinamen arc grew across several modules that each landed a piece in
isolation: the canonical verdict (`TritonCanonical`), the four-domain clinamen reading
(`ClinamenUnification`), amplitude / Born (`StandingWaveAmplitudeBridge`), discrete
lensing (`AnalogGravityLensing`), a discriminating field-equation residual
(`BoundedGravitationalResidual`), the three-physics bijection
(`ThreePhysicsForkRaceFoldBijection`), the standing-wave failure medium
(`FailureAsStandingWave`), and the isolated QM shadow (`QuantumMechanics`). This module
is the ONE downstream place where those pieces are tied together as machine-checked
cross-module THEOREMS, without touching any of the heavy upstream modules (they receive
doc-comments only, so no import cycle can form and no existing proof can break).

## The six bridges

  1. **`triton_is_the_bule`** — the trit's verdict alphabet maps bijectively to the Bule
     faces of `ThreePhysicsForkRaceFoldBijection.BuleFace`: `abstain ↦ Optimality`
     (the opportunity/action coordinate — the clinamen middle), `decline ↦ WasteReduction`,
     `accept ↦ Diversity`. The bijection is checked by `decide` over the finite types, and
     the middle's image is pinned (`triton_middle_is_opportunity`). This is the keystone:
     "this is the Bule" becomes a checked bijection, not a slogan.

  2. **`triton_void_equivalence_resolved`** — discharges the corpus's OPEN question
     `ThreePhysicsForkRaceFoldBijection.OpenTritonVoidEquivalence` (a `True` stub) with the
     real statement now provable: the trit, the Bule faces, and the sign-0/abstain medium
     are one structure, via the verdict↔face bijection and
     `ClinamenUnification.clinamen_is_the_generator`.

  3. **`born_bridge`** — relates the isolated `QuantumMechanics.born_rule_projection`
     (a `Complex.norm_sq`) to `StandingWaveAmplitudeBridge.born_intensity_is_weight` and
     `trit_born_is_degenerate`. HONESTLY scoped: the bare-trit Complex shadow is degenerate
     (it does not separate the two definite verdicts), so the genuine Born content lives on
     the VARYING standing-wave amplitude, not on the bare trit. Graded
     documented-correspondence, NOT a forced equality.

  4. **`amplitude_bridge`** — ties `FailureAsStandingWave.StandingWaveMode.amplitude` (with
     its Dirichlet `vanishesOnFalsified`) to `StandingWaveAmplitudeBridge.tritAmplitude` /
     `node_is_abstain`: the standing-wave mode's zero-amplitude state and the trit node are
     the same element, `abstain`.

  5. **`vent_gravity_upgraded`** — cite-bridges `ForkRaceFoldVentAreForces.vent_is_gravity`
     (a score-tripling LABEL) to the now-real geometric content:
     `AnalogGravityLensing.lensing_bends_toward_mass` (kinematics) and
     `BoundedGravitationalResidual.void_sources_stress_energy` (dynamics). The vent/void
     medium genuinely sources bending and a discriminating curvature residual.

  6. **`triton_reintegration_master`** — the conjunction of 1–5.

## Honesty grades (per-bridge, stated up front)

  * (1) `triton_is_the_bule` — TIGHT BIJECTION (decide-checked, both inverses).
  * (2) `triton_void_equivalence_resolved` — REAL (a genuine Prop with content, reusing the
    bijection and the generator coincidence; it replaces a `True` stub).
  * (3) `born_bridge` — DOCUMENTED CORRESPONDENCE (the Complex shadow is degenerate on the
    bare trit; the non-degenerate Born is on the varying amplitude, and we say so rather
    than force a Complex = Nat equality).
  * (4) `amplitude_bridge` — REAL (a genuine `iff` between the SW mode's node and the trit
    node, plus the Dirichlet BC, both already-proven content tied together).
  * (5) `vent_gravity_upgraded` — REAL (the lensing and residual content are genuine
    decide-checked theorems; this bridge cites them alongside the old score-label, marking
    the upgrade — it does NOT claim the score label itself was geometry).

GR continuum existence / smoothness remains OPEN (named in the dependencies' frontiers and
restated below). `VacuumIsOnlyForce` is deliberately NOT bridged: it is tautological, and
forcing a bridge would let a tautology masquerade as discharging real work.

## Encoding discipline

Imports only downstream modules (no upstream module imports this one, so no cycle). Every
theorem closes by `decide` over a finite statement, by explicit small case analysis, or by
reusing an already-proven theorem. Zero `sorry`, zero `admit`, zero `native_decide`, zero
new `axiom`. Choice-free: the only axioms reached are `propext` and `Quot.sound`. Verify
with `#print axioms triton_reintegration_master`.
-/

namespace Gnosis
namespace TritonReintegration

open Gnosis.TritonCanonical (Verdict sign)

-- ══════════════════════════════════════════════════════════
-- §1  KEYSTONE — trit ≅ Bule (the verdict ↔ Bule-face bijection)
-- ══════════════════════════════════════════════════════════

/-! The trit's verdict alphabet `{decline, abstain, accept}` maps bijectively onto the
    three Bule faces of `ThreePhysicsForkRaceFoldBijection.BuleFace`
    (`{Diversity, WasteReduction, Optimality}`). The middle `abstain` — the clinamen `+1` —
    lands on `Optimality`, whose docstring is the "opportunity / action" coordinate. So the
    Bule's opportunity face IS the clinamen middle, the waste face the decline, the
    diversity face the accept. This makes "this is the Bule" a checked bijection. -/

/-- The verdict → Bule-face map. The clinamen middle `abstain` lands on the
    `Optimality` (opportunity / action) face; `decline` on `WasteReduction`; `accept` on
    `Diversity`. -/
def verdictToBule : Verdict → ThreePhysicsForkRaceFoldBijection.BuleFace
  | .abstain => .Optimality
  | .decline => .WasteReduction
  | .accept  => .Diversity

/-- The inverse: Bule-face → verdict. -/
def buleToVerdict : ThreePhysicsForkRaceFoldBijection.BuleFace → Verdict
  | .Optimality     => .abstain
  | .WasteReduction => .decline
  | .Diversity      => .accept

/-- Left inverse: `buleToVerdict ∘ verdictToBule = id` on `Verdict`. -/
theorem verdictToBule_left_inverse (v : Verdict) :
    buleToVerdict (verdictToBule v) = v := by
  cases v <;> rfl

/-- Right inverse: `verdictToBule ∘ buleToVerdict = id` on `BuleFace`. -/
theorem verdictToBule_right_inverse (f : ThreePhysicsForkRaceFoldBijection.BuleFace) :
    verdictToBule (buleToVerdict f) = f := by
  cases f <;> rfl

/-- `verdictToBule` is injective (decide-checked over the finite domain via the inverse). -/
theorem verdictToBule_injective :
    ∀ a b : Verdict, verdictToBule a = verdictToBule b → a = b := by
  intro a b h
  have h' : buleToVerdict (verdictToBule a) = buleToVerdict (verdictToBule b) :=
    congrArg buleToVerdict h
  rw [verdictToBule_left_inverse a, verdictToBule_left_inverse b] at h'
  exact h'

/-- `verdictToBule` is surjective (every face is hit, witnessed by `buleToVerdict`). -/
theorem verdictToBule_surjective :
    ∀ f : ThreePhysicsForkRaceFoldBijection.BuleFace, ∃ v : Verdict, verdictToBule v = f := by
  intro f
  exact ⟨buleToVerdict f, verdictToBule_right_inverse f⟩

/-- **`triton_middle_is_opportunity`** — the clinamen middle maps to the opportunity face.
    `verdictToBule .abstain = .Optimality`: the trit's neutral middle (the clinamen `+1`)
    lands exactly on the Bule's opportunity / action coordinate. -/
theorem triton_middle_is_opportunity :
    verdictToBule .abstain = ThreePhysicsForkRaceFoldBijection.BuleFace.Optimality := by
  decide

/-- **`triton_is_the_bule`** — the keystone bijection (TIGHT).

    The verdict alphabet and the Bule faces are in bijection under `verdictToBule`:

      (a) it is injective and surjective (a bijection), with `buleToVerdict` the two-sided
          inverse;
      (b) the clinamen middle `abstain` lands on `Optimality` (the opportunity / action
          face) — the middle IS the opportunity coordinate;
      (c) the two definite verdicts land on the two remaining faces:
          `decline ↦ WasteReduction`, `accept ↦ Diversity`.

    So waste / opportunity / diversity = decline / abstain / accept, as a checked
    bijection. -/
theorem triton_is_the_bule :
    -- (a) bijection with explicit two-sided inverse
    ( (∀ a b : Verdict, verdictToBule a = verdictToBule b → a = b)
      ∧ (∀ f : ThreePhysicsForkRaceFoldBijection.BuleFace,
          ∃ v : Verdict, verdictToBule v = f)
      ∧ (∀ v : Verdict, buleToVerdict (verdictToBule v) = v)
      ∧ (∀ f : ThreePhysicsForkRaceFoldBijection.BuleFace,
          verdictToBule (buleToVerdict f) = f) )
    -- (b) the middle is opportunity
    ∧ verdictToBule .abstain = ThreePhysicsForkRaceFoldBijection.BuleFace.Optimality
    -- (c) the definite faces
    ∧ verdictToBule .decline = ThreePhysicsForkRaceFoldBijection.BuleFace.WasteReduction
    ∧ verdictToBule .accept = ThreePhysicsForkRaceFoldBijection.BuleFace.Diversity := by
  refine ⟨⟨verdictToBule_injective, verdictToBule_surjective,
           verdictToBule_left_inverse, verdictToBule_right_inverse⟩, ?_, ?_, ?_⟩
  · exact triton_middle_is_opportunity
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- §2  triton_void_equivalence_resolved — discharging the OPEN question
-- ══════════════════════════════════════════════════════════

/-! `ThreePhysicsForkRaceFoldBijection.OpenTritonVoidEquivalence` was a `True` stub asking
    whether the trit, the Bule faces, and the void/abstain medium are one structure. With
    the keystone bijection (§1) and `ClinamenUnification.clinamen_is_the_generator`, the
    real statement is now provable. We state it as a genuine Prop and prove it; the upstream
    `True` def is left untouched (a downstream pointer, not an edit — no import cycle). -/

/-- **`TritonVoidEquivalence`** — the genuine Prop the corpus's `OpenTritonVoidEquivalence`
    stub was a placeholder for. The trit, the Bule faces, and the sign-0 / abstain medium
    are one structure:

      * trit ↔ Bule: `verdictToBule` is a bijection (the keystone);
      * the trit's middle and the Bule's opportunity face are the same element under it;
      * the sign-0 / abstain medium IS that same middle — the four domain characterizations
        of "the middle" in `clinamen_is_the_generator` all pick out `abstain`. -/
def TritonVoidEquivalence : Prop :=
  -- trit ↔ Bule is a bijection
  ( (∀ a b : Verdict, verdictToBule a = verdictToBule b → a = b)
    ∧ (∀ f : ThreePhysicsForkRaceFoldBijection.BuleFace,
        ∃ v : Verdict, verdictToBule v = f) )
  -- the trit middle = the Bule opportunity face = the sign-0 medium, all `abstain`
  ∧ verdictToBule .abstain = ThreePhysicsForkRaceFoldBijection.BuleFace.Optimality
  ∧ (∀ v : Verdict, sign v = 0 ↔ v = .abstain)
  -- the abstain middle is the clinamen-added third value (no Boolean preimage)
  ∧ (∀ v : Verdict, (¬ ∃ b : Bool, Gnosis.TritonForkRaceFold.embedBool b = v) ↔ v = .abstain)

/-- **`triton_void_equivalence_resolved`** — the open question is discharged. The trit, the
    Bule faces, and the sign-0 / abstain medium are one structure: the verdict↔face
    bijection holds, the trit middle maps to the opportunity face, and the four domain
    characterizations of "the middle" (`clinamen_is_the_generator`) coincide on `abstain`.
    This replaces the `True`-stub `OpenTritonVoidEquivalence` with real content. -/
theorem triton_void_equivalence_resolved : TritonVoidEquivalence := by
  refine ⟨⟨verdictToBule_injective, verdictToBule_surjective⟩,
          triton_middle_is_opportunity, ?_, ?_⟩
  · exact (Gnosis.ClinamenUnification.clinamen_is_the_generator).2.1
  · exact (Gnosis.ClinamenUnification.clinamen_is_the_generator).1

/-- The resolution genuinely answers the upstream stub: the stub
    `OpenTritonVoidEquivalence` is inhabited (it is `True`), and the real
    `TritonVoidEquivalence` is also inhabited — but the latter carries content the former
    lacked. Recorded as a concrete tie between the two. -/
theorem open_triton_void_equivalence_now_has_content :
    ThreePhysicsForkRaceFoldBijection.OpenTritonVoidEquivalence ∧ TritonVoidEquivalence :=
  ⟨trivial, triton_void_equivalence_resolved⟩

-- ══════════════════════════════════════════════════════════
-- §3  born_bridge — the QM Born shadow vs the standing-wave Born
-- ══════════════════════════════════════════════════════════

/-! `QuantumMechanics.born_rule_projection` is `Complex.norm_sq psi = re² + im²`. On a
    bare-trit-shaped Complex shadow this is DEGENERATE (it cannot separate the two definite
    verdicts), exactly as `StandingWaveAmplitudeBridge.trit_born_is_degenerate` shows for
    the Nat intensity. The genuine, non-degenerate Born lives on the VARYING standing-wave
    amplitude (`born_intensity_is_weight`). We prove the documented correspondence, NOT a
    forced Complex = Nat equality — graded DOCUMENTED-CORRESPONDENCE. -/

/-- The bare-trit Complex shadow of a verdict: a `Complex` whose real part is the verdict's
    sign and whose imaginary part is `0`. This is the most direct embedding of the bare trit
    into the QM `Complex` shadow. -/
def tritComplex (v : Verdict) : Gnosis.QuantumMechanics.Complex :=
  { re := sign v, im := 0 }

/-- On the bare-trit shadow, `born_rule_projection` is the squared sign, `(sign v)²`. -/
theorem born_projection_is_sign_sq (v : Verdict) :
    Gnosis.QuantumMechanics.born_rule_projection (tritComplex v) = sign v * sign v := by
  unfold Gnosis.QuantumMechanics.born_rule_projection Gnosis.QuantumMechanics.Complex.norm_sq
    tritComplex
  simp

/-- The bare-trit Complex Born projection is `{0, 1}`-valued for every verdict. -/
theorem born_projection_is_zero_or_one (v : Verdict) :
    Gnosis.QuantumMechanics.born_rule_projection (tritComplex v) = 0
    ∨ Gnosis.QuantumMechanics.born_rule_projection (tritComplex v) = 1 := by
  cases v <;> (rw [born_projection_is_sign_sq]; decide)

/-- **The Complex shadow is DEGENERATE on the bare trit.** The two distinct definite
    verdicts `accept` and `decline` get the SAME Complex Born projection `1`, so the shadow
    cannot separate them — exactly the degeneracy `trit_born_is_degenerate` records for the
    Nat intensity. This is why the bare trit is the wrong carrier for Born. -/
theorem born_complex_shadow_degenerate :
    Verdict.accept ≠ Verdict.decline
    ∧ Gnosis.QuantumMechanics.born_rule_projection (tritComplex .accept) = 1
    ∧ Gnosis.QuantumMechanics.born_rule_projection (tritComplex .decline) = 1
    ∧ Gnosis.QuantumMechanics.born_rule_projection (tritComplex .accept)
        = Gnosis.QuantumMechanics.born_rule_projection (tritComplex .decline) := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [born_projection_is_sign_sq]; decide
  · rw [born_projection_is_sign_sq]; decide
  · rw [born_projection_is_sign_sq, born_projection_is_sign_sq]; decide

/-- The bare-trit Complex Born projection agrees numerically with the Nat trit intensity
    `intensity (tritAmplitude v)` for every verdict (`(sign v)² = |sign v|²`). The two
    degenerate carriers coincide — and both are degenerate. -/
theorem born_complex_matches_trit_intensity (v : Verdict) :
    Gnosis.QuantumMechanics.born_rule_projection (tritComplex v)
      = (Gnosis.StandingWaveAmplitudeBridge.intensity
          (Gnosis.StandingWaveAmplitudeBridge.tritAmplitude v) : Int) := by
  cases v <;>
    (rw [born_projection_is_sign_sq]
     decide)

/-- **`born_bridge`** — the Born shadow, honestly scoped (DOCUMENTED CORRESPONDENCE).

    The isolated `QuantumMechanics.born_rule_projection` (a `Complex.norm_sq`) connects to
    the standing-wave Born content as a DOCUMENTED correspondence, not a forced equality:

      (a) on the bare-trit Complex shadow it is `(sign v)²`, `{0,1}`-valued;
      (b) it is DEGENERATE — the two distinct definite verdicts share Born projection `1`,
          mirroring `StandingWaveAmplitudeBridge.trit_born_is_degenerate` for the Nat
          intensity (and the two carriers agree numerically,
          `born_complex_matches_trit_intensity`);
      (c) therefore the genuine, non-degenerate Born lives NOT on the bare trit but on the
          VARYING standing-wave amplitude: `born_intensity_is_weight` holds for every
          `StandingWaveMode` (node ⇒ zero weight; positive weight ⇔ antinode).

    We deliberately do NOT claim a Complex = Nat equality of the two Born notions — the
    honest statement is that the bare Complex shadow is degenerate and the real Born is on
    the medium. -/
theorem born_bridge :
    -- (a) bare-trit Complex Born is (sign)², {0,1}-valued
    (∀ v : Verdict, Gnosis.QuantumMechanics.born_rule_projection (tritComplex v)
        = sign v * sign v)
    ∧ (∀ v : Verdict, Gnosis.QuantumMechanics.born_rule_projection (tritComplex v) = 0
        ∨ Gnosis.QuantumMechanics.born_rule_projection (tritComplex v) = 1)
    -- (b) degenerate, and agrees numerically with the Nat trit intensity
    ∧ (Verdict.accept ≠ Verdict.decline
        ∧ Gnosis.QuantumMechanics.born_rule_projection (tritComplex .accept)
            = Gnosis.QuantumMechanics.born_rule_projection (tritComplex .decline))
    ∧ (∀ v : Verdict, Gnosis.QuantumMechanics.born_rule_projection (tritComplex v)
        = (Gnosis.StandingWaveAmplitudeBridge.intensity
            (Gnosis.StandingWaveAmplitudeBridge.tritAmplitude v) : Int))
    -- (b') the bare trit is degenerate (the Nat statement, cited)
    ∧ ((∀ v : Verdict, Gnosis.StandingWaveAmplitudeBridge.intensity
          (Gnosis.StandingWaveAmplitudeBridge.tritAmplitude v) = 0
          ∨ Gnosis.StandingWaveAmplitudeBridge.intensity
              (Gnosis.StandingWaveAmplitudeBridge.tritAmplitude v) = 1)
        ∧ (Verdict.accept ≠ Verdict.decline
            ∧ Gnosis.StandingWaveAmplitudeBridge.intensity
                (Gnosis.StandingWaveAmplitudeBridge.tritAmplitude .accept) = 1
            ∧ Gnosis.StandingWaveAmplitudeBridge.intensity
                (Gnosis.StandingWaveAmplitudeBridge.tritAmplitude .decline) = 1)
        ∧ (Gnosis.StandingWaveAmplitudeBridge.intensity
            (Gnosis.StandingWaveAmplitudeBridge.tritAmplitude .decline)
            + Gnosis.StandingWaveAmplitudeBridge.intensity
                (Gnosis.StandingWaveAmplitudeBridge.tritAmplitude .abstain)
            + Gnosis.StandingWaveAmplitudeBridge.intensity
                (Gnosis.StandingWaveAmplitudeBridge.tritAmplitude .accept) = 2))
    -- (c) the REAL, non-degenerate Born on the varying standing-wave amplitude
    ∧ (∀ (F : Gnosis.FailureAsStandingWave.FalsificationSet)
          (m : Gnosis.FailureAsStandingWave.StandingWaveMode F),
        (∀ c : Gnosis.FailureAsStandingWave.Claim,
            F.isFalsified c = true → Gnosis.StandingWaveAmplitudeBridge.modeIntensity m c = 0)
        ∧ (∀ c : Gnosis.FailureAsStandingWave.Claim,
            0 < Gnosis.StandingWaveAmplitudeBridge.modeIntensity m c ↔ 0 < m.amplitude c)) := by
  refine ⟨born_projection_is_sign_sq, born_projection_is_zero_or_one, ?_,
          born_complex_matches_trit_intensity, ?_, ?_⟩
  · exact ⟨(born_complex_shadow_degenerate).1, (born_complex_shadow_degenerate).2.2.2⟩
  · exact Gnosis.StandingWaveAmplitudeBridge.trit_born_is_degenerate
  · intro F m
    exact ⟨(Gnosis.StandingWaveAmplitudeBridge.born_intensity_is_weight F m).1,
           (Gnosis.StandingWaveAmplitudeBridge.born_intensity_is_weight F m).2.1⟩

-- ══════════════════════════════════════════════════════════
-- §4  amplitude_bridge — the SW mode node = the trit node = abstain
-- ══════════════════════════════════════════════════════════

/-! `FailureAsStandingWave.StandingWaveMode.amplitude` carries a Dirichlet boundary
    condition (`vanishesOnFalsified`): amplitude is `0` on falsified claims. The bare-trit
    amplitude `StandingWaveAmplitudeBridge.tritAmplitude` has its unique zero (node) at
    `abstain` (`node_is_abstain`). This bridge ties the two zero-amplitude states together:
    the standing wave's node and the trit's neutral middle are the same element. -/

/-- **`amplitude_bridge`** — the SW mode's zero-amplitude state is the trit node = abstain.

      (a) the trit node is exactly `abstain`: `tritAmplitude v = 0 ↔ v = abstain`
          (`node_is_abstain`), and `tritAmplitude .abstain = 0`;
      (b) on any `StandingWaveMode`, a falsified claim (Dirichlet node) has zero amplitude
          (`vanishesOnFalsified`) — the mode's node;
      (c) so the SW mode's node and the trit's node coincide as zero-amplitude states, and
          the trit's unique node is the clinamen middle `abstain`. -/
theorem amplitude_bridge :
    -- (a) the trit node is abstain (uniquely)
    ( Gnosis.StandingWaveAmplitudeBridge.tritAmplitude .abstain = 0
      ∧ (∀ v : Verdict, Gnosis.StandingWaveAmplitudeBridge.tritAmplitude v = 0
          ↔ v = .abstain) )
    -- (b) the SW mode's Dirichlet node: amplitude vanishes on falsified claims
    ∧ (∀ (F : Gnosis.FailureAsStandingWave.FalsificationSet)
          (m : Gnosis.FailureAsStandingWave.StandingWaveMode F)
          (c : Gnosis.FailureAsStandingWave.Claim),
        F.isFalsified c = true → m.amplitude c = 0)
    -- (c) and on the SW mode the zero-intensity node coincides with the zero-amplitude node
    ∧ (∀ (F : Gnosis.FailureAsStandingWave.FalsificationSet)
          (m : Gnosis.FailureAsStandingWave.StandingWaveMode F)
          (c : Gnosis.FailureAsStandingWave.Claim),
        F.isFalsified c = true → Gnosis.StandingWaveAmplitudeBridge.modeIntensity m c = 0) := by
  refine ⟨⟨Gnosis.StandingWaveAmplitudeBridge.tritAmplitude_abstain,
           Gnosis.StandingWaveAmplitudeBridge.node_is_abstain⟩, ?_, ?_⟩
  · intro F m c hF
    exact m.vanishesOnFalsified c hF
  · intro F m c hF
    exact Gnosis.StandingWaveAmplitudeBridge.modeIntensity_zero_on_falsified F m c hF

-- ══════════════════════════════════════════════════════════
-- §5  vent_gravity_upgraded — the score-label upgraded to real geometry
-- ══════════════════════════════════════════════════════════

/-! `ForkRaceFoldVentAreForces.vent_is_gravity` is a score-tripling LABEL
    (`score (vent b) = 3 · score b`). The genuine geometric content now exists downstream:
    `AnalogGravityLensing.lensing_bends_toward_mass` (the void sources real ray bending —
    kinematics) and `BoundedGravitationalResidual.void_sources_stress_energy` (the void
    sources a discriminating field-equation curvature residual — dynamics). This bridge
    cites the old label alongside the new real content, marking the upgrade. It does NOT
    claim the score label was ever geometry. -/

/-- **`vent_gravity_upgraded`** — the vent/void label, upgraded to real bending + curvature.

      (LABEL)      `vent_is_gravity`: `score (vent b) = 3 · score b` for every BuleyUnit —
                   the original score-tripling label (cited, not re-proved geometrically);
      (KINEMATICS) `lensing_bends_toward_mass`: with the void on, the least-cost geodesic
                   bends toward the mass (deflection `> 0`, strictly cheaper than straight,
                   a genuine least-cost path over the finite grid);
      (DYNAMICS)   `void_sources_stress_energy`: the stress-energy IS the void/vent medium
                   density, and at the sourced cell the nonzero discrete curvature `G = 6`
                   equals `κ·T = 6` — the medium genuinely sources curvature.

    The vent/void medium genuinely sources bending and curvature. (Continuum Einstein
    dynamics / existence remain OPEN — see the dependencies' frontiers and §7.) -/
theorem vent_gravity_upgraded :
    -- (LABEL) the score-tripling vent_is_gravity, cited
    (∀ b : Gnosis.SpectralNoiseEquilibrium.BuleyUnit,
        Gnosis.SpectralNoiseEquilibrium.buleyUnitScore (ForkRaceFoldVentAreForces.vent_operator b)
          = 3 * Gnosis.SpectralNoiseEquilibrium.buleyUnitScore b)
    -- (KINEMATICS) real lensing: the geodesic bends toward the mass
    ∧ ( Gnosis.AnalogGravityLensing.bendsTowardMass
          (Gnosis.AnalogGravityLensing.geodesic Gnosis.AnalogGravityLensing.indexMass)
        ∧ Gnosis.AnalogGravityLensing.pathCost Gnosis.AnalogGravityLensing.indexMass
              (Gnosis.AnalogGravityLensing.geodesic Gnosis.AnalogGravityLensing.indexMass)
            < Gnosis.AnalogGravityLensing.pathCost Gnosis.AnalogGravityLensing.indexMass
                Gnosis.AnalogGravityLensing.straightPath )
    -- (DYNAMICS) real curvature source: stress-energy is the void medium; G = κ·T at the sourced cell
    ∧ ( (∀ cell : Gnosis.BoundedGravitationalResidual.EinsteinCell,
            Gnosis.BoundedGravitationalResidual.stressEnergy cell = (cell.voidAmplitude : Int))
        ∧ (Gnosis.BoundedGravitationalResidual.discreteCurvature
              Gnosis.BoundedGravitationalResidual.sourcedCell
            = Gnosis.BoundedGravitationalResidual.sourceTerm
                Gnosis.BoundedGravitationalResidual.sourcedCell
          ∧ Gnosis.BoundedGravitationalResidual.discreteCurvature
              Gnosis.BoundedGravitationalResidual.sourcedCell = 6) ) := by
  refine ⟨ForkRaceFoldVentAreForces.vent_is_gravity, ?_, ?_⟩
  · exact ⟨(Gnosis.AnalogGravityLensing.lensing_bends_toward_mass).1,
           (Gnosis.AnalogGravityLensing.lensing_bends_toward_mass).2.1⟩
  · exact ⟨(Gnosis.BoundedGravitationalResidual.void_sources_stress_energy).1,
           (Gnosis.BoundedGravitationalResidual.void_sources_stress_energy).2.2.2⟩

-- ══════════════════════════════════════════════════════════
-- §6  MASTER — the reintegration conjunction
-- ══════════════════════════════════════════════════════════

/-- **`triton_reintegration_master`** — the clinamen / triton arc, reconnected.

    The conjunction of the five bridges:

      (1) KEYSTONE (tight bijection) — the verdict alphabet is in bijection with the Bule
          faces; the clinamen middle `abstain` is the opportunity face (`triton_is_the_bule`).
      (2) OPEN QUESTION RESOLVED (real) — the trit, the Bule faces, and the sign-0 / abstain
          medium are one structure, discharging `OpenTritonVoidEquivalence`
          (`triton_void_equivalence_resolved`).
      (3) BORN (documented correspondence) — the bare-trit Complex Born shadow is degenerate;
          the real Born is on the varying standing-wave amplitude (`born_bridge`).
      (4) AMPLITUDE (real) — the SW mode's zero-amplitude node is the trit node = abstain
          (`amplitude_bridge`).
      (5) VENT/GRAVITY (real) — the vent/void label is upgraded to real bending + curvature
          (`vent_gravity_upgraded`).

    HONESTY: only bridges (1), (2), (4), (5) are tight/real; bridge (3) is a documented
    correspondence (the bare-trit shadow is degenerate and we do not force a Complex = Nat
    equality). GR continuum existence / smoothness remains OPEN. `VacuumIsOnlyForce` is
    deliberately left unbridged (tautological — bridging it would let a tautology pose as
    real work). Rhetorical force is not evidence; the content is exactly these checked
    conjuncts. -/
theorem triton_reintegration_master :
    -- (1) KEYSTONE — verdict ↔ Bule bijection, middle ↦ opportunity
    ( ( (∀ a b : Verdict, verdictToBule a = verdictToBule b → a = b)
        ∧ (∀ f : ThreePhysicsForkRaceFoldBijection.BuleFace,
            ∃ v : Verdict, verdictToBule v = f)
        ∧ (∀ v : Verdict, buleToVerdict (verdictToBule v) = v)
        ∧ (∀ f : ThreePhysicsForkRaceFoldBijection.BuleFace,
            verdictToBule (buleToVerdict f) = f) )
      ∧ verdictToBule .abstain = ThreePhysicsForkRaceFoldBijection.BuleFace.Optimality
      ∧ verdictToBule .decline = ThreePhysicsForkRaceFoldBijection.BuleFace.WasteReduction
      ∧ verdictToBule .accept = ThreePhysicsForkRaceFoldBijection.BuleFace.Diversity )
    -- (2) OPEN QUESTION RESOLVED — the trit/Bule/medium are one structure
    ∧ TritonVoidEquivalence
    -- (3) BORN — bare shadow degenerate; real Born on the varying amplitude
    ∧ ( (∀ v : Verdict, Gnosis.QuantumMechanics.born_rule_projection (tritComplex v)
            = sign v * sign v)
        ∧ (Verdict.accept ≠ Verdict.decline
            ∧ Gnosis.QuantumMechanics.born_rule_projection (tritComplex .accept)
                = Gnosis.QuantumMechanics.born_rule_projection (tritComplex .decline))
        ∧ (∀ (F : Gnosis.FailureAsStandingWave.FalsificationSet)
              (m : Gnosis.FailureAsStandingWave.StandingWaveMode F),
            (∀ c : Gnosis.FailureAsStandingWave.Claim,
                F.isFalsified c = true
                  → Gnosis.StandingWaveAmplitudeBridge.modeIntensity m c = 0)
            ∧ (∀ c : Gnosis.FailureAsStandingWave.Claim,
                0 < Gnosis.StandingWaveAmplitudeBridge.modeIntensity m c
                  ↔ 0 < m.amplitude c)) )
    -- (4) AMPLITUDE — the SW mode node is the trit node = abstain
    ∧ ( Gnosis.StandingWaveAmplitudeBridge.tritAmplitude .abstain = 0
        ∧ (∀ v : Verdict, Gnosis.StandingWaveAmplitudeBridge.tritAmplitude v = 0
            ↔ v = .abstain)
        ∧ (∀ (F : Gnosis.FailureAsStandingWave.FalsificationSet)
              (m : Gnosis.FailureAsStandingWave.StandingWaveMode F)
              (c : Gnosis.FailureAsStandingWave.Claim),
            F.isFalsified c = true → m.amplitude c = 0) )
    -- (5) VENT/GRAVITY — the label upgraded to real bending + curvature
    ∧ ( (∀ b : Gnosis.SpectralNoiseEquilibrium.BuleyUnit,
            Gnosis.SpectralNoiseEquilibrium.buleyUnitScore
              (ForkRaceFoldVentAreForces.vent_operator b)
              = 3 * Gnosis.SpectralNoiseEquilibrium.buleyUnitScore b)
        ∧ Gnosis.AnalogGravityLensing.bendsTowardMass
            (Gnosis.AnalogGravityLensing.geodesic Gnosis.AnalogGravityLensing.indexMass)
        ∧ (Gnosis.BoundedGravitationalResidual.discreteCurvature
              Gnosis.BoundedGravitationalResidual.sourcedCell
            = Gnosis.BoundedGravitationalResidual.sourceTerm
                Gnosis.BoundedGravitationalResidual.sourcedCell
          ∧ Gnosis.BoundedGravitationalResidual.discreteCurvature
              Gnosis.BoundedGravitationalResidual.sourcedCell = 6) ) := by
  refine ⟨?_, triton_void_equivalence_resolved, ?_, ?_, ?_⟩
  · -- (1) keystone
    exact triton_is_the_bule
  · -- (3) Born: pull the needed conjuncts from born_bridge
    refine ⟨born_bridge.1, ?_, ?_⟩
    · exact born_bridge.2.2.1
    · exact born_bridge.2.2.2.2.2
  · -- (4) amplitude
    refine ⟨amplitude_bridge.1.1, amplitude_bridge.1.2, amplitude_bridge.2.1⟩
  · -- (5) vent/gravity
    refine ⟨vent_gravity_upgraded.1, vent_gravity_upgraded.2.1.1, vent_gravity_upgraded.2.2.2⟩

-- ══════════════════════════════════════════════════════════
-- §7  Reading
-- ══════════════════════════════════════════════════════════

/-! The clinamen / triton arc had grown across eight modules in isolation. This module is
the one downstream place where the pieces are reconnected as checked cross-module theorems,
without editing any heavy upstream module (they get doc-comments only — no import cycle, no
broken proof).

The KEYSTONE (`triton_is_the_bule`) is a tight bijection: the verdict alphabet
`{decline, abstain, accept}` maps bijectively onto the Bule faces
`{WasteReduction, Optimality, Diversity}`, with the clinamen middle `abstain` landing on the
opportunity / action face `Optimality` (`triton_middle_is_opportunity`). Waste / opportunity
/ diversity = decline / abstain / accept, as a `decide`-checked bijection with a two-sided
inverse.

`triton_void_equivalence_resolved` discharges the corpus's `OpenTritonVoidEquivalence` stub
(a `True` placeholder) with a genuine Prop: the trit, the Bule faces, and the sign-0 /
abstain medium are one structure, reusing the bijection and
`ClinamenUnification.clinamen_is_the_generator`.

`born_bridge` is a DOCUMENTED CORRESPONDENCE, honestly graded: the bare-trit Complex shadow
of `QuantumMechanics.born_rule_projection` is `(sign v)²`, `{0,1}`-valued and DEGENERATE
(the two definite verdicts share Born projection `1`), so the genuine non-degenerate Born
lives on the varying standing-wave amplitude (`born_intensity_is_weight`), not on the bare
trit. We do not force a Complex = Nat equality.

`amplitude_bridge` ties `FailureAsStandingWave.StandingWaveMode.amplitude` (with its
Dirichlet `vanishesOnFalsified`) to `StandingWaveAmplitudeBridge.tritAmplitude` /
`node_is_abstain`: the SW mode's zero-amplitude node and the trit node are the same element,
`abstain`.

`vent_gravity_upgraded` cite-bridges `ForkRaceFoldVentAreForces.vent_is_gravity` (a
score-tripling label) to the now-real `AnalogGravityLensing.lensing_bends_toward_mass`
(kinematics) and `BoundedGravitationalResidual.void_sources_stress_energy` (dynamics): the
vent/void medium genuinely sources bending and a discriminating curvature residual.

`triton_reintegration_master` is the honest conjunction of all five. GR continuum existence
/ smoothness remains OPEN. `VacuumIsOnlyForce` is deliberately NOT bridged: it is
tautological, and forcing a bridge would let a tautology masquerade as discharging real
work.

-- Next exploration:  (B34a)
--   Strengthen the keystone from a bare bijection of finite alphabets to a STRUCTURE
--   bijection that also carries the dynamics. Right now `verdictToBule` is a bijection of
--   three-element types; the sharper claim is that it is an ISOMORPHISM of the
--   fork/race/fold structure: prove that `verdictToBule` intertwines the trit's `quorum` /
--   `fold` (the safety-first three-witness fold in `TritonCanonical` / `TritonForkRaceFold`)
--   with `ThreePhysicsForkRaceFoldBijection.faceToPrimitive` composed with the scheduler
--   primitives — i.e. that the verdict fold and the Bule-face → primitive map commute,
--   making "trit ≅ Bule" an isomorphism of the WHOLE diagram (alphabet + operation), not
--   just the carrier sets. A sibling line: tie `OpenThirdPhysicsContent` and
--   `OpenForkBijectionToDeaths` (the other two `True` stubs in
--   `ThreePhysicsForkRaceFoldBijection §10`) to real content the same way
--   `triton_void_equivalence_resolved` ties `OpenTritonVoidEquivalence` — the third physics'
--   diversity/fork content via `clinamen_is_the_generator`'s computation projection, and the
--   fork↔death conjugacy via the existing Five-Deaths modules — discharging all three open
--   props downstream without editing the upstream `True` defs.
-/

end TritonReintegration
end Gnosis
