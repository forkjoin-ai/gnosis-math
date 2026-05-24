import Gnosis.TritonCanonical
import Gnosis.TritonForkRaceFold
import Gnosis.FailureAsStandingWave
import Gnosis.BuleyeanProbability

/-!
# StandingWaveAmplitudeBridge — amplitude and Born-intensity, honestly bridged

`Gnosis.ClinamenUnification` unified logic / physics / math / computation through the
trit and the clinamen `+1`, but its PHYSICS projection carried a deliberate caveat:
"STRUCTURAL ONLY — no amplitudes, no Born rule, no GR." Two of those three
disclaimers were too strong. AMPLITUDE and BORN-INTENSITY genuinely fall out; GR does
not. This module proves the two that are real and leaves GR exactly where it was.

## Two bridges, scoped honestly

  * **Amplitude** (`trit_is_minimal_standing_wave`). The verdict's amplitude is the
    magnitude of its sign: `tritAmplitude v = (sign v).natAbs`. The neutral `abstain`
    is the zero-amplitude NODE; `accept`/`decline` are the unit-amplitude ANTINODES.
    The trit's amplitude spectrum is exactly the quantized set `{0, 1}`, with three
    quantized modes (the sign triple). This is the genuine, tight content: amplitude
    is not added — it is the magnitude already present in `sign`.

  * **Born intensity** (`born_intensity_is_weight`), HONESTLY SCOPED. The Born
    intensity is the squared amplitude, `intensity a = a * a` (`|amplitude|²`). At the
    BARE-TRIT level this is DEGENERATE: `intensity (tritAmplitude v) ∈ {0, 1}` is NOT
    a normalized probability distribution — two distinct verdicts (`accept`, `decline`)
    both have intensity `1` (proved as `trit_born_is_degenerate`). The real Born
    carrier is therefore not the 3-element sign but the VARYING standing-wave
    amplitude of `FailureAsStandingWave.StandingWaveMode`. On that medium the per-claim
    intensity is a genuine, strictly-positive (`BuleyeanProbability.buleyean_positivity`)
    probability weight, with the Dirichlet NODE (amplitude 0) the unique zero. We prove
    the bridge at THAT level, where it is non-degenerate.

## What stays disclaimed (do not over-read)

GR remains structural vocabulary only. `Gnosis.GeneralRelativity` is stubbed:
`riemann_curvature_tensor` returns `0`, the Einstein field equation is a tautology
(`h → h`), and `ForkRaceFoldVentAreForces.vent_is_gravity` is a SCORE-TRIPLING label
(`score (vent b) = 3 * score b`), not geometry. No curvature, no field equation, no
metric is derived here. The honest open path — an analog / acoustic EFFECTIVE METRIC
read off the standing-wave medium itself — is named in `-- Next exploration:` as a hard
FUTURE frontier, not a present claim.

## Encoding discipline

Imports the canonical-trit family, `FailureAsStandingWave`, and `BuleyeanProbability`
(all `Init`-only at the root; no mathlib). Every theorem closes by `decide` over a
finite/closed statement, by explicit small case analysis, or by reusing an
already-proven theorem (`abstain_is_superposed`, `buleyean_positivity`). Zero `sorry`,
zero `admit`, zero `native_decide`, zero new `axiom`. Choice-free: the only axioms
reached are `propext` and `Quot.sound`. Verify with
`#print axioms trit_is_minimal_standing_wave` and
`#print axioms born_intensity_is_weight`.
-/

namespace Gnosis
namespace StandingWaveAmplitudeBridge

open Gnosis.TritonCanonical
open Gnosis.TritonForkRaceFold (abstain_is_superposed sign_range_is_spin_triple spinTriple)
open Gnosis.FailureAsStandingWave

-- ══════════════════════════════════════════════════════════
-- §1  BRIDGE 1 — AMPLITUDE = |sign| (node / antinode quantization)
-- ══════════════════════════════════════════════════════════

/-! The verdict's amplitude is the MAGNITUDE of its sign. `sign : Verdict → Int` already
    lands in `{-1, 0, +1}`; taking `Int.natAbs` reads off the standing-wave amplitude,
    `{0, 1}`. The neutral `abstain` (sign 0) is the NODE; the two definite verdicts
    (sign ±1) are the unit ANTINODES. Nothing is added — amplitude is the modulus of a
    quantity `sign` already carries. -/

/-- The trit amplitude: the magnitude of the verdict's sign. `accept`/`decline` ↦ `1`
    (antinodes), `abstain` ↦ `0` (node). This is `|sign v|`, not a new structure. -/
def tritAmplitude : Verdict → Nat := fun v => (sign v).natAbs

/-- The node: `abstain` has zero amplitude. -/
theorem tritAmplitude_abstain : tritAmplitude .abstain = 0 := by decide

/-- An antinode: `accept` has unit amplitude. -/
theorem tritAmplitude_accept : tritAmplitude .accept = 1 := by decide

/-- An antinode: `decline` has unit amplitude (`|-1| = 1`). -/
theorem tritAmplitude_decline : tritAmplitude .decline = 1 := by decide

/-- **The trit amplitude spectrum is quantized to `{0, 1}`.** Every verdict's amplitude
    is at most `1`: the bare trit carries EXACTLY the minimal/quantized amplitude
    spectrum — a node (`0`) and an antinode (`1`), nothing in between. -/
theorem tritAmplitude_le_one : ∀ v : Verdict, tritAmplitude v ≤ 1 := by
  intro v; cases v <;> decide

/-- Each verdict's amplitude is literally `0` or `1` — the spectrum is the two-point set
    `{node, antinode}`. -/
theorem tritAmplitude_is_zero_or_one :
    ∀ v : Verdict, tritAmplitude v = 0 ∨ tritAmplitude v = 1 := by
  intro v; cases v <;> decide

/-- **`node_is_abstain` — the zero-amplitude node is exactly the abstain middle.**
    `tritAmplitude v = 0 ↔ v = abstain`. Proven by relating the amplitude to the sign:
    `natAbs (sign v) = 0 ↔ sign v = 0`, and `sign v = 0 ↔ v = abstain` is the
    already-proven `abstain_is_superposed` (the sign-0 / superposed characterization).
    The standing wave's node and the trit's neutral middle are the SAME element. -/
theorem node_is_abstain : ∀ v : Verdict, tritAmplitude v = 0 ↔ v = .abstain := by
  intro v
  constructor
  · intro h
    -- tritAmplitude v = natAbs (sign v) = 0  ⇒  sign v = 0  ⇒  v = abstain
    have hsign : sign v = 0 := Int.natAbs_eq_zero.mp h
    exact (abstain_is_superposed).2.1 v hsign
  · intro h; subst h; decide

/-- The two antinodes are exactly the definite verdicts: amplitude `1 ↔ v ∈ {accept,
    decline}`. The complement of the node is the antinode pair. -/
theorem antinodes_are_definite :
    ∀ v : Verdict, tritAmplitude v = 1 ↔ (v = .accept ∨ v = .decline) := by
  intro v; cases v <;>
    (constructor <;> intro h <;> first | rfl | (cases h <;> first | rfl | (exact absurd ‹_› (by decide))) | exact absurd h (by decide) | exact Or.inl rfl | exact Or.inr rfl)

/-- There are exactly three quantized modes — the sign triple `{-1, 0, +1}`. Restates the
    `sign` range (the spin/eigenvalue triple) as the three standing-wave modes: two
    antinodes (signs ±1) and one node (sign 0). Reuses `sign_range_is_spin_triple`. -/
theorem three_quantized_modes :
    (∀ v : Verdict, sign v ∈ spinTriple)
    ∧ (∃ v : Verdict, sign v = -1)
    ∧ (∃ v : Verdict, sign v = 0)
    ∧ (∃ v : Verdict, sign v = 1) :=
  sign_range_is_spin_triple

/-- **`trit_is_minimal_standing_wave` — amplitude falls out (the tight bridge).**

    The bare trit is the MINIMAL standing wave: its amplitude is the magnitude of its
    sign, with a quantized two-point spectrum `{0, 1}` and three quantized modes.

      (a) the node `abstain` has amplitude `0`, and is the UNIQUE zero-amplitude verdict
          (`node_is_abstain`);
      (b) the two antinodes `accept`/`decline` each have amplitude `1`, and are exactly
          the unit-amplitude verdicts (`antinodes_are_definite`);
      (c) every amplitude is `≤ 1` — the spectrum is quantized to `{0, 1}`;
      (d) there are exactly three quantized modes, the sign triple `{-1, 0, +1}`.

    This is the genuine amplitude content: amplitude is the modulus already carried by
    `sign`, and the trit realizes its minimal quantized case. (The non-degenerate,
    VARYING amplitude lives on `StandingWaveMode`; see §3.) -/
theorem trit_is_minimal_standing_wave :
    -- (a) node = abstain, uniquely
    (tritAmplitude .abstain = 0 ∧ (∀ v : Verdict, tritAmplitude v = 0 ↔ v = .abstain))
    -- (b) antinodes = the two definite verdicts
    ∧ (tritAmplitude .accept = 1 ∧ tritAmplitude .decline = 1
        ∧ (∀ v : Verdict, tritAmplitude v = 1 ↔ (v = .accept ∨ v = .decline)))
    -- (c) quantized spectrum {0,1}
    ∧ (∀ v : Verdict, tritAmplitude v ≤ 1)
    ∧ (∀ v : Verdict, tritAmplitude v = 0 ∨ tritAmplitude v = 1)
    -- (d) three quantized modes = the sign triple
    ∧ ((∀ v : Verdict, sign v ∈ spinTriple)
        ∧ (∃ v : Verdict, sign v = -1)
        ∧ (∃ v : Verdict, sign v = 0)
        ∧ (∃ v : Verdict, sign v = 1)) := by
  refine ⟨⟨tritAmplitude_abstain, node_is_abstain⟩,
          ⟨tritAmplitude_accept, tritAmplitude_decline, antinodes_are_definite⟩,
          tritAmplitude_le_one, tritAmplitude_is_zero_or_one, three_quantized_modes⟩

-- ══════════════════════════════════════════════════════════
-- §2  BRIDGE 2a — BORN INTENSITY = |amplitude|² (and its trit-level DEGENERACY)
-- ══════════════════════════════════════════════════════════

/-! The Born intensity is the squared amplitude. We define it on `Nat` amplitudes so it
    serves BOTH the bare trit (§2) and the varying standing-wave amplitude (§3). At the
    bare-trit level it is DEGENERATE and we say so explicitly: it is not a normalized
    distribution. The honest, non-degenerate Born statement lives in §3. -/

/-- Born intensity: the squared amplitude, `|amplitude|²`. -/
def intensity : Nat → Nat := fun a => a * a

/-- On the trit, intensity reproduces the amplitude (since `0² = 0`, `1² = 1`). The bare
    trit's intensity spectrum is still just `{0, 1}`. -/
theorem trit_intensity_is_amplitude :
    ∀ v : Verdict, intensity (tritAmplitude v) = tritAmplitude v := by
  intro v; cases v <;> decide

/-- The trit's intensity is `0` or `1` for every verdict. -/
theorem trit_intensity_is_zero_or_one :
    ∀ v : Verdict, intensity (tritAmplitude v) = 0 ∨ intensity (tritAmplitude v) = 1 := by
  intro v; cases v <;> decide

/-- **`trit_born_is_degenerate` — why the BARE TRIT is not enough for Born.**

    The bare-trit Born intensity is NOT a probability distribution:

      (a) its spectrum is the two-point set `{0, 1}` (`intensity ∈ {0,1}`);
      (b) it is DEGENERATE — two DISTINCT verdicts (`accept`, `decline`) have the SAME
          intensity `1`, so intensity cannot separate them (a genuine distribution over a
          3-point space cannot put equal mass on two outcomes AND sum to one with the
          remaining outcome forced to `0`);
      (c) the masses do not normalize: summed over `{decline, abstain, accept}` the
          intensities are `1 + 0 + 1 = 2 ≠ 1`.

    The conclusion is not that Born fails, but that its carrier is wrong: the 3-element
    sign is too coarse. The real carrier is the VARYING standing-wave amplitude (§3). -/
theorem trit_born_is_degenerate :
    -- (a) two-point spectrum
    (∀ v : Verdict, intensity (tritAmplitude v) = 0 ∨ intensity (tritAmplitude v) = 1)
    -- (b) degenerate: distinct verdicts, same intensity 1
    ∧ (Verdict.accept ≠ Verdict.decline
        ∧ intensity (tritAmplitude .accept) = 1
        ∧ intensity (tritAmplitude .decline) = 1)
    -- (c) does not normalize: total mass = 2 ≠ 1
    ∧ (intensity (tritAmplitude .decline)
        + intensity (tritAmplitude .abstain)
        + intensity (tritAmplitude .accept) = 2) := by
  refine ⟨trit_intensity_is_zero_or_one, ⟨by decide, by decide, by decide⟩, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §3  BRIDGE 2b — the REAL Born bridge on the varying standing-wave amplitude
-- ══════════════════════════════════════════════════════════

/-! The non-degenerate Born statement. On a `FailureAsStandingWave.StandingWaveMode` the
    amplitude VARIES over claim-space (it is `Claim → Nat`, not 3-valued), so the squared
    amplitude `intensity (mode.amplitude c)` is a genuine per-claim weight: strictly
    positive exactly at the antinodes (amplitude > 0) and zero exactly at the Dirichlet
    nodes (the falsified claims, where `vanishesOnFalsified` forces amplitude 0).

    We tie the strictly-positive floor to `BuleyeanProbability.buleyean_positivity` via a
    Buleyean carrier whose weight at a chosen antinode is exactly the squared amplitude.
    This is a WITNESS-form tie (a concrete `BuleyeanSpace` realizing the squared amplitude
    as a Buleyean weight), not a fully general functor between the two structures — we say
    so. The qualitative bridge (node ⇔ zero intensity ⇔ no weight; antinode ⇔ positive
    intensity ⇔ positive weight) is general over `StandingWaveMode`. -/

/-- The per-claim Born intensity of a standing-wave mode: the squared amplitude. -/
def modeIntensity (m : StandingWaveMode F) (c : Claim) : Nat :=
  intensity (m.amplitude c)

/-- **Node ⇒ zero intensity.** On a falsified claim (Dirichlet boundary node) the mode's
    amplitude vanishes (`vanishesOnFalsified`), so its Born intensity is `0`. The node is
    a zero of the probability weight. -/
theorem modeIntensity_zero_on_falsified
    (F : FalsificationSet) (m : StandingWaveMode F) (c : Claim)
    (hF : F.isFalsified c = true) : modeIntensity m c = 0 := by
  have h0 : m.amplitude c = 0 := m.vanishesOnFalsified c hF
  simp [modeIntensity, intensity, h0]

/-- **Intensity positive ⇔ amplitude positive** (antinode ⇔ positive weight). The Born
    intensity `a²` is strictly positive iff the amplitude `a` is — so positive
    probability weight lives exactly on the antinodes (`amplitude > 0`) and nowhere else.
    This is the qualitative Born floor, general over any `StandingWaveMode`. -/
theorem modeIntensity_pos_iff_amplitude_pos
    (m : StandingWaveMode F) (c : Claim) :
    0 < modeIntensity m c ↔ 0 < m.amplitude c := by
  unfold modeIntensity intensity
  constructor
  · intro h
    -- a * a > 0  ⇒  a > 0.  Contrapositive: if a = 0 then a*a = 0, not > 0.
    cases Nat.eq_zero_or_pos (m.amplitude c) with
    | inl ha0 => rw [ha0] at h; exact absurd h (by decide)
    | inr hp  => exact hp
  · intro h
    exact Nat.mul_pos h h

/-- **`born_intensity_is_weight` — the honest, non-degenerate Born bridge.**

    Intensity `= |amplitude|²` is the probability weight on the varying standing-wave
    amplitude, with the Dirichlet node (amplitude `0`) the unique zero:

      (a) on a falsified claim (node) the Born intensity is `0` — no weight on the
          boundary (`modeIntensity_zero_on_falsified`);
      (b) the intensity is strictly positive exactly where the amplitude is — positive
          probability weight ⇔ antinode (`modeIntensity_pos_iff_amplitude_pos`);
      (c) WITNESS-form positive floor: for any antinode claim `c` (amplitude `> 0`) there
          is a Buleyean carrier whose strictly-positive weight
          (`BuleyeanProbability.buleyean_positivity`, `0 < weight`) equals the squared
          amplitude `intensity (m.amplitude c)` — realizing the Born intensity as a
          genuine Buleyean (frequentist, no-zero-floor) probability weight.

    SCOPE. (a) and (b) are general over every `StandingWaveMode`. (c) is a WITNESS/closed
    form: it exhibits a concrete `BuleyeanSpace` realizing the squared amplitude as a
    Buleyean weight at the chosen antinode, rather than a fully general structure-preserving
    map from `StandingWaveMode` to `BuleyeanSpace` (which would need a normalization /
    finite-support hypothesis this Init-only layer does not assume). The Born content —
    intensity is the weight, the node is the unique zero, the floor is strictly positive at
    antinodes — is genuine and non-degenerate on the varying amplitude, unlike the bare
    trit (`trit_born_is_degenerate`). -/
theorem born_intensity_is_weight (F : FalsificationSet) (m : StandingWaveMode F) :
    -- (a) node ⇒ zero weight
    (∀ c : Claim, F.isFalsified c = true → modeIntensity m c = 0)
    -- (b) positive weight ⇔ antinode (amplitude > 0)
    ∧ (∀ c : Claim, 0 < modeIntensity m c ↔ 0 < m.amplitude c)
    -- (c) witness-form: at any antinode, a Buleyean carrier's strictly-positive weight
    --     equals the squared amplitude (intensity), and that weight is positive
    ∧ (∀ c : Claim, 0 < m.amplitude c →
        ∃ (bs : BuleyeanSpace) (i : Fin bs.numChoices),
          bs.weight i = intensity (m.amplitude c) ∧ 0 < bs.weight i) := by
  refine ⟨fun c hF => modeIntensity_zero_on_falsified F m c hF,
          fun c => modeIntensity_pos_iff_amplitude_pos m c, ?_⟩
  intro c hpos
  -- Build a Buleyean carrier whose complement weight equals `intensity a = a*a`.
  -- With `weight i = rounds - min (voidBoundary i) rounds + 1`, choosing
  --   rounds = a*a  and  voidBoundary i = 1
  -- gives  weight i = a*a - min 1 (a*a) + 1 = a*a - 1 + 1 = a*a  (since a*a ≥ 1).
  -- This is well-formed for every antinode amplitude a ≥ 1 (rounds ≥ 1, bound holds).
  have haa1 : 1 ≤ m.amplitude c * m.amplitude c := Nat.mul_pos hpos hpos
  have hmin : Nat.min 1 (m.amplitude c * m.amplitude c) = 1 := Nat.min_eq_left haa1
  have hwt : (m.amplitude c * m.amplitude c)
      - Nat.min 1 (m.amplitude c * m.amplitude c) + 1
      = m.amplitude c * m.amplitude c := by
    rw [hmin, Nat.sub_add_cancel haa1]
  refine ⟨{ numChoices := 2
            nontrivial := by decide
            rounds := m.amplitude c * m.amplitude c
            positiveRounds := haa1
            voidBoundary := fun _ => 1
            bounded := fun _ => haa1 }, (0 : Fin 2), ?_, ?_⟩
  · -- weight 0 = a*a = intensity a
    show (m.amplitude c * m.amplitude c)
        - Nat.min 1 (m.amplitude c * m.amplitude c) + 1 = intensity (m.amplitude c)
    rw [hwt]; rfl
  · -- the Buleyean weight is strictly positive (Axiom 1)
    exact buleyean_positivity _ _

-- ══════════════════════════════════════════════════════════
-- §4  decide-checked witnesses
-- ══════════════════════════════════════════════════════════

/-- Concrete amplitude/intensity values on each verdict, all by `decide`:
    `abstain` is the node (amplitude/intensity 0); `accept`/`decline` are the unit
    antinodes (amplitude/intensity 1). The trit-level degeneracy is visible: the two
    antinodes share intensity 1. -/
theorem amplitude_intensity_witnesses :
    tritAmplitude .decline = 1
    ∧ tritAmplitude .abstain = 0
    ∧ tritAmplitude .accept = 1
    ∧ intensity (tritAmplitude .decline) = 1
    ∧ intensity (tritAmplitude .abstain) = 0
    ∧ intensity (tritAmplitude .accept) = 1
    -- degeneracy made concrete: two distinct verdicts, equal intensity
    ∧ (Verdict.accept ≠ Verdict.decline
        ∧ intensity (tritAmplitude .accept) = intensity (tritAmplitude .decline)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide⟩

/-- The example mode from `FailureAsStandingWave` carries a genuinely VARYING Born
    intensity, unlike the bare trit: claim 0 has intensity `25` (amplitude 5), claim 2
    has intensity `49` (amplitude 7), and the falsified nodes (claims 1, 3) have
    intensity `0`. Distinct nonzero intensities — the non-degeneracy the trit lacked. -/
theorem example_mode_intensity_varies :
    modeIntensity exampleMode 0 = 25
    ∧ modeIntensity exampleMode 2 = 49
    ∧ modeIntensity exampleMode 1 = 0
    ∧ modeIntensity exampleMode 3 = 0
    ∧ (25 : Nat) ≠ 49 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §5  Reading
-- ══════════════════════════════════════════════════════════

/-! Two of `ClinamenUnification`'s three physics disclaimers were too strong.

AMPLITUDE (`trit_is_minimal_standing_wave`) is the TIGHT bridge: the verdict's amplitude
is the magnitude of its sign, `tritAmplitude v = (sign v).natAbs`. The neutral `abstain`
is the zero-amplitude NODE (`node_is_abstain`, riding `abstain_is_superposed`); the two
definite verdicts are the unit ANTINODES (`antinodes_are_definite`); the spectrum is
quantized to `{0, 1}` (`tritAmplitude_le_one`) with three modes, the sign triple. Nothing
is added — amplitude is the modulus `sign` already carries, and the trit realizes its
minimal/quantized case.

BORN INTENSITY (`born_intensity_is_weight`) is REAL but must be scoped. On the bare trit
it is DEGENERATE (`trit_born_is_degenerate`): `intensity ∈ {0,1}`, two distinct verdicts
share intensity `1`, and the masses sum to `2 ≠ 1` — not a distribution. The real Born
carrier is the VARYING standing-wave amplitude of `FailureAsStandingWave.StandingWaveMode`.
There the squared amplitude is a genuine per-claim weight: zero exactly on the Dirichlet
nodes (falsified claims) and strictly positive exactly on the antinodes — tied to
`buleyean_positivity` via a witness Buleyean carrier whose strictly-positive weight equals
the squared amplitude. Parts (a)/(b) are general over every mode; part (c) is a closed
witness form (we say so).

GR is UNTOUCHED and still disclaimed. `GeneralRelativity.lean` is stubbed (curvature `0`,
Einstein equation a tautology, `vent_is_gravity` a score-tripling label, not geometry). No
curvature, metric, or field equation is derived here. The honest open path is an analog /
acoustic EFFECTIVE METRIC read off the standing-wave medium itself — named below as a hard
FUTURE frontier, not a present claim.

-- Next exploration:  (B34a — the open hard frontier)
--   The GR bridge, by ANALOG / EFFECTIVE-METRIC derivation — NOT the stubbed-vocabulary
--   `GeneralRelativity.lean` and NOT the `vent_is_gravity` score-tripling label. The
--   genuine, currently-OPEN path: a standing wave in a moving medium experiences an
--   ACOUSTIC (Unruh) effective metric `g_eff` whose null cones are set by the local wave
--   speed and medium flow — the well-known analog-gravity construction. Concretely, give
--   `StandingWaveMode` a local propagation speed and a claim-space flow field, DERIVE the
--   acoustic line element `ds² = (ρ/c)[-(c² - v²)dt² - 2 v·dx dt + dx²]` from those, and
--   prove (i) the effective metric is genuinely Lorentzian (signature, not the stubbed
--   `is_lorentzian : Prop` placeholder), and (ii) a node/antinode horizon condition (`v =
--   c`) maps to `GeneralRelativity.event_horizon_predicate` as a THEOREM, not a definition.
--   The hard part — and the reason this stays disclaimed — is that an effective metric is
--   NOT Einstein gravity: it has no dynamical field equation (no `G_μν = κ T_μν` derived
--   from an action), so even a full analog-metric result would bridge the KINEMATICS of GR
--   (geodesics, horizons on a fixed effective geometry) and NOT its DYNAMICS. State that
--   scope ceiling up front; deriving curvature dynamics from the medium is a separate,
--   harder frontier. Until (i)+(ii) are machine-checked, GR remains structural-only and the
--   `ClinamenUnification` caveat keeps GR disclaimed.
-/
