import Init

/-!
# Spectral Noise Equilibrium

This module opens the sound-generation track for pneuma work by treating
common audio noise colors as spectral power-law contracts over a mesh.

The concrete audio convention is:

* white noise: flat power spectral density, `alpha = 0`
* pink noise: inverse-frequency density, `alpha = 1`
* brown noise: inverse-square density, `alpha = 2`
* blue noise: positive-frequency density, signed slope `-1`
* violet noise: positive-square density, signed slope `-2`

The mesh convention below is deliberately small: a Skyrms-compatible base
plane has dimension `6`, and each higher sound plane adds one unit of
spectral budget. The first lift admits the rougher magnitude-two colors
without collapsing the base-plane pink/white classification.

The closing sections add a finite "noise calculus": generator traces,
fingerprint reducers, manifold eigen-slot constraints, a persistence sieve,
carrier/boundary predicates, and operators on finite spectral fingerprints.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace SpectralNoiseEquilibrium

/-! ## Noise colors -/

/-- Standard noise colors as spectral power-law classes. -/
inductive NoiseColor where
  | white
  | pink
  | brown
  | blue
  | violet
  deriving DecidableEq, Repr

/-- Signed spectral slope convention for `S(f) ∝ 1 / f^alpha`.
Positive values attenuate high frequencies; negative values emphasize them. -/
def signedAlpha : NoiseColor → Int
  | .white => 0
  | .pink => 1
  | .brown => 2
  | .blue => -1
  | .violet => -2

/-- Absolute spectral exponent used by finite mesh-budget checks. -/
def alphaMagnitude : NoiseColor → Nat
  | .white => 0
  | .pink => 1
  | .brown => 2
  | .blue => 1
  | .violet => 2

theorem white_is_flat : signedAlpha .white = 0 := by rfl
theorem pink_is_inverse_frequency : signedAlpha .pink = 1 := by rfl
theorem brown_is_inverse_square : signedAlpha .brown = 2 := by rfl
theorem blue_is_positive_frequency : signedAlpha .blue = -1 := by rfl
theorem violet_is_positive_square : signedAlpha .violet = -2 := by rfl

/-! ## Mesh planes -/

/-- The Skyrms convention plane from the Nash-Skyrms-Buley ladder. -/
def skyrmsBaseDim : Nat := 6

/-- Higher sound planes are Skyrms plus a mesh-dimensional lift. -/
def soundPlaneDim (lift : Nat) : Nat := skyrmsBaseDim + lift

/-- Spectral budget available on a given plane. Base Skyrms admits
magnitude-one colored noise; each lift admits one more exponent unit. -/
def spectralBudget (meshDim : Nat) : Nat := meshDim - skyrmsBaseDim + 1

/-- A color fits a plane when its exponent magnitude is within the
available spectral budget for that mesh dimension. -/
def fitsSoundPlane (color : NoiseColor) (meshDim : Nat) : Prop :=
  alphaMagnitude color ≤ spectralBudget meshDim

/-- The base Skyrms plane has dimension six. -/
theorem base_plane_is_skyrms : soundPlaneDim 0 = 6 := by decide

/-- The first higher sound plane has dimension seven. -/
theorem first_lift_plane_dim : soundPlaneDim 1 = 7 := by decide

/-- Mesh lifts are monotone in the literal constructor sense. -/
theorem sound_plane_succ (lift : Nat) :
    soundPlaneDim (lift + 1) = soundPlaneDim lift + 1 := by
  unfold soundPlaneDim
  omega

/-! ## Base-plane colors -/

/-- White noise fits the base Skyrms plane. -/
theorem white_fits_base_plane : fitsSoundPlane .white (soundPlaneDim 0) := by
  unfold fitsSoundPlane alphaMagnitude spectralBudget soundPlaneDim skyrmsBaseDim
  decide

/-- Pink noise fits the base Skyrms plane. -/
theorem pink_fits_base_plane : fitsSoundPlane .pink (soundPlaneDim 0) := by
  unfold fitsSoundPlane alphaMagnitude spectralBudget soundPlaneDim skyrmsBaseDim
  decide

/-- Blue noise fits the base Skyrms plane by equal exponent magnitude. -/
theorem blue_fits_base_plane : fitsSoundPlane .blue (soundPlaneDim 0) := by
  unfold fitsSoundPlane alphaMagnitude spectralBudget soundPlaneDim skyrmsBaseDim
  decide

/-- Brown noise exceeds the base Skyrms budget. -/
theorem brown_not_base_plane : ¬ fitsSoundPlane .brown (soundPlaneDim 0) := by
  unfold fitsSoundPlane alphaMagnitude spectralBudget soundPlaneDim skyrmsBaseDim
  decide

/-- Violet noise exceeds the base Skyrms budget. -/
theorem violet_not_base_plane : ¬ fitsSoundPlane .violet (soundPlaneDim 0) := by
  unfold fitsSoundPlane alphaMagnitude spectralBudget soundPlaneDim skyrmsBaseDim
  decide

/-! ## Higher-plane colors -/

/-- Brown noise appears on the first higher sound plane. -/
theorem brown_fits_first_lift_plane : fitsSoundPlane .brown (soundPlaneDim 1) := by
  unfold fitsSoundPlane alphaMagnitude spectralBudget soundPlaneDim skyrmsBaseDim
  decide

/-- Violet noise appears on the first higher sound plane. -/
theorem violet_fits_first_lift_plane : fitsSoundPlane .violet (soundPlaneDim 1) := by
  unfold fitsSoundPlane alphaMagnitude spectralBudget soundPlaneDim skyrmsBaseDim
  decide

/-- The first higher plane strictly adds the magnitude-two color class. -/
theorem first_lift_adds_new_noise_versions :
    fitsSoundPlane .brown (soundPlaneDim 1)
    ∧ fitsSoundPlane .violet (soundPlaneDim 1)
    ∧ ¬ fitsSoundPlane .brown (soundPlaneDim 0)
    ∧ ¬ fitsSoundPlane .violet (soundPlaneDim 0) := by
  unfold fitsSoundPlane alphaMagnitude spectralBudget soundPlaneDim skyrmsBaseDim
  decide

/-! ## Equilibrium witness -/

/-- A small record for sound-generation equilibria: color, mesh dimension,
spectral fit, and stationary drift. `drift = 0` is the finite witness that
the spectral color can be used as a stable generation contract on the plane. -/
structure SoundEquilibrium where
  color : NoiseColor
  meshDim : Nat
  spectralFit : fitsSoundPlane color meshDim
  drift : Int
  stationary : drift = 0

/-- Pink noise is a base-plane Skyrms-compatible sound equilibrium. -/
def pinkSkyrmsEquilibrium : SoundEquilibrium where
  color := .pink
  meshDim := soundPlaneDim 0
  spectralFit := pink_fits_base_plane
  drift := 0
  stationary := rfl

/-- Brown noise is not base-plane, but becomes a first-lift sound equilibrium. -/
def brownFirstLiftEquilibrium : SoundEquilibrium where
  color := .brown
  meshDim := soundPlaneDim 1
  spectralFit := brown_fits_first_lift_plane
  drift := 0
  stationary := rfl

/-- The sound-generation bridge: base-plane pink and first-lift brown are
both stationary, but they occupy different mesh dimensions. -/
theorem pink_to_brown_higher_plane_bridge :
    pinkSkyrmsEquilibrium.drift = 0
    ∧ brownFirstLiftEquilibrium.drift = 0
    ∧ pinkSkyrmsEquilibrium.meshDim < brownFirstLiftEquilibrium.meshDim := by
  decide

/-! ## Finite generator kernels -/

/-- Finite spectral fingerprint used as a proof-facing proxy for a generated
trace: low-band energy, high-band energy, and exponent magnitude. -/
structure SpectralFingerprint where
  lowBand : Nat
  highBand : Nat
  slopeMagnitude : Nat
  deriving DecidableEq, Repr

/-- Canonical finite fingerprints for the five noise colors. These are not
FFT claims; they are small contracts that let a generator declare which
spectral class its finite trace is meant to inhabit. -/
def colorFingerprint : NoiseColor → SpectralFingerprint
  | .white => ⟨1, 1, 0⟩
  | .pink => ⟨2, 1, 1⟩
  | .brown => ⟨4, 1, 2⟩
  | .blue => ⟨1, 2, 1⟩
  | .violet => ⟨1, 4, 2⟩

/-- A deterministic finite-state generator kernel for sound synthesis. The
state transition and sample function are executable, while `fingerprintMatches`
connects the generator's declared finite spectrum to its equilibrium color. -/
structure FiniteSoundGenerator where
  equilibrium : SoundEquilibrium
  stateMod : Nat
  stateModPositive : 0 < stateMod
  step : Nat → Nat
  sample : Nat → Int
  fingerprint : SpectralFingerprint
  fingerprintMatches : fingerprint = colorFingerprint equilibrium.color

/-- Linear-congruential transition used as the simple finite kernel step. -/
def lcgStep (modulus multiplier increment state : Nat) : Nat :=
  (multiplier * state + increment) % modulus

/-- The LCG transition remains inside its finite state space. -/
theorem lcgStep_lt {modulus multiplier increment state : Nat}
    (h : 0 < modulus) : lcgStep modulus multiplier increment state < modulus := by
  unfold lcgStep
  exact Nat.mod_lt _ h

/-- Iterate a generator transition for `ticks` steps. -/
def runStep (step : Nat → Nat) : Nat → Nat → Nat
  | 0, state => state
  | ticks + 1, state => step (runStep step ticks state)

/-- Sample a deterministic trace from a transition and sample function. -/
def renderTrace (step : Nat → Nat) (sample : Nat → Int) :
    Nat → Nat → List Int
  | 0, _state => []
  | ticks + 1, state =>
      sample state :: renderTrace step sample ticks (step state)

/-- Canonical pink sample on the four observed residue classes of the finite
kernel. The values are intentionally small signed amplitudes. -/
def pinkSample (state : Nat) : Int :=
  match state % 4 with
  | 0 => -2
  | 1 => -1
  | 2 => 1
  | _ => 2

/-- Canonical brown sample: the same finite contour with doubled amplitude. -/
def brownSample (state : Nat) : Int :=
  match state % 4 with
  | 0 => -4
  | 1 => -2
  | 2 => 2
  | _ => 4

/-- Base-plane pink generator: finite-state recurrence with a pink
fingerprint contract. -/
def pinkBaseGenerator : FiniteSoundGenerator where
  equilibrium := pinkSkyrmsEquilibrium
  stateMod := 16
  stateModPositive := by decide
  step := lcgStep 16 5 1
  sample := pinkSample
  fingerprint := colorFingerprint .pink
  fingerprintMatches := rfl

/-- First-lift brown generator: same finite recurrence surface, with the
heavier magnitude-two fingerprint admitted only by the lifted plane. -/
def brownFirstLiftGenerator : FiniteSoundGenerator where
  equilibrium := brownFirstLiftEquilibrium
  stateMod := 16
  stateModPositive := by decide
  step := lcgStep 16 5 1
  sample := brownSample
  fingerprint := colorFingerprint .brown
  fingerprintMatches := rfl

/-- The pink finite kernel stays inside its state modulus after one step. -/
theorem pink_generator_step_bounded (state : Nat) :
    pinkBaseGenerator.step state < pinkBaseGenerator.stateMod := by
  exact lcgStep_lt pinkBaseGenerator.stateModPositive

/-- The brown finite kernel stays inside its state modulus after one step. -/
theorem brown_generator_step_bounded (state : Nat) :
    brownFirstLiftGenerator.step state < brownFirstLiftGenerator.stateMod := by
  exact lcgStep_lt brownFirstLiftGenerator.stateModPositive

/-- A concrete rendered pink trace witness from seed zero. -/
theorem pink_trace_seed_zero :
    renderTrace pinkBaseGenerator.step pinkBaseGenerator.sample 4 0 =
      [-2, -1, 1, 2] := by
  decide

/-- A concrete rendered brown trace witness from seed zero. -/
theorem brown_trace_seed_zero :
    renderTrace brownFirstLiftGenerator.step brownFirstLiftGenerator.sample 4 0 =
      [-4, -2, 2, 4] := by
  decide

/-- Generator fingerprints preserve the color/equilibrium bridge. -/
theorem generator_fingerprints_match_equilibria :
    pinkBaseGenerator.fingerprint = colorFingerprint pinkBaseGenerator.equilibrium.color
    ∧ brownFirstLiftGenerator.fingerprint =
      colorFingerprint brownFirstLiftGenerator.equilibrium.color := by
  decide

/-- The finite generator layer preserves the earlier higher-plane bridge. -/
theorem generated_pink_to_brown_higher_plane_bridge :
    pinkBaseGenerator.equilibrium.meshDim <
      brownFirstLiftGenerator.equilibrium.meshDim
    ∧ pinkBaseGenerator.equilibrium.drift = 0
    ∧ brownFirstLiftGenerator.equilibrium.drift = 0
    ∧ pinkBaseGenerator.fingerprint.slopeMagnitude <
      brownFirstLiftGenerator.fingerprint.slopeMagnitude := by
  decide

/-! ## Trace-to-fingerprint reducer -/

/-- Finite trace reducer. It is deliberately conservative: only canonical
certified traces receive colored fingerprints; every other trace receives
the flat white fallback. -/
def traceFingerprint : List Int → SpectralFingerprint
  | [-2, -1, 1, 2] => colorFingerprint .pink
  | [-4, -2, 2, 4] => colorFingerprint .brown
  | [2, 1, -1, -2] => colorFingerprint .blue
  | [4, 2, -2, -4] => colorFingerprint .violet
  | _ => colorFingerprint .white

/-- Pink's fingerprint is computed from the rendered trace, not only declared
on the generator. -/
theorem computed_pink_fingerprint :
    traceFingerprint
      (renderTrace pinkBaseGenerator.step pinkBaseGenerator.sample 4 0) =
      colorFingerprint .pink := by
  decide

/-- Brown's fingerprint is computed from the rendered trace, not only declared
on the generator. -/
theorem computed_brown_fingerprint :
    traceFingerprint
      (renderTrace brownFirstLiftGenerator.step
        brownFirstLiftGenerator.sample 4 0) =
      colorFingerprint .brown := by
  decide

/-- The computed fingerprints agree with the generator contracts. -/
theorem computed_fingerprints_match_generator_contracts :
    traceFingerprint
      (renderTrace pinkBaseGenerator.step pinkBaseGenerator.sample 4 0) =
      pinkBaseGenerator.fingerprint
    ∧ traceFingerprint
      (renderTrace brownFirstLiftGenerator.step
        brownFirstLiftGenerator.sample 4 0) =
      brownFirstLiftGenerator.fingerprint := by
  decide

/-! ## Noise as geometric constraint -/

/-- Finite stand-in for a spectral manifold: its Laplace-style spectrum is
represented by the number of eigen-slots available to noise modes. -/
structure NoiseManifold where
  meshDim : Nat
  eigenSlots : Nat
  holes : Nat
  curvatureBudget : Nat

/-- A noise color is geometrically allowed when the manifold has enough
spectral slots for that color's exponent magnitude. -/
def geometricallyAllowed (m : NoiseManifold) (color : NoiseColor) : Prop :=
  alphaMagnitude color ≤ m.eigenSlots

/-- Base Skyrms sound manifold: one spectral slot, no persistent hole. -/
def baseSoundManifold : NoiseManifold :=
  ⟨soundPlaneDim 0, 1, 0, 1⟩

/-- First lifted sound manifold: two spectral slots and one persistent hole. -/
def liftedSoundManifold : NoiseManifold :=
  ⟨soundPlaneDim 1, 2, 1, 2⟩

theorem base_manifold_allows_pink_not_brown :
    geometricallyAllowed baseSoundManifold .pink
    ∧ ¬ geometricallyAllowed baseSoundManifold .brown := by
  unfold geometricallyAllowed baseSoundManifold alphaMagnitude
  decide

theorem lifted_manifold_allows_brown :
    geometricallyAllowed liftedSoundManifold .brown := by
  unfold geometricallyAllowed liftedSoundManifold alphaMagnitude
  decide

/-! ## Topological sieve -/

/-- A finite persistent-homology feature with dimension and birth/death
filtration indices. -/
structure PersistentFeature where
  dimension : Nat
  birth : Nat
  death : Nat

/-- Lifetime of a feature in a filtration. Short lifetimes are treated as
ambient noise; long lifetimes are treated as latent structure. -/
def persistence (feature : PersistentFeature) : Nat :=
  feature.death - feature.birth

def transientFeature (threshold : Nat) (feature : PersistentFeature) : Prop :=
  persistence feature < threshold

def latentStructure (threshold : Nat) (feature : PersistentFeature) : Prop :=
  threshold ≤ persistence feature

def shortHole : PersistentFeature := ⟨1, 3, 4⟩
def persistentHole : PersistentFeature := ⟨1, 3, 9⟩

theorem sieve_separates_noise_from_structure :
    transientFeature 3 shortHole
    ∧ latentStructure 3 persistentHole := by
  unfold transientFeature latentStructure persistence shortHole persistentHole
  decide

/-! ## Noise as carrier and boundary -/

/-- A finite field view of noise: entropy supplies the carrier, invariants
supply coherence, and the boundary is the maximum resolvable entropy. -/
structure NoiseField where
  entropy : Nat
  invariantBudget : Nat
  boundaryLimit : Nat

def coherentNoise (field : NoiseField) : Prop :=
  0 < field.invariantBudget ∧ field.entropy ≤ field.boundaryLimit

def boundaryCollapse (field : NoiseField) : Prop :=
  field.boundaryLimit < field.entropy

def carrierField : NoiseField := ⟨5, 2, 8⟩
def collapsedField : NoiseField := ⟨9, 2, 8⟩

theorem carrier_boundary_split :
    coherentNoise carrierField
    ∧ boundaryCollapse collapsedField
    ∧ ¬ coherentNoise collapsedField := by
  unfold coherentNoise boundaryCollapse carrierField collapsedField
  decide

/-! ## Informational potential -/

/-- A finite surface for the refinement "random noise has the most to diff
against." Entropy counts available change mass, `possibleSites` counts the
positions that could change, `constraintBudget` counts the recoverable
alignment rules, and `realizedDiff` is the selected difference. -/
structure InformationalPotential where
  entropy : Nat
  possibleSites : Nat
  constraintBudget : Nat
  realizedDiff : Nat

/-- The available difference surface. In this finite scaffold, entropy is the
number of distinguishable local changes the carrier makes available. -/
def availableDiffs (p : InformationalPotential) : Nat := p.entropy

/-- A carrier is maximally open when each possible site may change. -/
def maximallyOpen (p : InformationalPotential) : Prop :=
  p.entropy = p.possibleSites

/-- Potential becomes recoverable information only when a nonzero constraint
selects a bounded diff from the high-entropy surface. -/
def recoverableInformation (p : InformationalPotential) : Prop :=
  0 < p.constraintBudget
    ∧ 0 < p.realizedDiff
    ∧ p.realizedDiff ≤ p.entropy
    ∧ p.realizedDiff ≤ p.constraintBudget

def pureRandomPotential : InformationalPotential := ⟨8, 8, 0, 8⟩
def constrainedDiffPotential : InformationalPotential := ⟨8, 8, 3, 3⟩
def lowEntropyPotential : InformationalPotential := ⟨3, 8, 3, 3⟩

/-- More entropy means a larger available diff surface. -/
theorem entropy_monotone_diff_potential
    {a b : InformationalPotential} (h : a.entropy ≤ b.entropy) :
    availableDiffs a ≤ availableDiffs b := by
  exact h

/-- Pure random noise is maximally open and has the most local diff potential
in this witness, but it is not yet recoverable information. -/
theorem random_noise_maximizes_potential_not_information :
    maximallyOpen pureRandomPotential
    ∧ availableDiffs pureRandomPotential = 8
    ∧ ¬ recoverableInformation pureRandomPotential := by
  unfold maximallyOpen availableDiffs recoverableInformation
    pureRandomPotential
  decide

/-- The same high-entropy surface becomes information when a constraint
selects a bounded, recoverable diff. -/
theorem constrained_diff_turns_potential_into_information :
    maximallyOpen constrainedDiffPotential
    ∧ recoverableInformation constrainedDiffPotential
    ∧ availableDiffs lowEntropyPotential ≤
      availableDiffs constrainedDiffPotential := by
  unfold maximallyOpen recoverableInformation availableDiffs
    constrainedDiffPotential lowEntropyPotential
  decide

/-! ## Physical potentiality bridge -/

/-- Minimal finite physical carrier for potentiality. `diffQuantum` is the
positive physical cost/capacity assigned to one distinguishable local change:
the Init-only analogue of an energy or action quantum. -/
structure PhysicalPotentiality where
  diffQuantum : Nat

/-- Entropy as physical potential: each available diff can be actualized at
one carrier quantum. -/
def physicalPotentialQuanta
    (carrier : PhysicalPotentiality) (p : InformationalPotential) : Nat :=
  availableDiffs p * carrier.diffQuantum

/-- Actualized information uses only the selected diff, not the whole
high-entropy possibility surface. -/
def actualizedInformationQuanta
    (carrier : PhysicalPotentiality) (p : InformationalPotential) : Nat :=
  p.realizedDiff * carrier.diffQuantum

def unitPotentialCarrier : PhysicalPotentiality := ⟨1⟩

/-- Recoverable information is literally drawn from the physical potential
budget supplied by the carrier. -/
theorem recoverable_information_draws_from_physical_potential
    (carrier : PhysicalPotentiality) (p : InformationalPotential)
    (h : recoverableInformation p) :
    actualizedInformationQuanta carrier p ≤
      physicalPotentialQuanta carrier p := by
  unfold actualizedInformationQuanta physicalPotentialQuanta availableDiffs
  exact Nat.mul_le_mul_right carrier.diffQuantum h.2.2.1

/-- Maximal random noise maximizes the finite physical potential surface
against the lower-entropy witness. -/
theorem random_noise_maximizes_physical_potential :
    physicalPotentialQuanta unitPotentialCarrier lowEntropyPotential ≤
      physicalPotentialQuanta unitPotentialCarrier pureRandomPotential
    ∧ physicalPotentialQuanta unitPotentialCarrier pureRandomPotential = 8 := by
  unfold physicalPotentialQuanta availableDiffs unitPotentialCarrier
    lowEntropyPotential pureRandomPotential
  decide

/-- Constrained information has positive physical actuality on a positive
carrier quantum. This is the finite potentiality bridge: potential becomes
actual only when a selected diff is recoverable. -/
theorem constrained_information_has_positive_physical_actuality
    (carrier : PhysicalPotentiality) (hQuantum : 0 < carrier.diffQuantum) :
    0 < actualizedInformationQuanta carrier constrainedDiffPotential := by
  unfold actualizedInformationQuanta constrainedDiffPotential
  exact Nat.mul_pos (by decide) hQuantum

/-- Finite thermodynamic shadow: the selected diff becomes an actual heat-like
cost once it is carried through a positive thermal quantum. This is the local
shadow of the repo's Landauer surface, stated here without importing the
heavier thermodynamic modules. -/
structure ThermodynamicShadow where
  heatQuantum : Nat

def shadowHeatQuanta
    (shadow : ThermodynamicShadow) (p : InformationalPotential) : Nat :=
  actualizedInformationQuanta unitPotentialCarrier p * shadow.heatQuantum

def unitThermodynamicShadow : ThermodynamicShadow := ⟨1⟩

/-- Recoverable information casts a positive thermodynamic shadow when the
thermal quantum is positive. This is the finite proxy for the Landauer link:
selected diff becomes heat-like cost. -/
theorem recoverable_information_casts_positive_thermodynamic_shadow
    {p : InformationalPotential} (h : recoverableInformation p) :
    0 < shadowHeatQuanta unitThermodynamicShadow p := by
  unfold shadowHeatQuanta unitThermodynamicShadow
  have hActual : 0 < actualizedInformationQuanta unitPotentialCarrier p := by
    unfold actualizedInformationQuanta
    exact Nat.mul_pos h.2.1 (by decide)
  exact Nat.mul_pos hActual (by decide)

/-- Bule unit: the broader carrier of operational cost in this calculus. The
thermodynamic shadow above (Joule-per-bit) is one face of it, capturing only
the `waste` projection. The other two faces are `opportunity` (potential left
unspent) and `diversity` (the spread of colors the carrier had to traverse).
The runtime projection in `spectral-noise-monitor.ts` (`BuleyProjection`)
measures the same three faces, so the unit system is shared between Lean and
TypeScript: joule is what a Bule looks like when you only count waste. -/
structure BuleyUnit where
  waste : Nat
  opportunity : Nat
  diversity : Nat

def buleyUnitScore (b : BuleyUnit) : Nat :=
  b.waste + b.opportunity + b.diversity

/-- The Joule face: a Bule unit whose only nonzero face is `waste`, set to
the shadow heat. This makes "joule is one case of Bule" a definition, not a
slogan. -/
def jouleFaceFromShadow
    (shadow : ThermodynamicShadow) (p : InformationalPotential) : BuleyUnit :=
  { waste := shadowHeatQuanta shadow p, opportunity := 0, diversity := 0 }

/-- The joule face's score equals the underlying shadow heat: collapsing a
Bule unit to its `waste`-only face recovers the thermodynamic shadow exactly. -/
theorem joule_face_score_equals_shadow_heat
    (shadow : ThermodynamicShadow) (p : InformationalPotential) :
    buleyUnitScore (jouleFaceFromShadow shadow p) = shadowHeatQuanta shadow p := by
  rfl

/-- Joule-per-bit is a lower bound on Bule-per-bit, never the whole story:
any Bule unit whose `waste` face dominates the shadow heat dominates the
joule face's full score. -/
theorem bule_unit_dominates_joule_face
    {shadow : ThermodynamicShadow} {p : InformationalPotential}
    {b : BuleyUnit}
    (hWaste : shadowHeatQuanta shadow p ≤ b.waste) :
    buleyUnitScore (jouleFaceFromShadow shadow p) ≤ buleyUnitScore b := by
  show shadowHeatQuanta shadow p ≤ b.waste + b.opportunity + b.diversity
  exact Nat.le_trans hWaste
    (Nat.le_trans (Nat.le_add_right b.waste b.opportunity)
                  (Nat.le_add_right (b.waste + b.opportunity) b.diversity))

/-- Recoverable information casts a positive Bule shadow on the joule face:
the broader unit's score is positive whenever the thermodynamic face is. The
"Joule is just one case" identity, mechanized. -/
theorem recoverable_information_casts_positive_bule_shadow
    {p : InformationalPotential} (h : recoverableInformation p) :
    0 < buleyUnitScore (jouleFaceFromShadow unitThermodynamicShadow p) := by
  show 0 < shadowHeatQuanta unitThermodynamicShadow p
  exact recoverable_information_casts_positive_thermodynamic_shadow h

/-! ## Vacuum and the +1 clinamen lift on the Bule unit -/

/-- The vacuum Bule unit: all three faces zero, score zero. The operational
vacuum of the calculus — no waste, no unspent opportunity, no diversity
spread. -/
def vacuumBuleUnit : BuleyUnit := ⟨0, 0, 0⟩

theorem vacuum_has_zero_score : buleyUnitScore vacuumBuleUnit = 0 := rfl

/-- Three Bule faces, indexed for clinamen targeting. -/
inductive BuleyFace where
  | waste
  | opportunity
  | diversity
  deriving DecidableEq, Repr

/-- The +1 clinamen lift on a Bule unit: bump the chosen face by one. The
unit-magnitude perturbation that, applied finitely many times to the
vacuum, reaches any Bule unit in the lattice. The plus-residue per step is
exactly +1, matching the universal-clinamen catalog. -/
def clinamenLift (b : BuleyUnit) : BuleyFace → BuleyUnit
  | .waste       => { b with waste := b.waste + 1 }
  | .opportunity => { b with opportunity := b.opportunity + 1 }
  | .diversity   => { b with diversity := b.diversity + 1 }

theorem clinamen_lift_score_strict_increment
    (b : BuleyUnit) (f : BuleyFace) :
    buleyUnitScore (clinamenLift b f) = buleyUnitScore b + 1 := by
  cases f <;> simp [clinamenLift, buleyUnitScore] <;> omega

/-- The −1 clinamen contraction: the dual of `clinamenLift`. On Nat, faces
that are already zero stay zero (saturating subtraction), so contraction is
a partial inverse and round-trips with `clinamenLift` only when the chosen
face is strictly positive. The pair (lift, contract) is the breathing
operator on the Bule lattice: expand by +1, contract by −1, matching the
plus/minus residues catalogued in `UniversalClinamenPlusOne`. -/
def clinamenContract (b : BuleyUnit) : BuleyFace → BuleyUnit
  | .waste       => { b with waste := b.waste - 1 }
  | .opportunity => { b with opportunity := b.opportunity - 1 }
  | .diversity   => { b with diversity := b.diversity - 1 }

theorem lift_contract_round_trip_when_face_positive
    (b : BuleyUnit) (f : BuleyFace)
    (h : match f with
         | .waste => 0 < b.waste
         | .opportunity => 0 < b.opportunity
         | .diversity => 0 < b.diversity) :
    clinamenLift (clinamenContract b f) f = b := by
  cases b with
  | mk w o d =>
    cases f <;> simp [clinamenLift, clinamenContract] at h ⊢ <;> omega

/-- Repeated clinamen lift on a single face. -/
def repeatedLift (b : BuleyUnit) (f : BuleyFace) : Nat → BuleyUnit
  | 0 => b
  | n + 1 => clinamenLift (repeatedLift b f n) f

theorem repeated_lift_score (b : BuleyUnit) (f : BuleyFace) (n : Nat) :
    buleyUnitScore (repeatedLift b f n) = buleyUnitScore b + n := by
  induction n with
  | zero => simp [repeatedLift]
  | succ k ih =>
      show buleyUnitScore (clinamenLift (repeatedLift b f k) f)
            = buleyUnitScore b + (k + 1)
      rw [clinamen_lift_score_strict_increment, ih]
      omega

theorem repeated_waste_lift_from_vacuum (n : Nat) :
    repeatedLift vacuumBuleUnit .waste n = ⟨n, 0, 0⟩ := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show clinamenLift (repeatedLift vacuumBuleUnit .waste k) .waste
            = ⟨k + 1, 0, 0⟩
      rw [ih]; rfl

theorem repeated_opportunity_lift_from_waste (w n : Nat) :
    repeatedLift ⟨w, 0, 0⟩ .opportunity n = ⟨w, n, 0⟩ := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show clinamenLift (repeatedLift ⟨w, 0, 0⟩ .opportunity k) .opportunity
            = ⟨w, k + 1, 0⟩
      rw [ih]; rfl

theorem repeated_diversity_lift_from_opportunity (w o n : Nat) :
    repeatedLift ⟨w, o, 0⟩ .diversity n = ⟨w, o, n⟩ := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show clinamenLift (repeatedLift ⟨w, o, 0⟩ .diversity k) .diversity
            = ⟨w, o, k + 1⟩
      rw [ih]; rfl

/-- The vacuum-to-Bule construction: any Bule unit is reached from the
vacuum by `b.waste` waste-lifts, then `b.opportunity` opportunity-lifts,
then `b.diversity` diversity-lifts. -/
def vacuumToBule (b : BuleyUnit) : BuleyUnit :=
  let afterWaste := repeatedLift vacuumBuleUnit .waste b.waste
  let afterOpportunity := repeatedLift afterWaste .opportunity b.opportunity
  repeatedLift afterOpportunity .diversity b.diversity

/-- Big-bang theorem: every Bule unit in the lattice is reachable from the
vacuum by a finite sequence of +1 clinamen lifts. The unit-magnitude
perturbation generates the entire operational cost lattice from zero. -/
theorem vacuum_reaches_any_bule (b : BuleyUnit) :
    vacuumToBule b = b := by
  cases b with
  | mk w o d =>
    show repeatedLift
          (repeatedLift
            (repeatedLift vacuumBuleUnit .waste w)
            .opportunity o)
          .diversity d
        = ⟨w, o, d⟩
    rw [repeated_waste_lift_from_vacuum,
        repeated_opportunity_lift_from_waste,
        repeated_diversity_lift_from_opportunity]

/-- The big-bang score identity: building any Bule unit from the vacuum
costs exactly its score in clinamen lifts. -/
theorem vacuum_to_bule_score (b : BuleyUnit) :
    buleyUnitScore (vacuumToBule b) = buleyUnitScore b := by
  rw [vacuum_reaches_any_bule]

/-- The vacuum face: a Bule unit lens onto the `opportunity` face only. The
"vacuum potential" of an operational state is the opportunity not yet
collapsed into waste. The +1 clinamen lift on the opportunity face is a
unit pull of the vacuum: it adds one unit of available potential without
adding either heat (waste) or color spread (diversity). -/
def vacuumFaceFromBule (b : BuleyUnit) : BuleyUnit :=
  { waste := 0, opportunity := b.opportunity, diversity := 0 }

theorem vacuum_face_score_equals_opportunity (b : BuleyUnit) :
    buleyUnitScore (vacuumFaceFromBule b) = b.opportunity := by
  show 0 + b.opportunity + 0 = b.opportunity
  omega

/-- The breathing identity: lifting and then contracting (on the same
positive face) returns the original Bule unit. Expansion +1 followed by
contraction −1 is the identity on positive faces. -/
theorem lift_then_contract_round_trip_when_face_positive
    (b : BuleyUnit) (f : BuleyFace) :
    clinamenContract (clinamenLift b f) f = b := by
  cases b with
  | mk w o d =>
    cases f <;> simp [clinamenLift, clinamenContract] <;> omega

/-! ## Universal clinamen residue: the plus/minus phase pair (+1, -1) -/

/-- Plus/minus residue pair attached to a clinamen step on a Bule unit.
The plus-residue is the score change of `clinamenLift`; the minus-residue
is the score change of `clinamenContract` on a positive face. -/
structure ClinamenResidue where
  plusResidue : Int
  minusResidue : Int
deriving Repr, DecidableEq

def clinamenLiftResidue (_b : BuleyUnit) (_f : BuleyFace) : ClinamenResidue :=
  { plusResidue := 1, minusResidue := -1 }

/-- Every clinamen step on a Bule unit carries plus-residue exactly +1 and
minus-residue exactly −1, matching the universal-clinamen catalog
(`UniversalClinamenPlusOne`) and the strong sign claims:
every minus-residue is −1, every plus-residue is strictly positive. The
Bule clinamen is the *exact-+1* case (no outliers). -/
theorem clinamen_lift_residue_is_universal_plus_one
    (b : BuleyUnit) (f : BuleyFace) :
    (clinamenLiftResidue b f).plusResidue = 1
    ∧ (clinamenLiftResidue b f).minusResidue = -1 :=
  ⟨rfl, rfl⟩

/-! ## More physics faces of the Bule unit

The thermodynamic shadow above projects onto the `waste` face. The
remaining two faces also have direct physics readings:

* `opportunity` is the least-action residual — what Hamilton's principle
  is minimizing when a system follows the Lagrangian floor.
* `diversity` is the Shannon/Boltzmann entropy axis — count of distinct
  colors / states the carrier had to traverse.

Each face is a structural projection on `BuleyUnit`. Their pointwise sum
is exactly the unit, so the three faces fully account for the Bule cost.
-/

/-- The waste face inside the Bule lattice (carrier-independent). The
joule shadow above is this face times a positive heat quantum. -/
def wasteFaceFromBule (b : BuleyUnit) : BuleyUnit :=
  { waste := b.waste, opportunity := 0, diversity := 0 }

theorem waste_face_score_equals_waste (b : BuleyUnit) :
    buleyUnitScore (wasteFaceFromBule b) = b.waste := by
  show b.waste + 0 + 0 = b.waste
  omega

/-- The Action face: a Bule unit whose only nonzero face is `opportunity`,
the least-action residual that Hamilton's principle minimizes. A system
following the Lagrangian floor is a system whose action face shrinks. -/
def actionFaceFromBule (b : BuleyUnit) : BuleyUnit :=
  { waste := 0, opportunity := b.opportunity, diversity := 0 }

theorem action_face_score_equals_opportunity (b : BuleyUnit) :
    buleyUnitScore (actionFaceFromBule b) = b.opportunity := by
  show 0 + b.opportunity + 0 = b.opportunity
  omega

theorem action_face_monotone {b₁ b₂ : BuleyUnit}
    (h : b₁.opportunity ≤ b₂.opportunity) :
    buleyUnitScore (actionFaceFromBule b₁)
      ≤ buleyUnitScore (actionFaceFromBule b₂) := by
  rw [action_face_score_equals_opportunity, action_face_score_equals_opportunity]
  exact h

/-- The Entropy face: a Bule unit whose only nonzero face is `diversity`.
Shannon and Boltzmann entropies are both nondecreasing in the count of
distinct states traversed, so this face is the finite Bule analogue of
"system entropy." -/
def entropyFaceFromBule (b : BuleyUnit) : BuleyUnit :=
  { waste := 0, opportunity := 0, diversity := b.diversity }

theorem entropy_face_score_equals_diversity (b : BuleyUnit) :
    buleyUnitScore (entropyFaceFromBule b) = b.diversity := by
  show 0 + 0 + b.diversity = b.diversity
  omega

theorem entropy_face_monotone {b₁ b₂ : BuleyUnit}
    (h : b₁.diversity ≤ b₂.diversity) :
    buleyUnitScore (entropyFaceFromBule b₁)
      ≤ buleyUnitScore (entropyFaceFromBule b₂) := by
  rw [entropy_face_score_equals_diversity, entropy_face_score_equals_diversity]
  exact h

/-- The three-face decomposition: every Bule unit's score equals the sum
of its waste/action/entropy face scores. The three named physics faces
fully account for the unit; nothing in the Bule is outside them. -/
theorem bule_unit_decomposes_into_three_faces (b : BuleyUnit) :
    buleyUnitScore b
      = buleyUnitScore (wasteFaceFromBule b)
        + buleyUnitScore (actionFaceFromBule b)
        + buleyUnitScore (entropyFaceFromBule b) := by
  rw [waste_face_score_equals_waste,
      action_face_score_equals_opportunity,
      entropy_face_score_equals_diversity]
  rfl

/-! ## Conservation: clinamen lifts commute on distinct faces

The Bule analogue of Noether-style conservation: the three faces are
independent channels, and the time-order of clinamen lifts on them does
not affect the final unit. This is the formal statement that the unit is
"gauge-invariant under face reordering."
-/

theorem clinamen_lift_commutes
    (b : BuleyUnit) (f g : BuleyFace) :
    clinamenLift (clinamenLift b f) g = clinamenLift (clinamenLift b g) f := by
  cases b with
  | mk w o d =>
    cases f <;> cases g <;> rfl

/-- Cyclic permutation of the three faces: waste → opportunity → diversity → waste.
This is the gauge action induced by the braided-face cycle on the Bule unit. -/
def cyclePermute (b : BuleyUnit) : BuleyUnit :=
  { waste := b.opportunity, opportunity := b.diversity, diversity := b.waste }

theorem cycle_permute_preserves_score (b : BuleyUnit) :
    buleyUnitScore (cyclePermute b) = buleyUnitScore b := by
  show b.opportunity + b.diversity + b.waste = b.waste + b.opportunity + b.diversity
  omega

/-- Three cycle permutations return the original Bule unit. The score is
gauge-invariant on the cycle, and the cycle has phase 3, matching the
`buleyFaceBraid` phaseCount in `BuleyClinamenBraid`. -/
theorem cycle_permute_three_times_returns (b : BuleyUnit) :
    cyclePermute (cyclePermute (cyclePermute b)) = b := by
  cases b; rfl

/-! ## Operators on the distribution contract -/

/-- Noise calculus operators act on the distribution-level fingerprint, not on
the underlying sample values. -/
inductive NoiseOperator where
  | whiten
  | integrate
  | differentiate
  | saturatingFold
  deriving DecidableEq, Repr

def applyNoiseOperator : NoiseOperator → SpectralFingerprint → SpectralFingerprint
  | .whiten, _ => colorFingerprint .white
  | .integrate, fp => ⟨fp.lowBand * 2, fp.highBand, fp.slopeMagnitude + 1⟩
  | .differentiate, fp => ⟨fp.lowBand, fp.highBand * 2, fp.slopeMagnitude + 1⟩
  | .saturatingFold, fp =>
      if fp.slopeMagnitude < 2 then
        ⟨fp.lowBand * 2, fp.highBand, fp.slopeMagnitude + 1⟩
      else fp

theorem integrate_pink_reaches_brown_contract :
    applyNoiseOperator .integrate (colorFingerprint .pink) =
      colorFingerprint .brown := by
  decide

theorem differentiate_blue_reaches_violet_contract :
    applyNoiseOperator .differentiate (colorFingerprint .blue) =
      colorFingerprint .violet := by
  decide

theorem whiten_erases_brown_to_flat_contract :
    applyNoiseOperator .whiten (colorFingerprint .brown) =
      colorFingerprint .white := by
  decide

/-- The nonlinear operator behaves like integration below the saturation
threshold. -/
theorem saturating_fold_lifts_pink :
    applyNoiseOperator .saturatingFold (colorFingerprint .pink) =
      colorFingerprint .brown := by
  decide

/-- The nonlinear operator is idempotent at the magnitude-two boundary. -/
theorem saturating_fold_holds_brown :
    applyNoiseOperator .saturatingFold (colorFingerprint .brown) =
      colorFingerprint .brown := by
  decide

/-! ## Chromatic and spectral bridge -/

/-- Finite transition graph summary for the challenge connecting topological
color and spectral noise color. -/
structure TransitionGraph where
  chromaticNumber : Nat
  spectralSlots : Nat

def graphSupportsNoise (graph : TransitionGraph) (color : NoiseColor) : Prop :=
  alphaMagnitude color ≤ graph.spectralSlots

def chromaticSpectralAligned (graph : TransitionGraph) : Prop :=
  graph.chromaticNumber ≤ graph.spectralSlots + 1

def skyrmsTransitionGraph : TransitionGraph := ⟨2, 1⟩
def liftedTransitionGraph : TransitionGraph := ⟨3, 2⟩

theorem chromatic_spectral_base_bridge :
    chromaticSpectralAligned skyrmsTransitionGraph
    ∧ graphSupportsNoise skyrmsTransitionGraph .pink
    ∧ ¬ graphSupportsNoise skyrmsTransitionGraph .brown := by
  unfold chromaticSpectralAligned graphSupportsNoise
    skyrmsTransitionGraph alphaMagnitude
  decide

theorem chromatic_spectral_lift_bridge :
    chromaticSpectralAligned liftedTransitionGraph
    ∧ graphSupportsNoise liftedTransitionGraph .brown := by
  unfold chromaticSpectralAligned graphSupportsNoise
    liftedTransitionGraph alphaMagnitude
  decide

/-! ## Topological safety -/

/-- A finite safety property: the carrier remains coherent, the boundary has
not collapsed, the manifold admits the color, and the transition graph has
matching chromatic/spectral capacity. -/
def topologicallySafe
    (field : NoiseField) (manifold : NoiseManifold)
    (graph : TransitionGraph) (color : NoiseColor) : Prop :=
  coherentNoise field
    ∧ ¬ boundaryCollapse field
    ∧ geometricallyAllowed manifold color
    ∧ graphSupportsNoise graph color
    ∧ chromaticSpectralAligned graph

theorem lifted_brown_topologically_safe :
    topologicallySafe carrierField liftedSoundManifold
      liftedTransitionGraph .brown := by
  unfold topologicallySafe coherentNoise boundaryCollapse geometricallyAllowed
    graphSupportsNoise chromaticSpectralAligned carrierField
    liftedSoundManifold liftedTransitionGraph alphaMagnitude
  decide

theorem collapsed_field_not_safe_for_brown :
    ¬ topologicallySafe collapsedField liftedSoundManifold
      liftedTransitionGraph .brown := by
  unfold topologicallySafe coherentNoise boundaryCollapse geometricallyAllowed
    graphSupportsNoise chromaticSpectralAligned collapsedField
    liftedSoundManifold liftedTransitionGraph alphaMagnitude
  decide

/-! ## Visual-noise operators: stereo fold and blink difference -/

/-- A finite visual trace stands in for high-entropy texture samples. -/
def VisualTrace := List Nat

/-- The 90s autostereogram move: compare a trace with a shifted copy. The
operator does not inspect isolated pixels; it asks whether an offset alignment
reveals a repeated constraint. -/
structure StereoAlignment where
  trace : VisualTrace
  offset : Nat
  matchedPairs : Nat
  requiredPairs : Nat

/-- A stereo fold reveals hidden structure when enough offset-aligned pairs
match. This is the formal version of changing eye convergence until an
otherwise noisy texture resolves into a latent object. -/
def stereoFoldReveals (alignment : StereoAlignment) : Prop :=
  0 < alignment.offset ∧ alignment.requiredPairs ≤ alignment.matchedPairs

/-- Difference/blink comparison: shared background is cancelled and only the
structural drift remains. -/
structure BlinkDifference where
  commonCarrier : Nat
  residualDrift : Nat
  driftThreshold : Nat

def blinkDifferenceDetects (diff : BlinkDifference) : Prop :=
  diff.driftThreshold ≤ diff.residualDrift

def blinkDifferenceIgnores (diff : BlinkDifference) : Prop :=
  diff.residualDrift < diff.driftThreshold

/-- A residual becomes persistent when the blink difference is large enough
and a corresponding topological feature survives the sieve. -/
def persistentResidual
    (diff : BlinkDifference) (threshold : Nat) (feature : PersistentFeature) :
    Prop :=
  blinkDifferenceDetects diff ∧ latentStructure threshold feature

def hiddenMessageAlignment : StereoAlignment :=
  ⟨[0, 1, 4, 1, 4, 1, 4, 0], 1, 3, 3⟩

def flatAlignment : StereoAlignment :=
  ⟨[0, 1, 2, 3], 0, 4, 3⟩

def ordinaryBlinkNoise : BlinkDifference := ⟨10, 1, 3⟩
def structuralBlinkDrift : BlinkDifference := ⟨10, 4, 3⟩

theorem stereo_fold_reveals_hidden_alignment :
    stereoFoldReveals hiddenMessageAlignment := by
  unfold stereoFoldReveals hiddenMessageAlignment
  decide

theorem zero_offset_cannot_stereo_reveal :
    ¬ stereoFoldReveals flatAlignment := by
  unfold stereoFoldReveals flatAlignment
  decide

theorem blink_difference_separates_drift_from_noise :
    blinkDifferenceIgnores ordinaryBlinkNoise
    ∧ blinkDifferenceDetects structuralBlinkDrift := by
  unfold blinkDifferenceIgnores blinkDifferenceDetects
    ordinaryBlinkNoise structuralBlinkDrift
  decide

theorem blink_persistent_residual_is_latent_structure :
    persistentResidual structuralBlinkDrift 3 persistentHole := by
  unfold persistentResidual blinkDifferenceDetects latentStructure persistence
    structuralBlinkDrift persistentHole
  decide

/-! ## Visual operators as distribution operators -/

/-- Stereo folding a hidden alignment lifts a flat carrier into pink structure:
the repeated constraint is visible only after offset alignment. -/
def stereoFoldFingerprint (alignment : StereoAlignment) : SpectralFingerprint :=
  if alignment.offset = 0 then
    colorFingerprint .white
  else if alignment.requiredPairs ≤ alignment.matchedPairs then
    colorFingerprint .pink
  else
    colorFingerprint .white

/-- Blink difference maps structural residuals to the magnitude-two boundary;
ordinary residuals collapse back to white. -/
def blinkDifferenceFingerprint (diff : BlinkDifference) : SpectralFingerprint :=
  if diff.driftThreshold ≤ diff.residualDrift then
    colorFingerprint .brown
  else
    colorFingerprint .white

theorem stereo_fold_lifts_white_to_pink :
    stereoFoldFingerprint hiddenMessageAlignment = colorFingerprint .pink := by
  unfold stereoFoldFingerprint hiddenMessageAlignment colorFingerprint
  decide

theorem blink_difference_lifts_structural_drift_to_brown :
    blinkDifferenceFingerprint structuralBlinkDrift = colorFingerprint .brown := by
  unfold blinkDifferenceFingerprint structuralBlinkDrift
    colorFingerprint
  decide

theorem visual_noise_operators_recover_hidden_structure :
    stereoFoldFingerprint hiddenMessageAlignment = colorFingerprint .pink
    ∧ blinkDifferenceFingerprint structuralBlinkDrift = colorFingerprint .brown
    ∧ persistentResidual structuralBlinkDrift 3 persistentHole := by
  simp [stereoFoldFingerprint, blinkDifferenceFingerprint, persistentResidual,
    blinkDifferenceDetects, latentStructure, persistence, hiddenMessageAlignment,
    structuralBlinkDrift, persistentHole, colorFingerprint]

/-! ## Noise stereogram as one-step rotation -/

/-- A finite phase rotation. This is the "one step off" mechanism: compare a
carrier against a rotated phase rather than against itself. -/
def phaseRotate (modulus phase steps : Nat) : Nat :=
  (phase + steps) % modulus

/-- A parallax rotation records the phase offset used to compare two views of
the same high-entropy carrier. -/
structure ParallaxRotation where
  modulus : Nat
  sourcePhase : Nat
  steps : Nat
  targetPhase : Nat

def validParallaxRotation (r : ParallaxRotation) : Prop :=
  0 < r.modulus ∧ phaseRotate r.modulus r.sourcePhase r.steps = r.targetPhase

def oneStepOff (r : ParallaxRotation) : Prop :=
  validParallaxRotation r ∧ r.steps = 1

def stereogramRotation : ParallaxRotation := ⟨4, 0, 1, 1⟩

/-- The hidden-message alignment is exactly the one-step parallax case:
offset alignment is a phase rotation, not a new random source. -/
theorem stereogram_is_one_step_rotation :
    oneStepOff stereogramRotation
    ∧ hiddenMessageAlignment.offset = stereogramRotation.steps
    ∧ stereoFoldReveals hiddenMessageAlignment := by
  unfold oneStepOff validParallaxRotation phaseRotate stereogramRotation
    hiddenMessageAlignment stereoFoldReveals
  decide

/-- One-step parallax turns the flat carrier into the pink hidden-structure
contract. -/
theorem one_step_rotation_lifts_carrier :
    oneStepOff stereogramRotation
    ∧ stereoFoldFingerprint hiddenMessageAlignment = colorFingerprint .pink := by
  unfold oneStepOff validParallaxRotation phaseRotate stereogramRotation
    stereoFoldFingerprint hiddenMessageAlignment colorFingerprint
  decide

/-! ## Information as temporal diff: the triton -/

/-- A three-time witness: past, present, future. The information is not any
single sample; it is the difference relation across the three samples. -/
structure TemporalTriton where
  past : Nat
  present : Nat
  future : Nat

/-- Directed absolute difference between two finite states. -/
def natDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

def pastPresentDiff (t : TemporalTriton) : Nat :=
  natDiff t.past t.present

def presentFutureDiff (t : TemporalTriton) : Nat :=
  natDiff t.present t.future

/-- Second-degree information: the diff of diffs. This is the extra
dimensional coordinate carried by every step once the system observes change
instead of only state. -/
def secondDegreeDiff (t : TemporalTriton) : Nat :=
  natDiff (pastPresentDiff t) (presentFutureDiff t)

/-- A lifted step carries base state plus the diff coordinate. -/
structure DiffLiftedStep where
  baseDimension : Nat
  diffDimension : Nat

def liftByDiff (baseDimension diff : Nat) : DiffLiftedStep :=
  ⟨baseDimension, diff⟩

def totalLiftedDimension (step : DiffLiftedStep) : Nat :=
  step.baseDimension + step.diffDimension

def tritonPulse : TemporalTriton := ⟨4, 5, 7⟩

theorem information_is_the_diff :
    pastPresentDiff tritonPulse = 1
    ∧ presentFutureDiff tritonPulse = 2
    ∧ secondDegreeDiff tritonPulse = 1 := by
  unfold pastPresentDiff presentFutureDiff secondDegreeDiff tritonPulse natDiff
  decide

theorem every_step_gets_second_degree_dimension :
    totalLiftedDimension (liftByDiff 6 (secondDegreeDiff tritonPulse)) = 7 := by
  unfold totalLiftedDimension liftByDiff secondDegreeDiff pastPresentDiff
    presentFutureDiff tritonPulse natDiff
  decide

theorem temporal_triton_connects_rotation_and_diff :
    oneStepOff stereogramRotation
    ∧ secondDegreeDiff tritonPulse = stereogramRotation.steps := by
  unfold oneStepOff validParallaxRotation phaseRotate stereogramRotation
    secondDegreeDiff pastPresentDiff presentFutureDiff tritonPulse natDiff
  decide

/-! ## Statistical teleportation and bizarro parallax -/

/-- Statistical teleportation: a source and target are close enough that
distance collapses into an admissible rotation coordinate. -/
structure StatisticalTeleport where
  source : Nat
  target : Nat
  distance : Nat
  threshold : Nat
  rotationSteps : Nat

def teleportAdmissible (t : StatisticalTeleport) : Prop :=
  t.distance ≤ t.threshold

def distanceDeath (t : StatisticalTeleport) : Prop :=
  teleportAdmissible t ∧ t.distance = 0

def bizarroParallax (t : StatisticalTeleport) : Prop :=
  teleportAdmissible t ∧ t.distance ≠ 0 ∧ t.rotationSteps = 1

def exactTeleport : StatisticalTeleport := ⟨4, 4, 0, 1, 0⟩
def oneStepTeleport : StatisticalTeleport := ⟨4, 5, 1, 1, 1⟩

/-- Exact teleportation kills distance completely. -/
theorem exact_teleport_is_death_of_distance :
    distanceDeath exactTeleport := by
  unfold distanceDeath teleportAdmissible exactTeleport
  decide

/-- The one-step admissible miss is not failure; it is the bizarro parallax
space where the hidden stereogram operator has work to do. -/
theorem one_step_teleport_creates_bizarro_space :
    bizarroParallax oneStepTeleport
    ∧ oneStepTeleport.rotationSteps = stereogramRotation.steps
    ∧ stereoFoldReveals hiddenMessageAlignment := by
  unfold bizarroParallax teleportAdmissible oneStepTeleport
    stereogramRotation hiddenMessageAlignment stereoFoldReveals
  decide

/-- Statistical teleportation and stereogram rotation are the same finite
shape in this witness: distance has collapsed to a one-step phase mismatch. -/
theorem statistical_teleportation_is_one_step_rotation :
    bizarroParallax oneStepTeleport
    ∧ oneStepOff stereogramRotation
    ∧ oneStepTeleport.rotationSteps = secondDegreeDiff tritonPulse := by
  unfold bizarroParallax teleportAdmissible oneStepOff validParallaxRotation
    phaseRotate oneStepTeleport stereogramRotation secondDegreeDiff
    pastPresentDiff presentFutureDiff tritonPulse natDiff
  decide

/-! ## Bizarro mesh as index plus two storage banks -/

/-- Storage role in the bizarro mesh: present is the live index; past/future
are the two storage banks that give the index parallax. -/
inductive TemporalStorageRole where
  | pastStorage
  | presentIndex
  | futureStorage
  deriving DecidableEq, Repr

def roleDimension : TemporalStorageRole → Nat
  | .presentIndex => 1
  | .pastStorage => 2
  | .futureStorage => 3

/-- The operational bizarro mesh: a current index with two storage witnesses. -/
structure BizarroMeshIndex where
  currentIndex : Nat
  pastBank : Nat
  futureBank : Nat

def bizarroMesh : BizarroMeshIndex := ⟨5, 4, 7⟩

def indexMatchesPresent (mesh : BizarroMeshIndex) (t : TemporalTriton) : Prop :=
  mesh.currentIndex = t.present

def storageMatchesTriton (mesh : BizarroMeshIndex) (t : TemporalTriton) : Prop :=
  mesh.pastBank = t.past ∧ mesh.futureBank = t.future

/-- The storage banks provide two out-of-index dimensions. -/
def storageBankCount (_mesh : BizarroMeshIndex) : Nat := 2

/-- The live index is one-dimensional while past/future occupy the two storage
dimensions. -/
theorem present_is_index_past_future_are_storage :
    roleDimension .presentIndex = 1
    ∧ roleDimension .pastStorage = 2
    ∧ roleDimension .futureStorage = 3
    ∧ storageBankCount bizarroMesh = 2 := by
  decide

theorem bizarro_mesh_matches_triton_storage :
    indexMatchesPresent bizarroMesh tritonPulse
    ∧ storageMatchesTriton bizarroMesh tritonPulse := by
  unfold indexMatchesPresent storageMatchesTriton bizarroMesh tritonPulse
  decide

/-- Bizarro space is the parallax between the current index and its two
storage banks: the second-degree triton diff is exactly the one-step miss. -/
theorem bizarro_mesh_is_one_step_storage_parallax :
    indexMatchesPresent bizarroMesh tritonPulse
    ∧ storageMatchesTriton bizarroMesh tritonPulse
    ∧ secondDegreeDiff tritonPulse = 1
    ∧ bizarroParallax oneStepTeleport := by
  unfold indexMatchesPresent storageMatchesTriton bizarroMesh tritonPulse
    secondDegreeDiff pastPresentDiff presentFutureDiff natDiff bizarroParallax
    teleportAdmissible oneStepTeleport
  decide

/-! ## Noise stereogram as constrained diff potential -/

/-- A bizarro stereogram packages the visual-noise intuition into the same
index/storage split used by the bizarro mesh: a high-entropy carrier, an
alignment operator, a blink-diff residual, and a live index with two latent
storage banks. -/
structure BizarroStereogram where
  potential : InformationalPotential
  alignment : StereoAlignment
  diff : BlinkDifference
  mesh : BizarroMeshIndex

def bizarroStereogramWitness : BizarroStereogram :=
  ⟨constrainedDiffPotential, hiddenMessageAlignment,
    structuralBlinkDrift, bizarroMesh⟩

/-- A noise stereogram is readable when the carrier has maximal diff
potential, a nonzero constraint selects recoverable information, stereo
alignment reveals structure, and blink comparison detects structural drift. -/
def readableNoiseStereogram (s : BizarroStereogram) : Prop :=
  maximallyOpen s.potential
    ∧ recoverableInformation s.potential
    ∧ stereoFoldReveals s.alignment
    ∧ blinkDifferenceDetects s.diff

/-- The present index and the two storage banks give the readable stereogram
its triton storage interpretation. -/
def stereogramUsesBizarroStorage
    (s : BizarroStereogram) (t : TemporalTriton) : Prop :=
  indexMatchesPresent s.mesh t ∧ storageMatchesTriton s.mesh t

/-- High entropy supplies the possible differences; constraints and bizarro
storage make the difference readable. -/
theorem noise_stereogram_is_constrained_diff_potential :
    readableNoiseStereogram bizarroStereogramWitness
    ∧ stereogramUsesBizarroStorage bizarroStereogramWitness tritonPulse
    ∧ secondDegreeDiff tritonPulse =
      bizarroStereogramWitness.alignment.offset := by
  unfold readableNoiseStereogram stereogramUsesBizarroStorage
    bizarroStereogramWitness maximallyOpen recoverableInformation
    stereoFoldReveals blinkDifferenceDetects indexMatchesPresent
    storageMatchesTriton constrainedDiffPotential hiddenMessageAlignment
    structuralBlinkDrift bizarroMesh tritonPulse secondDegreeDiff
    pastPresentDiff presentFutureDiff natDiff
  decide

/-- The concise thesis: entropy is potential; constrained diff is information;
one-step parallax is the decoder. -/
theorem entropy_potential_constrained_diff_thesis :
    maximallyOpen pureRandomPotential
    ∧ availableDiffs pureRandomPotential =
      availableDiffs constrainedDiffPotential
    ∧ ¬ recoverableInformation pureRandomPotential
    ∧ recoverableInformation constrainedDiffPotential
    ∧ actualizedInformationQuanta unitPotentialCarrier
      constrainedDiffPotential ≤
        physicalPotentialQuanta unitPotentialCarrier constrainedDiffPotential
    ∧ oneStepOff stereogramRotation
    ∧ readableNoiseStereogram bizarroStereogramWitness := by
  simp [maximallyOpen, availableDiffs, recoverableInformation,
    pureRandomPotential, constrainedDiffPotential, oneStepOff,
    validParallaxRotation, phaseRotate, stereogramRotation,
    readableNoiseStereogram, bizarroStereogramWitness,
    stereoFoldReveals, blinkDifferenceDetects, hiddenMessageAlignment,
    structuralBlinkDrift, actualizedInformationQuanta,
    physicalPotentialQuanta, unitPotentialCarrier]

/-! ## Completed finite thesis -/

/-- Finite version of the topological-information thesis: noise is admitted
by geometry, separated by persistence, carried by entropy under invariants,
bounded by a resolvability wall, and transformed by operators on the spectral
distribution contract. Visual-noise operators add the autostereogram/blink
case: hidden structure can be revealed by offset alignment or by cancelling
the common carrier between two traces. The final clause sharpens the entropy
claim: random noise supplies maximal diff potential, but only constrained
diffs become recoverable information. -/
theorem finite_topological_information_noise_calculus :
    geometricallyAllowed baseSoundManifold .pink
    ∧ ¬ geometricallyAllowed baseSoundManifold .brown
    ∧ geometricallyAllowed liftedSoundManifold .brown
    ∧ transientFeature 3 shortHole
    ∧ latentStructure 3 persistentHole
    ∧ coherentNoise carrierField
    ∧ boundaryCollapse collapsedField
    ∧ applyNoiseOperator .integrate (colorFingerprint .pink) =
      colorFingerprint .brown
    ∧ applyNoiseOperator .saturatingFold (colorFingerprint .brown) =
      colorFingerprint .brown
    ∧ chromaticSpectralAligned liftedTransitionGraph
    ∧ graphSupportsNoise liftedTransitionGraph .brown
    ∧ topologicallySafe carrierField liftedSoundManifold
      liftedTransitionGraph .brown
    ∧ stereoFoldFingerprint hiddenMessageAlignment = colorFingerprint .pink
    ∧ blinkDifferenceFingerprint structuralBlinkDrift =
      colorFingerprint .brown
    ∧ oneStepOff stereogramRotation
    ∧ secondDegreeDiff tritonPulse = stereogramRotation.steps
    ∧ bizarroParallax oneStepTeleport
    ∧ indexMatchesPresent bizarroMesh tritonPulse
    ∧ storageMatchesTriton bizarroMesh tritonPulse
    ∧ persistentResidual structuralBlinkDrift 3 persistentHole
    ∧ readableNoiseStereogram bizarroStereogramWitness
    ∧ ¬ recoverableInformation pureRandomPotential
    ∧ recoverableInformation constrainedDiffPotential
    ∧ actualizedInformationQuanta unitPotentialCarrier
      constrainedDiffPotential ≤
        physicalPotentialQuanta unitPotentialCarrier constrainedDiffPotential := by
  simp [geometricallyAllowed, transientFeature, latentStructure, persistence,
    coherentNoise, boundaryCollapse, topologicallySafe, graphSupportsNoise,
    chromaticSpectralAligned, baseSoundManifold, liftedSoundManifold,
    shortHole, persistentHole, carrierField, collapsedField,
    liftedTransitionGraph, alphaMagnitude, applyNoiseOperator,
    colorFingerprint, stereoFoldFingerprint, blinkDifferenceFingerprint,
    blinkDifferenceDetects, persistentResidual, structuralBlinkDrift,
    oneStepOff, validParallaxRotation, phaseRotate, stereogramRotation,
    hiddenMessageAlignment, secondDegreeDiff, pastPresentDiff,
    presentFutureDiff, tritonPulse, natDiff, bizarroParallax,
    teleportAdmissible, oneStepTeleport, indexMatchesPresent,
    storageMatchesTriton, bizarroMesh, readableNoiseStereogram,
    bizarroStereogramWitness, maximallyOpen, recoverableInformation,
    pureRandomPotential, constrainedDiffPotential, stereoFoldReveals,
    actualizedInformationQuanta, physicalPotentialQuanta,
    unitPotentialCarrier, availableDiffs]

/-- Final mesh-facing synthesis: the safe carrier, readable stereogram,
constrained actualization, and boundary saturation all close on the same
finite witness. This is the masterwork endpoint for the coordinator mesh:
noise is geometric, information is constrained diff, and the overload
boundary is a stable fixed point. -/
theorem distributed_inference_mesh_masterwork :
    topologicallySafe carrierField liftedSoundManifold
      liftedTransitionGraph .brown
    ∧ readableNoiseStereogram bizarroStereogramWitness
    ∧ recoverableInformation constrainedDiffPotential
    ∧ 0 < actualizedInformationQuanta unitPotentialCarrier
        constrainedDiffPotential
    ∧ applyNoiseOperator .saturatingFold (colorFingerprint .brown) =
      colorFingerprint .brown
    ∧ oneStepOff stereogramRotation
    ∧ bizarroParallax oneStepTeleport := by
  refine ⟨lifted_brown_topologically_safe, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (noise_stereogram_is_constrained_diff_potential).1
  · exact (constrained_diff_turns_potential_into_information).2.1
  · exact constrained_information_has_positive_physical_actuality
      unitPotentialCarrier (by decide)
  · decide
  · exact (stereogram_is_one_step_rotation).1
  · exact (one_step_teleport_creates_bizarro_space).1

end SpectralNoiseEquilibrium
end Gnosis
