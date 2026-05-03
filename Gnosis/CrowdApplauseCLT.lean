import Init

/-!
# Crowd Applause as Acoustic Central-Limit Pseudo-Noise

This module formalizes the user's claim as a finite, Init-only Lean model:

* one clap is a broad-spectrum transient, not a tuning-fork tone;
* the primary source is air-jet flow from a compressed hand cavity rather
  than solid-tissue collision alone;
* the standard clap bands are `100 Hz..10000 Hz`, with a Helmholtz thud
  around `250 Hz..500 Hz` and a crack around `2000 Hz..4000 Hz`;
* the waveform has attack/body/decay phases, with attack under `1 ms`
  and a dry clap under `10 ms`;
* Repp/Fletcher hand configurations shift resonance, SPL, and high-frequency
  bandwidth;
* a crowd is a massive sum of independent point-process impulses;
* high-frequency transient bins fill with scale, shifting the apparent
  spectrum from pink-ish to white-ish;
* applause is still pseudo-noise rather than pure white noise because it
  retains temporal correlation, admits synchronous phase transitions, and
  has a finite biological clap-rate cap.
* room-acoustics clap tests, synthesis models, and biometric signatures are
  represented as finite side contracts.

No probability-library CLT is imported here.  The CLT-facing content is the
finite contract used in the prose: independent summands plus a large crowd
limit where spectral holes vanish.
-/

namespace Gnosis
namespace CrowdApplauseCLT

/-! ## Frequency and waveform contracts -/

/-- Closed integer frequency interval in Hertz. -/
structure HzBand where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

/-- Interval inclusion for frequency bands. -/
def within (inner outer : HzBand) : Prop :=
  outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi

/-- A band is broad-spectrum when it has more than one frequency point. -/
def broadSpectrum (band : HzBand) : Prop :=
  band.lo < band.hi

/-- A tuning-fork idealization has a single frequency. -/
def singleFrequency (band : HzBand) : Prop :=
  band.lo = band.hi

/-- Standard human clap range from the prompt: `100 Hz..10000 Hz`. -/
def standardHumanClapRange : HzBand :=
  ⟨100, 10000⟩

/-- Low/mid Helmholtz thud band from trapped air between the palms. -/
def helmholtzThudBand : HzBand :=
  ⟨250, 500⟩

/-- High crack band where skin impact and air expulsion are piercing. -/
def crackBand : HzBand :=
  ⟨2000, 4000⟩

/-- Full high-transient region described in the prompt. -/
def highTransientBand : HzBand :=
  ⟨2000, 10000⟩

theorem standard_clap_frequency_signature :
    standardHumanClapRange.lo = 100
    ∧ standardHumanClapRange.hi = 10000
    ∧ helmholtzThudBand.lo = 250
    ∧ helmholtzThudBand.hi = 500
    ∧ crackBand.lo = 2000
    ∧ crackBand.hi = 4000 := by
  decide

theorem thud_and_crack_are_inside_standard_clap :
    within helmholtzThudBand standardHumanClapRange
    ∧ within crackBand standardHumanClapRange
    ∧ within highTransientBand standardHumanClapRange := by
  unfold within standardHumanClapRange helmholtzThudBand crackBand highTransientBand
  decide

theorem clap_is_broad_spectrum_not_tuning_fork :
    broadSpectrum standardHumanClapRange
    ∧ ¬ singleFrequency standardHumanClapRange := by
  unfold broadSpectrum singleFrequency standardHumanClapRange
  decide

/-- Oscilloscope phases of a dry clap transient. -/
inductive ClapPhase where
  | attack
  | body
  | decay
  deriving DecidableEq, Repr

/-- One millisecond in microseconds. -/
def oneMillisecondUs : Nat := 1000

/-- Ten milliseconds in microseconds. -/
def tenMillisecondsUs : Nat := 10000

/-- Dry-clap phase durations in microseconds: near-instant attack,
short body, and rapid decay. -/
def phaseDurationUs : ClapPhase → Nat
  | .attack => 900
  | .body => 3000
  | .decay => 6000

/-- Total dry-clap duration in this finite waveform contract. -/
def dryClapDurationUs : Nat :=
  phaseDurationUs .attack + phaseDurationUs .body + phaseDurationUs .decay

theorem attack_is_under_one_millisecond :
    phaseDurationUs .attack < oneMillisecondUs := by
  decide

theorem dry_clap_is_under_ten_milliseconds :
    dryClapDurationUs < tenMillisecondsUs := by
  decide

theorem waveform_has_attack_body_decay_signature :
    phaseDurationUs .attack = 900
    ∧ phaseDurationUs .body = 3000
    ∧ phaseDurationUs .decay = 6000
    ∧ dryClapDurationUs = 9900 := by
  decide

/-! ## Flow excitation and damping -/

/-- Mechanism candidates for the audible clap onset. -/
inductive SoundGenerationMechanism where
  | airJetFlow
  | solidTissueImpact
  deriving DecidableEq, Repr

/-- Outlet where the compressed cavity vents in the finite model. -/
inductive HandOutlet where
  | thumbIndexGap
  | otherEdge
  deriving DecidableEq, Repr

/-- The primary audible driver is the compressed-cavity air jet. -/
def primarySoundGeneration : SoundGenerationMechanism :=
  .airJetFlow

/-- Pressure/intensity proxy: the new research says intensity scales
quadratically with clap speed, represented here by `speed^2`. -/
def soundPressureProxy (clapSpeed : Nat) : Nat :=
  clapSpeed * clapSpeed

/-- A finite flow-excitation event: enclosure, gauge pressure, vented jet,
and first acoustic peak are tracked directly. -/
structure FlowExcitation where
  temporaryEnclosure : Bool
  gaugePressureProxy : Nat
  outlet : HandOutlet
  jetVelocityProxy : Nat
  firstPeakSynchronized : Bool
  significantSoundBeforeJet : Bool
  deriving DecidableEq, Repr

/-- Canonical flow event for a fast clap in this model. -/
def canonicalFlowExcitation : FlowExcitation :=
  { temporaryEnclosure := true
    gaugePressureProxy := soundPressureProxy 12
    outlet := .thumbIndexGap
    jetVelocityProxy := 12
    firstPeakSynchronized := true
    significantSoundBeforeJet := false }

theorem primary_driver_is_flow_not_solid_impact :
    primarySoundGeneration = .airJetFlow
    ∧ primarySoundGeneration ≠ .solidTissueImpact := by
  decide

theorem pressure_proxy_is_quadratic_example :
    soundPressureProxy 12 = 4 * soundPressureProxy 6
    ∧ soundPressureProxy 6 < soundPressureProxy 12 := by
  unfold soundPressureProxy
  decide

theorem jet_flow_matches_first_acoustic_peak :
    canonicalFlowExcitation.temporaryEnclosure = true
    ∧ canonicalFlowExcitation.outlet = .thumbIndexGap
    ∧ canonicalFlowExcitation.firstPeakSynchronized = true
    ∧ canonicalFlowExcitation.significantSoundBeforeJet = false := by
  decide

/-- Soft hand tissue is viscoelastic and heavily damped. -/
structure HandMaterial where
  viscoelastic : Bool
  dampingRate : Nat
  energyAbsorption : Nat
  deriving DecidableEq, Repr

/-- Soft palm/finger tissue absorbs energy instead of sustaining resonance. -/
def softHandTissue : HandMaterial :=
  { viscoelastic := true
    dampingRate := 9
    energyAbsorption := 8 }

theorem viscoelastic_damping_explains_short_dry_clap :
    softHandTissue.viscoelastic = true
    ∧ 5 ≤ softHandTissue.dampingRate
    ∧ dryClapDurationUs < tenMillisecondsUs := by
  decide

/-! ## Hand geometry changes the spectral mode -/

/-- Palm geometry changes the clap spectrum. -/
inductive ClapMode where
  | flatPalmToPalm
  | cuppedHands
  deriving DecidableEq, Repr

/-- Resonant low band for a clap mode.  Cupped hands lower the Helmholtz
resonance toward `150 Hz..400 Hz`. -/
def modeResonanceBand : ClapMode → HzBand
  | .flatPalmToPalm => helmholtzThudBand
  | .cuppedHands => ⟨150, 400⟩

/-- Overall spectral range for a clap mode. -/
def modeSpectrumBand : ClapMode → HzBand
  | .flatPalmToPalm => standardHumanClapRange
  | .cuppedHands => ⟨150, 4000⟩

/-- Integer width of a frequency band. -/
def bandWidth (band : HzBand) : Nat :=
  band.hi - band.lo

theorem cupped_hands_lower_resonance :
    (modeResonanceBand .cuppedHands).lo = 150
    ∧ (modeResonanceBand .cuppedHands).hi = 400
    ∧ (modeResonanceBand .cuppedHands).hi <
      (modeResonanceBand .flatPalmToPalm).hi := by
  decide

theorem flat_palm_has_broadest_highest_spectrum :
    bandWidth (modeSpectrumBand .cuppedHands) <
      bandWidth (modeSpectrumBand .flatPalmToPalm)
    ∧ (modeSpectrumBand .cuppedHands).hi <
      (modeSpectrumBand .flatPalmToPalm).hi := by
  decide

/-- Effective rigidity proxy for projecting sound.  Flat claps preserve more
transient energy; cupped claps absorb more and emphasize resonance. -/
def effectiveRigidity : ClapMode → Nat
  | .flatPalmToPalm => 9
  | .cuppedHands => 4

theorem flat_clap_projects_more_by_rigidity_proxy :
    effectiveRigidity .cuppedHands < effectiveRigidity .flatPalmToPalm := by
  decide

/-! ## Repp and Fletcher configuration taxonomy -/

/-- Repp's orientation axis. -/
inductive ReppOrientation where
  | parallel
  | angled
  deriving DecidableEq, Repr

/-- Repp's contact axis, with the extra A1+/A1- variants represented as
cupped and flat refinements. -/
inductive ReppContact where
  | palmToPalm
  | midPalm
  | fingersToPalm
  | veryCupped
  | fullyFlat
  deriving DecidableEq, Repr

/-- Eight Repp handclap modes. -/
inductive ReppMode where
  | p1
  | p2
  | p3
  | a1
  | a2
  | a3
  | a1plus
  | a1minus
  deriving DecidableEq, Repr

/-- Orientation of a Repp mode. -/
def reppOrientation : ReppMode → ReppOrientation
  | .p1 | .p2 | .p3 => .parallel
  | .a1 | .a2 | .a3 | .a1plus | .a1minus => .angled

/-- Contact class of a Repp mode. -/
def reppContact : ReppMode → ReppContact
  | .p1 | .a1 => .palmToPalm
  | .p2 | .a2 => .midPalm
  | .p3 | .a3 => .fingersToPalm
  | .a1plus => .veryCupped
  | .a1minus => .fullyFlat

/-- Spectral peak band associated with a Repp mode. -/
def reppPeakBand : ReppMode → HzBand
  | .p1 | .a1 => ⟨150, 900⟩
  | .p2 => ⟨500, 1500⟩
  | .p3 | .a3 => ⟨1500, 2500⟩
  | .a2 => ⟨100, 10000⟩
  | .a1plus => ⟨150, 400⟩
  | .a1minus => ⟨100, 10000⟩

/-- Repp palm modes have a notch around 2.5 kHz. -/
def hasNotchAt2500Hz : ReppMode → Bool
  | .p1 | .a1 => true
  | _ => false

/-- SPL proxy in dB for the Repp modes.  A2 is the loud 85 dB witness. -/
def reppSplDb : ReppMode → Nat
  | .a2 => 85
  | .a1minus => 82
  | .a3 => 80
  | .p3 => 78
  | .p2 => 76
  | .p1 => 72
  | .a1 => 72
  | .a1plus => 70

theorem repp_palm_modes_are_low_peak_with_notch :
    (reppPeakBand .p1).hi < 1000
    ∧ (reppPeakBand .a1).hi < 1000
    ∧ hasNotchAt2500Hz .p1 = true
    ∧ hasNotchAt2500Hz .a1 = true := by
  decide

theorem repp_finger_modes_peak_near_two_khz :
    within (reppPeakBand .p3) ⟨1000, 3000⟩
    ∧ within (reppPeakBand .a3) ⟨1000, 3000⟩ := by
  unfold within
  decide

theorem repp_a2_is_loud_broad_spectrum :
    reppOrientation .a2 = .angled
    ∧ reppContact .a2 = .midPalm
    ∧ reppSplDb .a2 = 85
    ∧ broadSpectrum (reppPeakBand .a2) := by
  unfold broadSpectrum
  decide

theorem repp_cupped_deep_flat_bright :
    (reppPeakBand .a1plus).lo = 150
    ∧ (reppPeakBand .a1plus).hi = 400
    ∧ (reppPeakBand .a1minus).hi = 10000
    ∧ bandWidth (reppPeakBand .a1plus) <
      bandWidth (reppPeakBand .a1minus) := by
  decide

/-- Fletcher's aerodynamic split between flat and domed impacts. -/
inductive FletcherImpact where
  | flat
  | domed
  deriving DecidableEq, Repr

/-- Jet-flow regime in Fletcher's model. -/
inductive JetRegime where
  | subsonic
  | supersonicShock
  deriving DecidableEq, Repr

/-- Fletcher impact spectrum.  Flat reaches broadband 10 kHz; domed rolls
off earlier and keeps a lower resonant maximum. -/
def fletcherSpectrum : FletcherImpact → HzBand
  | .flat => standardHumanClapRange
  | .domed => ⟨150, 4000⟩

/-- Fletcher jet regime by impact geometry. -/
def fletcherJetRegime : FletcherImpact → JetRegime
  | .flat => .supersonicShock
  | .domed => .subsonic

/-- Whether the impact has a strong Helmholtz component. -/
def strongHelmholtzComponent : FletcherImpact → Bool
  | .flat => false
  | .domed => true

theorem fletcher_flat_is_shock_broadband :
    fletcherJetRegime .flat = .supersonicShock
    ∧ (fletcherSpectrum .flat).hi = 10000
    ∧ strongHelmholtzComponent .flat = false := by
  decide

theorem fletcher_domed_is_helmholtz_weighted :
    fletcherJetRegime .domed = .subsonic
    ∧ strongHelmholtzComponent .domed = true
    ∧ (fletcherSpectrum .domed).lo = 150
    ∧ (fletcherSpectrum .domed).hi < (fletcherSpectrum .flat).hi := by
  decide

/-! ## Point processes and crowd summation -/

/-- One person's clap as a finite point-process impulse with timing and
frequency variation. -/
structure PersonClapProcess where
  timingJitterUs : Nat
  frequencyVariationHz : Nat
  impulseEnergy : Nat
  deriving DecidableEq, Repr

/-- Canonical individual clap process: a transient point with variation. -/
def canonicalPersonClap : PersonClapProcess :=
  { timingJitterUs := phaseDurationUs .attack
    frequencyVariationHz := 50
    impulseEnergy := 1 }

/-- A crowd process records the number of independent summands and the
finite proof that the total impulse energy is the sum of those summands. -/
structure CrowdPointProcess where
  participants : Nat
  process : PersonClapProcess
  independentTiming : Bool
  summedImpulseEnergy : Nat
  summedMatches : summedImpulseEnergy = participants * process.impulseEnergy

/-- Build the exact crowd-summation process for `n` people. -/
def crowdPointProcess (n : Nat) : CrowdPointProcess :=
  { participants := n
    process := canonicalPersonClap
    independentTiming := true
    summedImpulseEnergy := n * canonicalPersonClap.impulseEnergy
    summedMatches := rfl }

theorem crowd_signal_is_sum_of_independent_claps (n : Nat) :
    (crowdPointProcess n).independentTiming = true
    ∧ (crowdPointProcess n).summedImpulseEnergy =
      n * canonicalPersonClap.impulseEnergy := by
  constructor <;> rfl

/-! ## Pink-ish individual, white-ish crowd -/

/-- Three-band spectral energy proxy: low thud, mid body, high crack. -/
structure BandEnergy where
  low : Nat
  mid : Nat
  high : Nat
  deriving DecidableEq, Repr

/-- A single clap is low/mid weighted in this contract. -/
def singleClapEnergy : BandEnergy :=
  ⟨4, 8, 2⟩

/-- Pink-ish means low/mid body energy dominates high crack energy. -/
def pinkIshEnergy (e : BandEnergy) : Prop :=
  e.high < e.low + e.mid

/-- White-ish coverage means no high-frequency transient bins remain empty. -/
def highTransientBins : Nat := 64

/-- Stadium-scale witness used by this finite model. -/
def stadiumParticipants : Nat := 64000

/-- Filled high-frequency transient bins.  Once the crowd has at least as
many independent clap offsets as bins, all high-frequency holes are filled. -/
def filledHighTransientBins (participants : Nat) : Nat :=
  if highTransientBins ≤ participants then highTransientBins else participants

/-- Remaining high-frequency holes. -/
def spectralHoles (participants : Nat) : Nat :=
  highTransientBins - filledHighTransientBins participants

/-- Crowd energy adds the individual clap energy plus high-transient bin
coverage from timing offsets. -/
def crowdBandEnergy (participants : Nat) : BandEnergy :=
  { low := participants * singleClapEnergy.low
    mid := participants * singleClapEnergy.mid
    high := participants * singleClapEnergy.high
      + filledHighTransientBins participants }

/-- The apparent noise color in the finite coverage model. -/
inductive ApparentNoiseColor where
  | pinkIsh
  | whiteIsh
  deriving DecidableEq, Repr

/-- Apparent color: high-frequency holes leave the clap pink-ish; zero holes
give the white-ish coverage profile described in the prompt. -/
def apparentNoiseColor (participants : Nat) : ApparentNoiseColor :=
  if spectralHoles participants = 0 then .whiteIsh else .pinkIsh

theorem single_clap_is_pinkish :
    pinkIshEnergy singleClapEnergy
    ∧ apparentNoiseColor 1 = .pinkIsh
    ∧ 0 < spectralHoles 1 := by
  unfold pinkIshEnergy apparentNoiseColor spectralHoles filledHighTransientBins
    singleClapEnergy highTransientBins
  decide

theorem high_transient_bins_fill_at_scale {participants : Nat}
    (h : highTransientBins ≤ participants) :
    filledHighTransientBins participants = highTransientBins
    ∧ spectralHoles participants = 0 := by
  have hfill : filledHighTransientBins participants = highTransientBins := by
    unfold filledHighTransientBins
    simp [h]
  constructor
  · exact hfill
  · unfold spectralHoles
    rw [hfill]
    exact Nat.sub_self highTransientBins

theorem stadium_fills_high_frequency_holes :
    filledHighTransientBins stadiumParticipants = highTransientBins
    ∧ spectralHoles stadiumParticipants = 0 := by
  decide

theorem pink_to_white_transition_at_scale {participants : Nat}
    (h : highTransientBins ≤ participants) :
    apparentNoiseColor participants = .whiteIsh := by
  have hholes := (high_transient_bins_fill_at_scale h).2
  unfold apparentNoiseColor
  simp [hholes]

theorem stadium_crowd_is_whiteish_by_coverage :
    apparentNoiseColor stadiumParticipants = .whiteIsh := by
  decide

theorem crowd_high_energy_has_transient_fill_term (participants : Nat) :
    (crowdBandEnergy participants).high =
      participants * singleClapEnergy.high
        + filledHighTransientBins participants := by
  rfl

/-- Small groups preserve distinguishable clap impulses. -/
def distinguishableIndividualClaps (participants : Nat) : Prop :=
  participants < highTransientBins

/-- Large crowds merge impulses into a continuous texture. -/
def continuousApplauseTexture (participants : Nat) : Prop :=
  highTransientBins ≤ participants

/-- The finite CLT proxy: independent summands plus enough events to fill
the transient bins. -/
def gaussianWhiteApproximationEligible (participants : Nat) : Prop :=
  (crowdPointProcess participants).independentTiming = true
    ∧ highTransientBins ≤ participants
    ∧ spectralHoles participants = 0

theorem small_group_retains_individual_impulses :
    distinguishableIndividualClaps 8
    ∧ ¬ continuousApplauseTexture 8
    ∧ apparentNoiseColor 8 = .pinkIsh := by
  unfold distinguishableIndividualClaps continuousApplauseTexture apparentNoiseColor
    spectralHoles filledHighTransientBins highTransientBins
  decide

theorem stadium_merges_into_continuous_texture :
    continuousApplauseTexture stadiumParticipants
    ∧ gaussianWhiteApproximationEligible stadiumParticipants := by
  unfold continuousApplauseTexture gaussianWhiteApproximationEligible
  constructor
  · decide
  · constructor
    · rfl
    · constructor
      · decide
      · exact stadium_fills_high_frequency_holes.2

/-! ## Why applause is pseudo-noise, not pure white noise -/

/-- Crowd applause regimes: initially stochastic, optionally synchronized. -/
inductive ApplauseRegime where
  | stochastic
  | synchronous
  deriving DecidableEq, Repr

/-- Synchronous clapping creates a low-frequency power spike. -/
def lowFrequencyPower : ApplauseRegime → Nat
  | .stochastic => 1
  | .synchronous => 16

theorem synchronous_phase_transition_creates_low_frequency_spike :
    lowFrequencyPower .stochastic < lowFrequencyPower .synchronous := by
  decide

/-! ## Kuramoto-style synchronization and frustration -/

/-- Finite Kuramoto-style crowd state.  Synchronization is possible when
coupling exceeds the spread of preferred clap rates. -/
structure KuramotoCrowd where
  clapRateHz : Nat
  naturalFrequencySpread : Nat
  couplingStrength : Nat
  phaseLocked : Bool
  deriving DecidableEq, Repr

/-- Synchronization condition for the finite Kuramoto proxy. -/
def synchronizes (crowd : KuramotoCrowd) : Prop :=
  crowd.naturalFrequencySpread ≤ crowd.couplingStrength

/-- Fast applause: high noise intensity, but too much frequency dispersion. -/
def fastUnsynchronizedCrowd : KuramotoCrowd :=
  { clapRateHz := 4
    naturalFrequencySpread := 12
    couplingStrength := 6
    phaseLocked := false }

/-- Period-doubled applause: slower, lower dispersion, phase-locking possible. -/
def periodDoubledCrowd : KuramotoCrowd :=
  { clapRateHz := 2
    naturalFrequencySpread := 5
    couplingStrength := 6
    phaseLocked := true }

/-- Noise-intensity proxy: faster clapping makes a louder unsynchronized
surface. -/
def noiseIntensityProxy (crowd : KuramotoCrowd) : Nat :=
  crowd.clapRateHz * 10

theorem period_doubling_enables_kuramoto_lock :
    ¬ synchronizes fastUnsynchronizedCrowd
    ∧ synchronizes periodDoubledCrowd
    ∧ periodDoubledCrowd.clapRateHz = fastUnsynchronizedCrowd.clapRateHz / 2
    ∧ periodDoubledCrowd.phaseLocked = true := by
  unfold synchronizes fastUnsynchronizedCrowd periodDoubledCrowd
  decide

theorem synchronized_applause_frustration_tradeoff :
    noiseIntensityProxy periodDoubledCrowd <
      noiseIntensityProxy fastUnsynchronizedCrowd
    ∧ ¬ synchronizes fastUnsynchronizedCrowd
    ∧ synchronizes periodDoubledCrowd := by
  unfold noiseIntensityProxy synchronizes fastUnsynchronizedCrowd periodDoubledCrowd
  decide

/-- Temporal driver distinguishing pure white noise from human applause. -/
structure TemporalDriver where
  correlatedMoments : Bool
  finiteClapRateCapHz : Option Nat
  admitsSynchronousPhase : Bool
  deriving DecidableEq, Repr

/-- Mathematical white-noise ideal: no correlation, no biological cap, no
synchronous phase transition. -/
def pureWhiteDriver : TemporalDriver :=
  { correlatedMoments := false
    finiteClapRateCapHz := none
    admitsSynchronousPhase := false }

/-- Human applause driver: correlated, physically capped, and capable of
stochastic-to-synchronous phase transition. -/
def humanApplauseDriver (capHz : Nat) : TemporalDriver :=
  { correlatedMoments := true
    finiteClapRateCapHz := some capHz
    admitsSynchronousPhase := true }

/-- Pure white noise as the temporal ideal named in the prompt. -/
def pureWhiteNoise (driver : TemporalDriver) : Prop :=
  driver.correlatedMoments = false
    ∧ driver.finiteClapRateCapHz = none
    ∧ driver.admitsSynchronousPhase = false

/-- Pseudo-noise: sensor-random appearance with at least one human temporal
driver still present. -/
def pseudoNoise (driver : TemporalDriver) : Prop :=
  driver.correlatedMoments = true
    ∨ driver.finiteClapRateCapHz.isSome = true
    ∨ driver.admitsSynchronousPhase = true

theorem pure_white_driver_is_pure_white :
    pureWhiteNoise pureWhiteDriver := by
  unfold pureWhiteNoise pureWhiteDriver
  decide

theorem applause_is_not_pure_white_noise (capHz : Nat) :
    ¬ pureWhiteNoise (humanApplauseDriver capHz) := by
  intro h
  unfold pureWhiteNoise humanApplauseDriver at h
  cases h.1

theorem applause_is_pseudo_noise (capHz : Nat) :
    pseudoNoise (humanApplauseDriver capHz) := by
  unfold pseudoNoise humanApplauseDriver
  exact Or.inl rfl

/-! ## Room-acoustics measurement contracts -/

/-- Common decay metrics used in room-acoustics surveys. -/
inductive DecayMetric where
  | t20
  | t30
  | rt60
  deriving DecidableEq, Repr

/-- Decay window in dB. -/
def decayWindowDb : DecayMetric → Nat
  | .t20 => 20
  | .t30 => 30
  | .rt60 => 60

/-- Signal-to-noise requirement in dB for each metric. -/
def snrRequirementDb : DecayMetric → Nat
  | .t20 => 35
  | .t30 => 45
  | .rt60 => 75

/-- Impulsive source model for clap-test reliability. -/
structure ImpulseSource where
  signalAboveBackgroundDb : Nat
  directionalBiasDb : Nat
  lowFrequencyFloorHz : Nat
  lowBandGainDb : Nat
  deriving DecidableEq, Repr

/-- Whether the source has enough SNR for a decay metric. -/
def meetsSnr (metric : DecayMetric) (source : ImpulseSource) : Prop :=
  snrRequirementDb metric ≤ source.signalAboveBackgroundDb

/-- Directional bias greater than 15 dB is treated as non-omnidirectional. -/
def directionalBiasAcceptable (source : ImpulseSource) : Prop :=
  source.directionalBiasDb ≤ 15

/-- Low-frequency coverage reaches at least the 125 Hz octave band. -/
def lowFrequencyCoverage (source : ImpulseSource) : Prop :=
  source.lowFrequencyFloorHz ≤ 125

/-- A typical bare clap in a concert hall, using an integer 26 dB proxy for
the reported 26.4 dB above background. -/
def bareHandclapSource : ImpulseSource :=
  { signalAboveBackgroundDb := 26
    directionalBiasDb := 16
    lowFrequencyFloorHz := 500
    lowBandGainDb := 0 }

/-- Leather gloves add low-band SPL and extend the practical low-frequency
source down to the 125 Hz band in this finite contract. -/
def leatherGloveClapSource : ImpulseSource :=
  { signalAboveBackgroundDb := bareHandclapSource.signalAboveBackgroundDb + 15
    directionalBiasDb := bareHandclapSource.directionalBiasDb
    lowFrequencyFloorHz := 125
    lowBandGainDb := 15 }

theorem decay_metric_requirements :
    decayWindowDb .t20 = 20
    ∧ snrRequirementDb .t20 = 35
    ∧ decayWindowDb .t30 = 30
    ∧ snrRequirementDb .t30 = 45
    ∧ decayWindowDb .rt60 = 60
    ∧ snrRequirementDb .rt60 = 75 := by
  decide

theorem bare_clap_test_is_unreliable_for_professional_rt :
    ¬ meetsSnr .t20 bareHandclapSource
    ∧ ¬ meetsSnr .t30 bareHandclapSource
    ∧ ¬ directionalBiasAcceptable bareHandclapSource
    ∧ ¬ lowFrequencyCoverage bareHandclapSource := by
  unfold meetsSnr directionalBiasAcceptable lowFrequencyCoverage
    bareHandclapSource snrRequirementDb
  decide

theorem leather_gloves_improve_snr_but_not_directionality :
    leatherGloveClapSource.lowBandGainDb = 15
    ∧ meetsSnr .t20 leatherGloveClapSource
    ∧ ¬ meetsSnr .t30 leatherGloveClapSource
    ∧ lowFrequencyCoverage leatherGloveClapSource
    ∧ ¬ directionalBiasAcceptable leatherGloveClapSource := by
  unfold meetsSnr lowFrequencyCoverage directionalBiasAcceptable
    leatherGloveClapSource bareHandclapSource snrRequirementDb
  decide

/-! ## Digital synthesis contracts -/

/-- Event controls used by synthesis systems for many clappers. -/
inductive EnsembleEventModel where
  | poisson
  | kuramoto
  | roundRobin
  deriving DecidableEq, Repr

/-- Single-clap synthesis architecture: excitation plus resonator filtering. -/
structure ClapSynthesisModel where
  whiteNoiseExcitation : Bool
  bandPassShaped : Bool
  attackDecayEnvelope : Bool
  resonatorOrder : Nat
  lpcDerivedCoefficients : Bool
  randomizedParameters : Bool
  deriving DecidableEq, Repr

/-- Physics-informed ClapLab/ClaPD-style finite synthesis contract. -/
def resonatorFilterClapModel : ClapSynthesisModel :=
  { whiteNoiseExcitation := true
    bandPassShaped := true
    attackDecayEnvelope := true
    resonatorOrder := 4
    lpcDerivedCoefficients := true
    randomizedParameters := true }

/-- Crowd-applause synthesis control layer. -/
structure CrowdSynthesisModel where
  clapperPoolSize : Nat
  eventModel : EnsembleEventModel
  roundRobinReallocation : Bool
  kuramotoControl : Bool
  deriving DecidableEq, Repr

/-- Asynchronous crowd: Poisson event generation over a virtual pool. -/
def poissonCrowdSynthesis : CrowdSynthesisModel :=
  { clapperPoolSize := 64
    eventModel := .poisson
    roundRobinReallocation := true
    kuramotoControl := false }

/-- Rhythmic crowd: Kuramoto phase control over a virtual pool. -/
def kuramotoCrowdSynthesis : CrowdSynthesisModel :=
  { clapperPoolSize := 64
    eventModel := .kuramoto
    roundRobinReallocation := true
    kuramotoControl := true }

theorem resonator_filter_synthesis_contract :
    resonatorFilterClapModel.whiteNoiseExcitation = true
    ∧ resonatorFilterClapModel.bandPassShaped = true
    ∧ resonatorFilterClapModel.attackDecayEnvelope = true
    ∧ 2 ≤ resonatorFilterClapModel.resonatorOrder
    ∧ resonatorFilterClapModel.lpcDerivedCoefficients = true
    ∧ resonatorFilterClapModel.randomizedParameters = true := by
  decide

theorem large_ensemble_synthesis_modes :
    poissonCrowdSynthesis.eventModel = .poisson
    ∧ poissonCrowdSynthesis.roundRobinReallocation = true
    ∧ kuramotoCrowdSynthesis.eventModel = .kuramoto
    ∧ kuramotoCrowdSynthesis.kuramotoControl = true
    ∧ poissonCrowdSynthesis.clapperPoolSize =
      kuramotoCrowdSynthesis.clapperPoolSize := by
  decide

/-! ## Biometric signature contracts -/

/-- Biological and behavioral variables that shape a personal clap. -/
inductive BiometricVariable where
  | skinTexture
  | handSize
  | cavityGeometry
  | boneStructure
  | strikingForce
  | personalTechnique
  deriving DecidableEq, Repr

/-- Full finite list of identity-bearing clap variables. -/
def clapIdentityVariables : List BiometricVariable :=
  [ .skinTexture
  , .handSize
  , .cavityGeometry
  , .boneStructure
  , .strikingForce
  , .personalTechnique
  ]

/-- A biometric signature is nontrivial when it includes physical geometry,
damping, and performance variables. -/
def biometricSignatureNontrivial (xs : List BiometricVariable) : Prop :=
  BiometricVariable.handSize ∈ xs
    ∧ BiometricVariable.skinTexture ∈ xs
    ∧ BiometricVariable.strikingForce ∈ xs
    ∧ BiometricVariable.personalTechnique ∈ xs

theorem clap_has_biometric_signature_basis :
    biometricSignatureNontrivial clapIdentityVariables
    ∧ BiometricVariable.cavityGeometry ∈ clapIdentityVariables
    ∧ BiometricVariable.boneStructure ∈ clapIdentityVariables := by
  unfold biometricSignatureNontrivial clapIdentityVariables
  decide

/-! ## End-to-end theorem matching the prose -/

/-- The complete finite theorem: one clap is a broad transient with the
given bands; one clap is pink-ish; a stadium-scale crowd fills the
high-frequency holes and appears white-ish; it is nevertheless not pure
white noise because the human temporal driver remains. -/
theorem applause_clt_acoustic_pseudonoise_summary (capHz : Nat) :
    broadSpectrum standardHumanClapRange
    ∧ within helmholtzThudBand standardHumanClapRange
    ∧ within crackBand standardHumanClapRange
    ∧ phaseDurationUs .attack < oneMillisecondUs
    ∧ dryClapDurationUs < tenMillisecondsUs
    ∧ (crowdPointProcess stadiumParticipants).independentTiming = true
    ∧ apparentNoiseColor 1 = .pinkIsh
    ∧ apparentNoiseColor stadiumParticipants = .whiteIsh
    ∧ ¬ pureWhiteNoise (humanApplauseDriver capHz)
    ∧ pseudoNoise (humanApplauseDriver capHz) := by
  constructor
  · exact clap_is_broad_spectrum_not_tuning_fork.1
  · constructor
    · exact thud_and_crack_are_inside_standard_clap.1
    · constructor
      · exact thud_and_crack_are_inside_standard_clap.2.1
      · constructor
        · exact attack_is_under_one_millisecond
        · constructor
          · exact dry_clap_is_under_ten_milliseconds
          · constructor
            · decide
            · constructor
              · exact single_clap_is_pinkish.2.1
              · constructor
                · exact stadium_crowd_is_whiteish_by_coverage
                · constructor
                  · exact applause_is_not_pure_white_noise capHz
                  · exact applause_is_pseudo_noise capHz

/-- Research-refined summary: air-jet physics, hand-mode taxonomy,
crowd-scale CLT proxy, synchronization/frustration, measurement limits,
synthesis, and biometric structure are all present in the finite model. -/
theorem refined_handclap_research_summary (capHz : Nat) :
    primarySoundGeneration = .airJetFlow
    ∧ canonicalFlowExcitation.firstPeakSynchronized = true
    ∧ soundPressureProxy 12 = 4 * soundPressureProxy 6
    ∧ reppSplDb .a2 = 85
    ∧ fletcherJetRegime .flat = .supersonicShock
    ∧ gaussianWhiteApproximationEligible stadiumParticipants
    ∧ synchronizes periodDoubledCrowd
    ∧ ¬ synchronizes fastUnsynchronizedCrowd
    ∧ ¬ meetsSnr .t30 bareHandclapSource
    ∧ meetsSnr .t20 leatherGloveClapSource
    ∧ resonatorFilterClapModel.whiteNoiseExcitation = true
    ∧ biometricSignatureNontrivial clapIdentityVariables
    ∧ pseudoNoise (humanApplauseDriver capHz) := by
  constructor
  · exact primary_driver_is_flow_not_solid_impact.1
  · constructor
    · exact jet_flow_matches_first_acoustic_peak.2.2.1
    · constructor
      · exact pressure_proxy_is_quadratic_example.1
      · constructor
        · exact repp_a2_is_loud_broad_spectrum.2.2.1
        · constructor
          · exact fletcher_flat_is_shock_broadband.1
          · constructor
            · exact stadium_merges_into_continuous_texture.2
            · constructor
              · exact period_doubling_enables_kuramoto_lock.2.1
              · constructor
                · exact period_doubling_enables_kuramoto_lock.1
                · constructor
                  · exact bare_clap_test_is_unreliable_for_professional_rt.2.1
                  · constructor
                    · exact leather_gloves_improve_snr_but_not_directionality.2.1
                    · constructor
                      · exact resonator_filter_synthesis_contract.1
                      · constructor
                        · exact clap_has_biometric_signature_basis.1
                        · exact applause_is_pseudo_noise capHz

end CrowdApplauseCLT
end Gnosis
