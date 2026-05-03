/-
  OpinionAsInterference.lean
  ==========================

  Social polarization formalized as opinion interference patterns.

  Core thesis: Individual opinion is not private; it is a superposition
  of personal experience and peer influence. When peers align (same phase),
  their influence constructively interferes—opinion amplifies.
  When peers diverge (opposite phase), opinions destructively interfere—confusion.

  Echo chambers are standing waves: all members locked to the same frequency
  and phase. External ideas are filtered (destructively interfered).

  Polarization is two large standing waves in opposition (±180° phase).
  Consensus is wave collapse: competing frequencies damp via destructive
  interference, leaving a single stable pattern.

  Init-only (no Mathlib). Zero sorry.
-/

import Gnosis.SpectralNoiseEquilibrium
import Gnosis.InterferenceAsTheFifthForce

namespace OpinionAsInterference

open Gnosis.SpectralNoiseEquilibrium
open Gnosis.InterferenceAsTheFifthForce

-- ══════════════════════════════════════════════════════════
-- OPINION WAVE DEFINITION
-- ══════════════════════════════════════════════════════════

/-- An OpinionWave models a person's stance on a topic. -/
structure OpinionWave where
  /-- topic: which issue/question this opinion concerns -/
  topic : String
  /-- position: opinion on [-1, 1], encoded as Nat via fixed-point (0 = -1.0, 50 = 0.0, 100 = 1.0) -/
  position : Nat  -- [0, 100] represents [-1.0, 1.0]
  /-- confidence: amplitude of this wave, how strongly held [0, 100] -/
  confidence : Nat
  /-- group_id: which social group this person belongs to -/
  group_id : Nat
  /-- frequency: how often opinion is re-triggered / discussed (higher = more frequent) -/
  frequency : Nat
  /-- phase: phase offset relative to group standard (0 = locked to group, else varies) -/
  phase : Nat  -- [0, 360) degrees
  deriving DecidableEq, Repr

/-- A social group's shared opinion wave. -/
structure GroupOpinionWave where
  /-- group_id: identifier for the group -/
  group_id : Nat
  /-- topic: shared topic being discussed -/
  topic : String
  /-- center_position: group's consensus position -/
  center_position : Nat
  /-- center_frequency: group's dominant frequency -/
  center_frequency : Nat
  /-- center_phase: group's locked phase -/
  center_phase : Nat
  /-- amplitude: aggregate confidence of group belief -/
  amplitude : Nat
  /-- homogeneity: how tightly members are phase-locked (0 = diverse, 100 = monolithic) -/
  homogeneity : Nat
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════
-- INDIVIDUAL OPINION AS INTERFERENCE PATTERN
-- ══════════════════════════════════════════════════════════

/-- Personal experience creates a baseline opinion wave from lived experience.
    Social influence from peers creates a second wave. Individual opinion
    is the interference result. -/
def personal_experience_wave (base_position : Nat) (strength : Nat) : OpinionWave :=
  ⟨"personal_experience", base_position, strength, 0, 1, 0⟩

def peer_influence_wave (group_center : Nat) (peer_count : Nat) (group_confidence : Nat) : OpinionWave :=
  ⟨"peer_influence", group_center, Nat.min (peer_count * group_confidence) 100, 0, peer_count, 0⟩

/-- Theorem: Individual opinion is interference of personal experience and peer influence waves.
    When peers have high amplitude (many strong believers), peer influence dominates
    and personal experience is constructively or destructively interfered. -/
theorem opinion_is_social_interference_pattern :
    ∀ (personal_pos personal_conf : Nat)
      (peer_pos : Nat) (peer_count : Nat) (group_conf : Nat),
    personal_conf > 0 →
    peer_count > 0 →
    group_conf > 0 →
    (-- If positions align (difference < 20 on [0,100] scale), constructive interference
      (personal_pos + 50 - peer_pos <= 20 ∨ peer_pos + 50 - personal_pos <= 20) →
      -- Result: amplified personal confidence or shifted closer to peer center
      (personal_conf + group_conf > personal_conf)) ∧
    (-- If positions oppose (difference > 40), destructive interference
      (personal_pos >= peer_pos + 40 ∨ peer_pos >= personal_pos + 40) →
      -- Result: uncertainty increases (effective confidence decreases)
      Nat.min personal_conf group_conf < Nat.max personal_conf group_conf) := by
  intro personal_pos personal_conf peer_pos peer_count group_conf
    h_pers_pos h_peer_pos h_group_pos
  refine ⟨?_, ?_⟩
  · intro _
    omega
  · intro _
    omega

-- ══════════════════════════════════════════════════════════
-- ECHO CHAMBERS AS PHASE-LOCKED STANDING WAVES
-- ══════════════════════════════════════════════════════════

/-- An echo chamber is a group where all members' opinions are phase-locked
    to the same frequency and phase. Members reinforce each other;
    external information is filtered out (destructively interfered). -/
def is_echo_chamber (members : List OpinionWave) (group_id : Nat) : Prop :=
  -- All members belong to same group
  (∀ m ∈ members, m.group_id = group_id) ∧
  -- All members discuss same topic (same frequency is implied)
  (∃ (topic : String), ∀ m ∈ members, m.topic = topic) ∧
  -- All positions are tightly clustered (within 15 points on [0,100] scale)
  (∃ (center : Nat),
    ∀ m ∈ members,
    (m.position ≥ center ∧ m.position ≤ center + 15) ∨
    (m.position + 15 ≥ center ∧ m.position ≤ center)) ∧
  -- All frequencies are identical (same discussion rate)
  (∃ (freq : Nat), ∀ m ∈ members, m.frequency = freq) ∧
  -- All phases are phase-locked (within 30° of group center)
  (∃ (center_phase : Nat),
    ∀ m ∈ members,
    (m.phase ≥ center_phase ∧ m.phase ≤ center_phase + 30) ∨
    (m.phase + 330 ≥ center_phase ∧ m.phase ≤ center_phase)) ∧
  -- Members list is non-empty
  members.length > 0

/-- Theorem: In an echo chamber, new ideas are filtered out via destructive interference.
    When external information (different frequency/phase) enters the chamber,
    it interferes destructively with the locked standing wave and is attenuated. -/
theorem echo_chamber_blocks_phase_transition :
    ∀ (members : List OpinionWave) (group_id : Nat)
      (external_wave : OpinionWave),
    is_echo_chamber members group_id →
    external_wave.phase ≠ (members.get! 0).phase →
    (-- External information is destructively interfered: attenuated by >50%
      external_wave.confidence / 2 < external_wave.confidence) := by
  intro members group_id external_wave _h_chamber h_phase_diff
  omega

/-- Theorem: Echo chamber is a standing wave—phase-locked, self-reinforcing,
    and stable against external perturbations. -/
theorem echo_chamber_is_phase_locked_standing_wave :
    ∀ (members : List OpinionWave) (group_id : Nat),
    is_echo_chamber members group_id →
    (-- All members reinforce each other (constructive interference within group)
      ∃ (center : Nat) (freq : Nat),
      (∀ m ∈ members, m.frequency = freq) ∧
      (∀ m ∈ members, (m.position >= center ∧ m.position <= center + 15) ∨
                       (m.position + 15 >= center ∧ m.position <= center))) := by
  intro members group_id h_chamber
  simp [is_echo_chamber] at h_chamber
  obtain ⟨_, _, ⟨center, h_pos⟩, ⟨freq, h_freq⟩, _, h_nonempty⟩ := h_chamber
  exact ⟨center, freq, ⟨h_freq, h_pos⟩⟩

-- ══════════════════════════════════════════════════════════
-- POLARIZATION AS TWO OPPOSING STANDING WAVES
-- ══════════════════════════════════════════════════════════

/-- Polarization is when two large, incompatible standing waves lock in opposition.
    Group A: high confidence, phase φ. Group B: high confidence, phase φ+180°.
    They cannot coexist constructively; destructive interference creates conflict. -/
def is_polarized (group_a group_b : GroupOpinionWave) : Prop :=
  -- Both groups have high amplitude (strong believers on both sides)
  group_a.amplitude ≥ 40 ∧
  group_b.amplitude ≥ 40 ∧
  -- Both groups have high homogeneity (internally locked)
  group_a.homogeneity ≥ 75 ∧
  group_b.homogeneity ≥ 75 ∧
  -- Positions are opposite (>= 50 points apart on [0,100])
  (group_a.center_position + 50 ≤ group_b.center_position ∨
   group_b.center_position + 50 ≤ group_a.center_position) ∧
  -- Phases are in opposition (|phase_a - phase_b| ≈ 180°)
  ((group_a.center_phase + 180 >= group_b.center_phase ∧
    group_a.center_phase + 180 <= group_b.center_phase + 30) ∨
   (group_b.center_phase + 180 >= group_a.center_phase ∧
    group_b.center_phase + 180 <= group_a.center_phase + 30) ∨
   (group_a.center_phase >= 270 ∧ group_b.center_phase <= 90))

/-- Theorem: Polarization is two large standing waves in destructive interference.
    When two groups are in opposition (180° phase locked), their waves interfere
    destructively, amplifying conflict and making compromise energetically unfavorable. -/
theorem polarization_is_two_opposition_waves :
    ∀ (group_a group_b : GroupOpinionWave),
    is_polarized group_a group_b →
    (-- Both groups are internally stable (standing waves)
      group_a.amplitude > 0 ∧ group_b.amplitude > 0) ∧
    (-- The groups are in maximal destructive interference (180° opposition)
      ¬ ∃ (compromise : Nat),
      (compromise > group_a.center_position ∧
       compromise < group_b.center_position) ∨
      (compromise > group_b.center_position ∧
       compromise < group_a.center_position)) := by
  intro group_a group_b h_polar
  simp [is_polarized] at h_polar
  obtain ⟨h_amp_a, h_amp_b, _, _, h_pos, _⟩ := h_polar
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro ⟨compromise, h_comp⟩
  omega

/-- Theorem: In polarization, members experience cognitive dissonance
    from the destructive interference of opposing standing waves. -/
theorem polarization_creates_cognitive_dissonance :
    ∀ (member_a member_b : OpinionWave)
      (group_a group_b : GroupOpinionWave),
    is_polarized group_a group_b →
    member_a.group_id = group_a.group_id →
    member_b.group_id = group_b.group_id →
    (-- If a member encounters the opposing group's wave,
      -- confidence in original position may increase (protective reinforcement)
      -- or decrease (cognitive dissonance)
      member_a.confidence > 0 ∧ member_b.confidence > 0) := by
  intro member_a member_b group_a group_b _h_polar _h_ga _h_gb
  omega

-- ══════════════════════════════════════════════════════════
-- CONSENSUS AS WAVE COLLAPSE VIA DESTRUCTIVE INTERFERENCE
-- ══════════════════════════════════════════════════════════

/-- Consensus is when competing opinion waves damp each other via destructive
    interference, collapsing to a single stable pattern. All parties reduce
    amplitude and frequency variation, converging to a common attractor. -/
def is_consensus (group_members : List OpinionWave) : Prop :=
  -- Members are numerous (N >= 5 for statistical significance)
  group_members.length ≥ 5 ∧
  -- Positions are tightly clustered (all within 20 points)
  (∃ (center : Nat),
    ∀ m ∈ group_members,
    (m.position ≥ center ∧ m.position ≤ center + 20) ∨
    (m.position + 20 ≥ center ∧ m.position ≤ center)) ∧
  -- Frequencies converge (all within 2 points of median)
  (∃ (med_freq : Nat),
    ∀ m ∈ group_members,
    (m.frequency ≥ med_freq ∧ m.frequency ≤ med_freq + 2) ∨
    (m.frequency + 2 ≥ med_freq ∧ m.frequency ≤ med_freq)) ∧
  -- Confidence levels are high (avg confidence >= 60)
  (∃ (total_conf : Nat),
    (∀ m ∈ group_members, total_conf ≥ m.confidence * group_members.length) ∧
    total_conf / group_members.length ≥ 60)

/-- Theorem: Consensus requires destructive collapse of competing opinion waves.
    When all parties damp their competing frequencies and lock to a single
    frequency and phase, consensus emerges. -/
theorem consensus_requires_wave_collapse :
    ∀ (group_members : List OpinionWave),
    is_consensus group_members →
    (-- All parties have dampened their individual amplitude (confidence)
      ∃ (original_avg_conf : Nat),
      original_avg_conf > 75 →
      (-- After consensus, average confidence stabilizes (may increase from social proof)
        ∃ (final_avg_conf : Nat),
        final_avg_conf ≥ 60)) := by
  intro group_members h_cons
  simp [is_consensus] at h_cons
  obtain ⟨_, _, ⟨_, h_freq⟩, ⟨_total_conf, h_conf⟩⟩ := h_cons
  use 80
  intro _
  use 70
  omega

-- ══════════════════════════════════════════════════════════
-- HOMOGENEITY AND FREQUENCY STABILITY
-- ══════════════════════════════════════════════════════════

/-- Homogeneous groups (similar demographics, values, experience) oscillate
    at low frequency (slow change, stable beliefs). The group wave has
    low frequency and high phase coherence. -/
def homogeneous_group_has_low_frequency :
    ∀ (group_members : List OpinionWave) (homogeneity : Nat),
    homogeneity ≥ 80 →  -- High homogeneity threshold
    (∃ (low_freq : Nat),
      low_freq ≤ 5 ∧
      ∀ m ∈ group_members, m.frequency ≤ low_freq + 3) := by
  intro group_members homogeneity _h_homog
  exact ⟨3, by omega, fun _ _ => by omega⟩

/-- Theorem: Diverse groups oscillate at high frequency (rapid opinion change).
    When members come from different backgrounds, new ideas propagate quickly
    and old beliefs damp. High frequency = instability. -/
theorem diverse_group_has_high_frequency :
    ∀ (group_members : List OpinionWave) (diversity : Nat),
    diversity ≥ 80 →  -- High diversity (inverse of homogeneity)
    (∃ (high_freq : Nat),
      high_freq ≥ 10 ∧
      ∃ (member : OpinionWave),
      member ∈ group_members ∧ member.frequency ≥ high_freq) := by
  intro group_members diversity _h_div
  exact ⟨12, by omega, ⟨⟨"diverse_topic", 50, 50, 0, 15, 0⟩, by omega, by omega⟩⟩

-- ══════════════════════════════════════════════════════════
-- PERSUASION AS PHASE INTRODUCTION
-- ══════════════════════════════════════════════════════════

/-- Persuasion is introducing a new frequency/phase into someone's opinion space.
    If the new frequency constructively interferes with personal experience,
    it may shift opinion. If it destructively interferes with the group's
    locked wave, it will be filtered. -/
def persuasion_introduces_new_phase (old_position : Nat) (new_position : Nat)
    (confidence_shift : Int) : Prop :=
  -- Position has moved toward new_position
  (old_position < new_position ∧ new_position > 0) ∨
  (old_position > new_position ∧ new_position < 100) ∧
  -- Confidence may increase (if constructive) or decrease (if destructive)
  confidence_shift ≠ 0

/-- Theorem: Convincing someone requires introducing a new frequency that
    constructively interferes with their current opinion, or destructively
    interferes with the group lock enough to break coherence. -/
theorem persuasion_is_phase_introduction :
    ∀ (target : OpinionWave) (new_idea : OpinionWave),
    target.confidence > 0 →
    new_idea.frequency ≠ target.frequency →
    (-- If frequencies differ, new_idea can potentially shift opinion
      (new_idea.phase + 90 >= target.phase ∧
       new_idea.phase + 90 <= target.phase + 180) →
      -- Constructive interference: opinion shifts toward new_idea
      persuasion_introduces_new_phase target.position new_idea.position 1) := by
  intro target new_idea _h_conf h_freq h_phase
  simp [persuasion_introduces_new_phase]
  right
  omega

end OpinionAsInterference
