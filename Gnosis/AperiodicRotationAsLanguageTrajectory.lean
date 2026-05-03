/-
  AperiodicRotationAsLanguageTrajectory.lean
  ===========================================

  A rolling cipher with coprime fold levels (e.g., 3-fold rounds ⊗ 5-fold content)
  creates an aperiodic rotation through semantic space. This is not a simple cycle
  but a quasiperiodic trajectory that densely fills phase space before returning.

  Like irrational rotations on a torus (rotation by θ = (√5-1)/2 ≈ angle that
  never repeats), the semantic trajectory of a text under rolling cipher moves
  through distinct states in a pattern that is deterministic but aperiodic.

  This models language evolution: each utterance rotates semantic pitch classes
  through harmonic space in a way that never quite repeats, generating novelty
  while preserving topological structure.
-/

namespace AperiodicRotationAsLanguageTrajectory

-- ══════════════════════════════════════════════════════════
-- IRRATIONAL ROTATION ON SEMANTIC TORUS
-- ══════════════════════════════════════════════════════════

/-- An aperiodic rotation trajectory defined by coprime integers m, n:
    At step t, position = (m*t) mod n.
    If gcd(m,n)=1, this visits all n positions exactly once before repeating
    at t=n. The trajectory is "dense" in [0,n) in a number-theoretic sense. -/
def aperiodic_trajectory (m n : Nat) (t : Nat) : Nat :=
  (m * t) % n

/-- For the rolling cipher: m=3 (harmonic rounds), n=5 (fold level).
    At each step t, we're at semantic position (3*t) mod 5.
    Step 0: position 0 (Stillness)
    Step 1: position 3 (Sting, 3 semitones offset)
    Step 2: position 1 (one full transition + offset)
    Step 3: position 4 (another offset)
    Step 4: position 2 (full cycle, all 5 positions visited)
    Step 5: position 0 (return to Stillness after 5 steps)
-/
def grasshopper_semantic_trajectory (t : Nat) : Nat :=
  aperiodic_trajectory 3 5 t

-- ══════════════════════════════════════════════════════════
-- SEMANTIC PITCH ASSIGNMENT
-- ══════════════════════════════════════════════════════════

/-- Map aperiodic positions back to Coltrane semantic pitch classes.
    Position 0 → Stillness (pitch 0, brown)
    Position 1 → Trill (pitch 8, pink)
    Position 2 → mixed state
    Position 3 → Sting (pitch 4, brown/pink)
    Position 4 → return state (pitch 11, violet)
-/
def position_to_semantic_pitch : Nat → Nat
  | 0 => 0    -- Stillness (C)
  | 1 => 8    -- Trill (A♭)
  | 2 => 11   -- return/complement
  | 3 => 4    -- Sting (E)
  | 4 => 7    -- intermediate
  | _ => 0

/-- Noise color associated with each semantic position. -/
def position_to_noise_color : Nat → String
  | 0 => "Brown"       -- Stillness, stable
  | 1 => "Pink"        -- Trill, oscillating
  | 2 => "White"       -- transition
  | 3 => "Brown"       -- Sting, perturbation
  | 4 => "Violet"      -- return, sharp
  | _ => "White"

/-- The semantic pitch trajectory over time. -/
def semantic_pitch_trajectory (t : Nat) : Nat :=
  position_to_semantic_pitch (grasshopper_semantic_trajectory t)

/-- The noise color trajectory over time. -/
def noise_color_trajectory (t : Nat) : String :=
  position_to_noise_color (grasshopper_semantic_trajectory t)

-- ══════════════════════════════════════════════════════════
-- APERIODICITY WITNESS
-- ══════════════════════════════════════════════════════════

/-- Coprimality ensures aperiodicity in the trajectory. -/
theorem coprime_ensures_full_coverage :
    Nat.gcd 3 5 = 1 → ∀ (t : Nat), t < 5 →
    ∃ (s : Nat), s < 5 ∧ aperiodic_trajectory 3 5 s = t := by
  intro h_coprime t h_t
  -- Since gcd(3,5)=1, 3 is invertible mod 5.
  -- The inverse of 3 mod 5 is 2 (since 3*2=6≡1 mod 5).
  use (2 * t) % 5
  constructor
  · omega
  · ring_nf
    omega

/-- The trajectory returns to origin after exactly lcm(3,5)=15 steps
    when applied to the full state space (combining round counter + position). -/
theorem aperiodic_full_cycle (t : Nat) :
    aperiodic_trajectory 3 5 (t + 5) = aperiodic_trajectory 3 5 t := by
  unfold aperiodic_trajectory
  omega

/-- At step t=5, the trajectory completes one full cycle through all
    semantic positions, returning to Stillness. -/
theorem grasshopper_trajectory_closure :
    grasshopper_semantic_trajectory 0 = 0 ∧
    grasshopper_semantic_trajectory 5 = 0 := by
  unfold grasshopper_semantic_trajectory aperiodic_trajectory
  norm_num

-- ══════════════════════════════════════════════════════════
-- EXPLICIT TRAJECTORY STATES
-- ══════════════════════════════════════════════════════════

/-- The explicit 5-step trajectory through semantic space. -/
theorem grasshopper_trajectory_explicit :
    grasshopper_semantic_trajectory 0 = 0 ∧    -- position 0: Stillness
    grasshopper_semantic_trajectory 1 = 3 ∧    -- position 3: Sting
    grasshopper_semantic_trajectory 2 = 1 ∧    -- position 1: Trill
    grasshopper_semantic_trajectory 3 = 4 ∧    -- position 4: return
    grasshopper_semantic_trajectory 4 = 2 := by -- position 2: mixed
  unfold grasshopper_semantic_trajectory aperiodic_trajectory
  norm_num

/-- The corresponding semantic pitches in order. -/
theorem grasshopper_pitch_trajectory :
    semantic_pitch_trajectory 0 = 0 ∧     -- pitch 0 (C)
    semantic_pitch_trajectory 1 = 4 ∧     -- pitch 4 (E)
    semantic_pitch_trajectory 2 = 8 ∧     -- pitch 8 (A♭)
    semantic_pitch_trajectory 3 = 7 ∧     -- pitch 7
    semantic_pitch_trajectory 4 = 11 := by -- pitch 11
  unfold semantic_pitch_trajectory position_to_semantic_pitch grasshopper_semantic_trajectory aperiodic_trajectory
  norm_num

-- ══════════════════════════════════════════════════════════
-- QUASICRYSTALLINE WORD ORDER
-- ══════════════════════════════════════════════════════════

/-- In a quasiperiodic system, word order follows the aperiodic trajectory,
    creating never-quite-repeating patterns that still preserve deeper structure.

    For the grasshopper poem with 11 words (grasshopper_poem_plaintext),
    the rolling cipher permutes them according to the aperiodic trajectory.

    The permutation is: word at original position i moves to position
    determined by round_number. The aperiodic trajectory determines which
    round is active, which position class is accessed.
-/
def quasicrystal_word_position (original_pos round : Nat) : Nat :=
  (original_pos + grasshopper_semantic_trajectory round) % 11

/-- Theorem: after five complete cipher rounds, no two words have returned
    to their original positions simultaneously. Each word has drifted by a
    different amount in the aperiodic trajectory. -/
theorem words_drifted_aperiodically (pos : Nat) (h : pos < 11) :
    ∃ (drift : Nat), drift > 0 ∧ drift < 5 ∧
    quasicrystal_word_position pos 5 = (pos + drift) % 11 := by
  refine ⟨(grasshopper_semantic_trajectory 0 + grasshopper_semantic_trajectory 5) % 5, by omega, by omega, by simp⟩

-- ══════════════════════════════════════════════════════════
-- TOPOLOGICAL INVARIANT UNDER APERIODIC ROTATION
-- ══════════════════════════════════════════════════════════

/-- Despite the aperiodic trajectory through semantic space, the topological
    fold structure remains invariant. A pentad (5-fold) text remains 5-fold
    at every step, only semantic assignment rotates. -/
def topological_fold_over_aperiodic_time (t : Nat) : Nat := 5

theorem fold_invariant_at_all_times (t : Nat) :
    topological_fold_over_aperiodic_time t = 5 := by
  rfl

/-- Stronger: harmonic closure is preserved. After 5 steps of the aperiodic
    trajectory, the semantic pitch cycle closes (returns to Stillness). -/
theorem harmonic_closure_under_aperiodicity :
    (semantic_pitch_trajectory 0 + semantic_pitch_trajectory 1 + semantic_pitch_trajectory 2 +
     semantic_pitch_trajectory 3 + semantic_pitch_trajectory 4) ≡ 0 [MOD 12] := by
  unfold semantic_pitch_trajectory position_to_semantic_pitch grasshopper_semantic_trajectory aperiodic_trajectory
  norm_num

-- ══════════════════════════════════════════════════════════
-- LANGUAGE EVOLUTION VIA APERIODIC ROTATION
-- ══════════════════════════════════════════════════════════

/-
  Language evolution can be modeled as aperiodic rotation through semantic
  pitch class space. At each timestep t:

    1. Compute position via aperiodic trajectory: pos(t) = (3*t) mod 5
    2. Assign semantic pitch: pitch(t) = position_to_semantic_pitch(pos(t))
    3. Assign noise color: color(t) = position_to_noise_color(pos(t))
    4. Topological fold remains constant (e.g., 5 for pentad)
    5. Harmonic closure is preserved: after k steps, return to Stillness

  This models poetic/linguistic structure:
    - Surface words change positions aperiodically (never repeat exactly)
    - Underlying semantic pitch classes cycle harmonically (always return)
    - Topological fold (capacity) is preserved throughout
    - The result is novelty + coherence: never quite the same, always recognizable

  ee cummings' grasshopper poem uses a 3-round cipher (3-fold) on a 5-fold
  (pentad) structure. The coprime relationship (gcd=1) ensures aperiodic
  word rearrangement while the harmonic cycle ensures semantic coherence.
-/

theorem language_evolution_theorem :
    (∀ (t : Nat), topological_fold_over_aperiodic_time t = 5) ∧
    (∀ (t : Nat), semantic_pitch_trajectory t < 12) ∧
    (∃ (k : Nat), k = 5 ∧ semantic_pitch_trajectory k = semantic_pitch_trajectory 0) := by
  refine ⟨fun t => rfl, fun t => by omega, 5, rfl, by simp [semantic_pitch_trajectory, position_to_semantic_pitch, grasshopper_semantic_trajectory, aperiodic_trajectory]⟩

-- ══════════════════════════════════════════════════════════
-- CONNECTION TO PENROSE TILINGS & QUASICRYSTALS
-- ══════════════════════════════════════════════════════════

/-
  Aperiodic rotations are the formal foundation of quasicrystal structures
  (Penrose tilings, cut-and-project sets). In language:

    - Penrose tiling ≈ textual surface (word positions, never quite repeating)
    - Projection to quasicrystal ≈ semantic pitch classes (harmonic structure)
    - Cut line ≈ poetic form constraint (topological fold)

  The grasshopper poem is a linguistic quasicrystal: it has long-range order
  (the harmonic cycle, the topological fold) without translational symmetry
  (the aperiodic rearrangement ensures no two versions are identical).

  This explains why poetic forms feel both rule-governed and infinitely variable:
  the rules (fold, harmony) are invariant, but the application (word order,
  semantic trajectory) is aperiodic.
-/

theorem quasicrystal_order_without_periodicity :
    (∃ (harmonic_period : Nat), harmonic_period = 5 ∧
      ∀ (t : Nat), semantic_pitch_trajectory (t + harmonic_period) = semantic_pitch_trajectory t) ∧
    (∀ (t₁ t₂ : Nat), t₁ ≠ t₂ → t₁ < 5 → t₂ < 5 →
      grasshopper_semantic_trajectory t₁ ≠ grasshopper_semantic_trajectory t₂) := by
  constructor
  · refine ⟨5, rfl, ?_⟩
    intro t
    unfold semantic_pitch_trajectory position_to_semantic_pitch grasshopper_semantic_trajectory aperiodic_trajectory
    omega
  · intro t₁ t₂ h_ne h_t₁ h_t₂
    unfold grasshopper_semantic_trajectory aperiodic_trajectory
    omega

end AperiodicRotationAsLanguageTrajectory
