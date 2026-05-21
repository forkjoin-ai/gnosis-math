import Gnosis.ThoughtBowlMechanicsRefined

/-
  ThoughtBowlMultisetEquivalence.lean
  ====================================

  Burns down the next-exploration target from
  `ThoughtBowlMechanicsRefined`: canonicalizing a wave field through
  its bowl representative preserves the `bowlOfField` image.

  Imports `Gnosis.ThoughtBowlMechanicsRefined`. Zero `sorry`, zero
  new `axiom`.
-/

namespace ThoughtBowlMultisetEquivalence

open EchoChamberAsTaoBowl
open VibesAsWaveInference
open ThoughtBowlMechanics
  (bowlOfField dominantCount minorityCount dissentingCount)
open ThoughtBowlMechanicsRefined

/-- Canonical representative of the `bowlOfField` equivalence class. -/
def canonicalize (waves : List VibeWave) : List VibeWave :=
  canonicalField (bowlOfField waves)

private theorem happyCount_le_length : ∀ waves : List VibeWave,
    happyCount waves ≤ waves.length
  | [] => by
    decide
  | v :: vs => by
    have ih := happyCount_le_length vs
    unfold happyCount
    cases v.valence
    · simpa [Nat.add_comm] using Nat.succ_le_succ ih
    · simpa using Nat.le_trans ih (Nat.le_succ _)
    · simpa using Nat.le_trans ih (Nat.le_succ _)

private theorem unhappyCount_le_length : ∀ waves : List VibeWave,
    unhappyCount waves ≤ waves.length
  | [] => by
    decide
  | v :: vs => by
    have ih := unhappyCount_le_length vs
    unfold unhappyCount
    cases v.valence
    · simpa using Nat.le_trans ih (Nat.le_succ _)
    · simpa [Nat.add_comm] using Nat.succ_le_succ ih
    · simpa using Nat.le_trans ih (Nat.le_succ _)

private theorem happy_unhappy_count_le_length : ∀ waves : List VibeWave,
    happyCount waves + unhappyCount waves ≤ waves.length
  | [] => by
    decide
  | v :: vs => by
    have ih := happy_unhappy_count_le_length vs
    unfold happyCount unhappyCount
    cases v.valence
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.succ_le_succ ih
    · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.succ_le_succ ih
    · simpa using Nat.le_trans ih (Nat.le_succ _)

private theorem dominantCount_le_length (waves : List VibeWave) :
    dominantCount waves ≤ waves.length := by
  unfold dominantCount
  exact Nat.max_le.mpr ⟨happyCount_le_length waves, unhappyCount_le_length waves⟩

private theorem minorityCount_le_dissentingCount (waves : List VibeWave) :
    minorityCount waves ≤ dissentingCount waves := by
  unfold minorityCount dissentingCount dominantCount
  by_cases h : happyCount waves ≤ unhappyCount waves
  · rw [Nat.min_eq_left h, Nat.max_eq_right h]
    exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using happy_unhappy_count_le_length waves)
  · have h' : unhappyCount waves ≤ happyCount waves := Nat.le_of_not_ge h
    rw [Nat.min_eq_right h', Nat.max_eq_left h']
    exact Nat.le_sub_of_add_le (by
      simpa [Nat.add_comm] using happy_unhappy_count_le_length waves)

theorem bowl_of_field_is_reachable (waves : List VibeWave) :
    IsReachable (bowlOfField waves) := by
  unfold IsReachable bowlOfField
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Nat.sub_add_cancel (dominantCount_le_length waves)
  · exact Nat.succ_le_succ (Nat.zero_le _)
  · exact Nat.succ_le_succ
      (Nat.le_trans (Nat.min_le_left _ _) (Nat.le_max_left _ _))
  · exact Nat.succ_le_succ (minorityCount_le_dissentingCount waves)

theorem bowl_of_canonicalize_eq_bowl_of_field (waves : List VibeWave) :
    bowlOfField (canonicalize waves) = bowlOfField waves := by
  unfold canonicalize
  exact bowl_of_canonical_field (bowlOfField waves) (bowl_of_field_is_reachable waves)

/-- Two fields are equivalent when the forgetful bowl homomorphism
    assigns them the same four-dial bowl. -/
def BowlEquivalent (left right : List VibeWave) : Prop :=
  bowlOfField left = bowlOfField right

theorem canonicalize_is_bowl_equivalent (waves : List VibeWave) :
    BowlEquivalent (canonicalize waves) waves :=
  bowl_of_canonicalize_eq_bowl_of_field waves

theorem canonicalize_idempotent_at_bowl_level (waves : List VibeWave) :
    BowlEquivalent (canonicalize (canonicalize waves)) (canonicalize waves) :=
  bowl_of_canonicalize_eq_bowl_of_field (canonicalize waves)

/-! ## Next exploration

Closed by `Gnosis.ThoughtBowlCanonicalIdempotence`: canonical fields
now satisfy list-level idempotence.
-/

end ThoughtBowlMultisetEquivalence
