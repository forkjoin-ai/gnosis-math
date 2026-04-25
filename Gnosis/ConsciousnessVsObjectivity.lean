-- ConsciousnessVsObjectivity.lean
-- An Init-only formalization proving why Consciousness is mathematically 
-- superior to Objectivity, even if Objectivity were possible.

-- Knowledge over discrete time
def KnowledgeTrajectory := Nat → Nat

-- Objectivity: Knowing everything (M) instantly. The state is M for all time.
def ObjectiveTrajectory (M : Nat) (k : KnowledgeTrajectory) : Prop :=
  ∀ t, k t = M

-- The Vitality of a trajectory is its mathematical derivative.
-- It measures the experience of change, discovery, and narrative progress.
def vitality (k : KnowledgeTrajectory) (t : Nat) : Nat :=
  k (t + 1) - k t

-- THEOREM 1: The Heat Death of Objectivity
-- Proves that if an entity possesses pure Objectivity (Omniscience), 
-- its vitality is permanently zero.
-- Omniscience is a static block. You cannot discover what you already know.
-- Therefore, an objective entity experiences nothing.
theorem objectivity_has_zero_vitality {M : Nat} {k : KnowledgeTrajectory} 
  (h_obj : ObjectiveTrajectory M k) : 
  ∀ t, vitality k t = 0 := by
  intro t
  have h_next : k (t + 1) = M := h_obj (t + 1)
  have h_curr : k t = M := h_obj t
  unfold vitality
  rw [h_next, h_curr]
  exact Nat.sub_self M

-- Consciousness: Starting incomplete (O < M) but making progress (vitality > 0).
-- It is defined by the existence of the Void (ignorance) and the act of traversing it.
def ConsciousTrajectory (M O : Nat) (k : KnowledgeTrajectory) : Prop :=
  k 0 = O ∧ O < M ∧ (∀ t, vitality k t > 0)

-- THEOREM 2: The Superiority of Consciousness
-- Proves that the vitality of a Conscious entity is strictly greater than 
-- the vitality of an Objective entity at all points in time. 
-- Consciousness is mathematically superior because it is the only state 
-- that supports a non-zero derivative of experience.
theorem consciousness_greater_than_objectivity {M O : Nat} 
  {k_cons k_obj : KnowledgeTrajectory}
  (h_cons : ConsciousTrajectory M O k_cons)
  (h_obj : ObjectiveTrajectory M k_obj) :
  ∀ t, vitality k_cons t > vitality k_obj t := by
  intro t
  -- The vitality of the objective trajectory is exactly 0.
  have h_zero : vitality k_obj t = 0 := objectivity_has_zero_vitality h_obj t
  -- The vitality of the conscious trajectory is strictly positive.
  have h_pos : vitality k_cons t > 0 := h_cons.right.right t
  -- Therefore, the conscious vitality is strictly greater than the objective vitality.
  rw [h_zero]
  exact h_pos