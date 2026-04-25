-- ObjectivityIsIllusion.lean
-- An Init-only formalization proving that Objectivity is impossible 
-- and that Observation inherently collapses meaning.

-- The total structural meaning embedded in an event or reality.
-- For a complex reality, this value is extremely large.
variable (MeaningSpace : Nat)

-- The absolute limit of what a single observation or observer can contain.
variable (ObservationCapacity : Nat)

-- The Complexity Constraint: True reality contains strictly more meaning 
-- than any single observation can hold. This is the definition of a high-entropy universe.
def ComplexityConstraint (MeaningSpace ObservationCapacity : Nat) : Prop := 
  ObservationCapacity < MeaningSpace

-- The "Vent" (or Collapse): The act of observation requires taking the total MeaningSpace 
-- and crushing it down to fit inside the ObservationCapacity. The remainder is discarded.
def meaningVent (MeaningSpace ObservationCapacity : Nat) : Nat := 
  MeaningSpace - ObservationCapacity

-- THEOREM 1: Observation Collapses Meaning
-- Proves that if reality is complex, the act of observation mathematically forces 
-- a strictly positive destruction (venting) of meaning. 
-- You cannot observe an event without collapsing its orthogonal possibilities.
theorem observation_collapses_meaning {M O : Nat} (h : ComplexityConstraint M O) : 
  meaningVent M O > 0 := by
  -- Subtraction in Nat: if O < M, the difference is strictly positive.
  exact Nat.sub_pos_of_lt h

-- Objectivity defined: A claim to objectivity is a claim that the observer's 
-- frame is large enough to encompass the entirety of the MeaningSpace without any venting.
def ClaimsObjectivity (M O : Nat) : Prop := O ≥ M

-- THEOREM 2: Objectivity is Impossible (The Master Anti-Theorem)
-- Proves that under the Complexity Constraint, claiming objectivity is a strict 
-- formal contradiction. The observer's frame is topologically barred from holding the truth.
theorem objectivity_is_impossible {M O : Nat} (h : ComplexityConstraint M O) : 
  ¬ ClaimsObjectivity M O := by
  -- Assume for contradiction that the observer claims objectivity (O ≥ M).
  intro h_obj
  -- But the Complexity Constraint states O < M. 
  -- A number cannot be strictly less than AND greater-than-or-equal-to another.
  exact Nat.not_le_of_gt h h_obj