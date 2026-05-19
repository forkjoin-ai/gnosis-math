import Std

/-!
# Emergence from Terminal Attractors

This module models terminal-attractor contraction in a deliberately small
Nat-valued charge space. The constructive witnesses keep the theory honest:
structured systems have positive distance from the vacuum, and the same
distance measures their irreducibility and emergence strength.

Zero sorry. Zero axioms.
-/

namespace Gnosis
namespace EmergenceFromTerminalAttractors

/-- A point in charge-face space. The terminal state is `(0, 0, 0)`. -/
structure ChargePoint where
  x : Nat
  y : Nat
  z : Nat
deriving DecidableEq, Repr

/-- The vacuum terminal state. -/
def vacuum : ChargePoint := ⟨0, 0, 0⟩

/-- The contraction distance from a point to vacuum. -/
def contraction_distance (p : ChargePoint) : Nat :=
  p.x + p.y + p.z

/-- A configuration is structured when it has positive distance from vacuum. -/
def is_structured (p : ChargePoint) : Prop :=
  0 < contraction_distance p

/-- A contraction step never increases charge and either holds position or reaches vacuum. -/
def is_contraction_step (source target : ChargePoint) : Prop :=
  (target.x ≤ source.x ∧ target.y ≤ source.y ∧ target.z ≤ source.z) ∧
  (target = source ∨ target = vacuum)

/-- A contraction path starts at an initial point, ends at vacuum, and never increases distance. -/
structure ContractPath (initial : ChargePoint) (steps : Nat) where
  path : Nat → ChargePoint
  start_eq : path 0 = initial
  end_vacuum : path steps = vacuum
  contracts_monotonically : ∀ i : Nat, i < steps →
    contraction_distance (path (i + 1)) ≤ contraction_distance (path i)

/-- The irreducibility of a system is its contraction distance. -/
def irreducibility (p : ChargePoint) : Nat :=
  contraction_distance p

/-- Emergence strength follows irreducibility in this finite model. -/
def emergence_strength (p : ChargePoint) : Nat :=
  irreducibility p

/-- The vacuum state has zero contraction distance. -/
theorem vacuum_distance_zero : contraction_distance vacuum = 0 := by
  rfl

/-- Vacuum is not structured. -/
theorem vacuum_not_structured : ¬is_structured vacuum := by
  unfold is_structured
  simp [vacuum_distance_zero]

/-- All structured points are not vacuum. -/
theorem structured_ne_vacuum (p : ChargePoint) (h : is_structured p) :
    p ≠ vacuum := by
  intro eq
  rw [eq] at h
  exact vacuum_not_structured h

/-- A structured point has positive distance to vacuum. -/
theorem structured_positive_distance (p : ChargePoint) (h : is_structured p) :
    0 < contraction_distance p := by
  exact h

/-- Irreducibility is positive iff the point is structured. -/
theorem irreducibility_pos_iff_structured (p : ChargePoint) :
    0 < irreducibility p ↔ is_structured p := by
  rfl

/-- Every structured point has positive emergence strength. -/
theorem structured_has_emergence (p : ChargePoint) (h : is_structured p) :
    0 < emergence_strength p := by
  exact h

/-- Coordinate-wise contraction is transitive. -/
theorem contraction_transitive (p q r : ChargePoint)
    (h1 : q.x ≤ p.x ∧ q.y ≤ p.y ∧ q.z ≤ p.z)
    (h2 : r.x ≤ q.x ∧ r.y ≤ q.y ∧ r.z ≤ q.z) :
    r.x ≤ p.x ∧ r.y ≤ p.y ∧ r.z ≤ p.z := by
  omega

/-- For every positive complexity level there is a structured system at exactly
that contraction distance, and any long enough horizon admits a monotone path
to the vacuum. -/
theorem emergence_from_vacuum_pull :
    ∀ (complexity_level : Nat),
    0 < complexity_level →
    ∃ (system : ChargePoint),
      is_structured system ∧
      contraction_distance system = complexity_level ∧
      ∀ (path_length : Nat),
        path_length ≥ complexity_level →
        ∃ (path : Nat → ChargePoint),
          path 0 = system ∧
          path path_length = vacuum ∧
          ∀ i : Nat, i < path_length →
            contraction_distance (path (i + 1)) ≤ contraction_distance (path i) ∧
            (contraction_distance (path i) = 0 → path (i + 1) = vacuum) := by
  intro complexity_level hpositive
  refine Exists.intro ⟨complexity_level, 0, 0⟩ ?_
  constructor
  · exact hpositive
  constructor
  · simp [contraction_distance]
  · intro path_length hlen
    let path : Nat → ChargePoint := fun i =>
      if i = 0 then ⟨complexity_level, 0, 0⟩ else vacuum
    refine Exists.intro path ?_
    constructor
    · simp [path]
    constructor
    · have hpath_positive : 0 < path_length := Nat.lt_of_lt_of_le hpositive hlen
      simp [path, Nat.ne_of_gt hpath_positive]
    · intro i _hi
      constructor
      · by_cases hzero : i = 0
        · subst i
          simp [path, contraction_distance, vacuum]
        · simp [path, hzero, contraction_distance, vacuum]
      · intro hdist
        by_cases hzero : i = 0
        · subst i
          simp [path, contraction_distance] at hdist
          omega
        · simp [path, hzero]

/-- Organization is measured by the irreducible distance to the terminal state. -/
theorem order_from_irreducibility_not_randomness :
    ∀ (p : ChargePoint),
      is_structured p →
      emergence_strength p = contraction_distance p := by
  intro _p _hstructured
  rfl

/-- Complexity is precisely irreducibility in this finite contraction model. -/
theorem complexity_equals_irreducibility (p : ChargePoint) (_h : is_structured p) :
    emergence_strength p = contraction_distance p := by
  rfl

/-- The emergence game is persistence under terminal-attractor contraction. -/
theorem emergence_is_persistence_game (p : ChargePoint) (h : is_structured p) :
    0 < emergence_strength p ∧
    emergence_strength p = contraction_distance p ∧
    ∃ (path : Nat → ChargePoint),
      path 0 = p ∧
      path (emergence_strength p) = vacuum ∧
      ∀ i : Nat, i < emergence_strength p →
        is_contraction_step (path i) (path (i + 1)) := by
  constructor
  · exact structured_has_emergence p h
  constructor
  · exact complexity_equals_irreducibility p h
  · let path : Nat → ChargePoint := fun i => if i = 0 then p else vacuum
    refine Exists.intro path ?_
    constructor
    · simp [path]
    constructor
    · have hpos : 0 < emergence_strength p := structured_has_emergence p h
      simp [path, Nat.ne_of_gt hpos]
    · intro i _hi
      unfold is_contraction_step
      constructor
      · by_cases hzero : i = 0
        · subst i
          simp [path, vacuum]
        · simp [path, hzero, vacuum]
      · by_cases hzero : i = 0
        · subst i
          simp [path, vacuum]
        · simp [path, hzero]

end EmergenceFromTerminalAttractors
end Gnosis
