import Init

/-!
# Emergence from Terminal Attractors

Finite contraction model for terminal-attractor emergence. The module keeps the
claim modest: a structured point has positive distance from vacuum, and a
one-step-to-vacuum path is a monotone contraction witness.

Zero `sorry`, zero new `axiom`, no Mathlib.
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

/-- The contraction distance from a point to vacuum: sum of coordinates. -/
def contraction_distance (p : ChargePoint) : Nat :=
  p.x + p.y + p.z

/-- A configuration is structured when it has positive distance from vacuum. -/
def is_structured (p : ChargePoint) : Prop :=
  0 < contraction_distance p

instance (p : ChargePoint) : Decidable (is_structured p) := by
  unfold is_structured
  exact inferInstance

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

theorem vacuum_distance_zero : contraction_distance vacuum = 0 := by
  rfl

theorem vacuum_not_structured : ¬ is_structured vacuum := by
  intro h
  unfold is_structured at h
  rw [vacuum_distance_zero] at h
  exact Nat.lt_irrefl 0 h

theorem structured_ne_vacuum (p : ChargePoint) (h : is_structured p) :
    p ≠ vacuum := by
  intro hp
  rw [hp] at h
  exact vacuum_not_structured h

theorem structured_positive_distance (p : ChargePoint) (h : is_structured p) :
    0 < contraction_distance p :=
  h

theorem irreducibility_pos_iff_structured (p : ChargePoint) :
    0 < irreducibility p ↔ is_structured p := by
  rfl

theorem structured_has_emergence (p : ChargePoint) (h : is_structured p) :
    0 < emergence_strength p := by
  unfold emergence_strength
  exact h

theorem contraction_transitive (p q r : ChargePoint)
    (h1 : q.x ≤ p.x ∧ q.y ≤ p.y ∧ q.z ≤ p.z)
    (h2 : r.x ≤ q.x ∧ r.y ≤ q.y ∧ r.z ≤ q.z) :
    r.x ≤ p.x ∧ r.y ≤ p.y ∧ r.z ≤ p.z := by
  exact ⟨Nat.le_trans h2.1 h1.1,
    Nat.le_trans h2.2.1 h1.2.1,
    Nat.le_trans h2.2.2 h1.2.2⟩

/-- For every positive complexity level, there is a structured point at exactly that distance. -/
theorem emergence_from_vacuum_pull :
    ∀ (complexity_level : Nat),
    0 < complexity_level →
    ∃ system : ChargePoint,
      contraction_distance system = complexity_level ∧
      is_structured system := by
  intro complexity_level hpositive
  refine ⟨⟨complexity_level, 0, 0⟩, ?_, ?_⟩
  · rfl
  · exact hpositive

/-- Organization is measured by irreducible distance to the terminal state. -/
theorem order_from_irreducibility_not_randomness :
    ∀ p : ChargePoint,
      is_structured p →
      ∃ path : Nat → ChargePoint,
        path 0 = p ∧
        path (irreducibility p) = vacuum ∧
        contraction_distance (path (irreducibility p)) = 0 ∧
        ∀ i : Nat, i < irreducibility p →
          contraction_distance (path (i + 1)) ≤ contraction_distance (path i) := by
  intro p hstructured
  let path : Nat → ChargePoint := fun i => if i = 0 then p else vacuum
  refine ⟨path, ?_, ?_, ?_, ?_⟩
  · simp [path]
  · have hirrPositive : 0 < irreducibility p := hstructured
    have hirrNe : irreducibility p ≠ 0 := Nat.ne_of_gt hirrPositive
    simp [path, hirrNe]
  · have hirrPositive : 0 < irreducibility p := hstructured
    have hirrNe : irreducibility p ≠ 0 := Nat.ne_of_gt hirrPositive
    simp [path, hirrNe, vacuum_distance_zero]
  · intro i _hi
    cases i with
    | zero =>
        simp [path, vacuum_distance_zero]
    | succ i =>
        simp [path, vacuum_distance_zero]

/-- Complexity is precisely irreducibility in this finite contraction model. -/
theorem complexity_equals_irreducibility (p : ChargePoint) (_h : is_structured p) :
    emergence_strength p = contraction_distance p := by
  rfl

/-- The emergence game is persistence under terminal-attractor contraction. -/
theorem emergence_is_persistence_game (p : ChargePoint) (h : is_structured p) :
    0 < emergence_strength p ∧
    emergence_strength p = contraction_distance p ∧
    ∃ path : Nat → ChargePoint,
      path 0 = p ∧
      path (emergence_strength p) = vacuum ∧
      ∀ i : Nat, i < emergence_strength p →
        contraction_distance (path (i + 1)) ≤ contraction_distance (path i) := by
  obtain ⟨path, hstart, hend, _hdist, hmono⟩ :=
    order_from_irreducibility_not_randomness p h
  refine ⟨structured_has_emergence p h, complexity_equals_irreducibility p h, ?_⟩
  refine ⟨path, hstart, ?_, ?_⟩
  · unfold emergence_strength
    exact hend
  · intro i hi
    unfold emergence_strength at hi
    exact hmono i hi

end EmergenceFromTerminalAttractors
end Gnosis
