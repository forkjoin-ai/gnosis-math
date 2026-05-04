import Init

/-!
  # Finite analogue of Floer / Morse fixed-point counting.

  This module formalizes a tractable, finite shadow of the Lefschetz fixed-point
  principle and the discrete Morse inequalities. It does not touch the Arnold
  conjecture, nor symplectic geometry; it verifies two concrete instances where
  a self-map's fixed-point count meets the topological bound set by the Euler
  characteristic of a small combinatorial space.

  The pattern formalized here maps onto the Lefschetz-style inequality
  `#Fix(f) ≥ |χ(X)|` and onto the discrete Morse inequality
  `#crit_k(f) ≥ β_k(X)` for a particular finite simplicial complex: the
  boundary of a tetrahedron, `∂Δ³`, which is combinatorially a 2-sphere.

  No `sorry`, no new `axiom`, no `native_decide` on non-trivial goals.
-/

namespace FloerFiniteFixedPoints

/-! ### Part 1: Lefschetz-flavored count on a finite discrete space.

    We take `X = Fin n`, viewed as a zero-dimensional discrete space with
    Euler characteristic `n`. For the identity self-map, every point is
    fixed, so `#Fix(id) = n ≥ |χ(X)|` holds with equality.
-/

/-- Number of fixed points of a self-map on `Fin n`, computed by brute search. -/
def fixCount (n : Nat) (f : Fin n → Fin n) : Nat :=
  (List.range n).foldl
    (fun acc k =>
      if h : k < n then
        let i : Fin n := ⟨k, h⟩
        if f i = i then acc + 1 else acc
      else acc)
    0

/-- Euler characteristic of the zero-dimensional discrete space on `Fin n`. -/
def eulerDiscrete (n : Nat) : Nat := n

/-- The identity map on `Fin n`. -/
def idFin (n : Nat) : Fin n → Fin n := fun i => i

/-- Fixed-point count of the identity on `Fin 3` equals 3.
    (Every point is fixed, matching `χ(Fin 3) = 3`.) -/
theorem fix_id_fin3 : fixCount 3 (idFin 3) = 3 := by
  decide

/-- Fixed-point count of the identity on `Fin 5` equals 5. -/
theorem fix_id_fin5 : fixCount 5 (idFin 5) = 5 := by
  decide

/-- Lefschetz-style inequality for the identity on `Fin 3`:
    the number of fixed points is at least the Euler characteristic. -/
theorem lefschetz_id_fin3 : fixCount 3 (idFin 3) ≥ eulerDiscrete 3 := by
  decide

/-- Lefschetz-style inequality for the identity on `Fin 5`. -/
theorem lefschetz_id_fin5 : fixCount 5 (idFin 5) ≥ eulerDiscrete 5 := by
  decide

/-- A concrete non-identity self-map on `Fin 3`: swap `0` and `1`, fix `2`. -/
def swap01Fin3 : Fin 3 → Fin 3 := fun i =>
  match i.val, i.isLt with
  | 0, _ => ⟨1, by decide⟩
  | 1, _ => ⟨0, by decide⟩
  | 2, _ => ⟨2, by decide⟩
  | n + 3, h => absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 n))

/-- The swap-and-fix map on `Fin 3` has exactly one fixed point. -/
theorem fix_swap01_fin3 : fixCount 3 swap01Fin3 = 1 := by
  decide

/-! ### Part 2: Discrete Euler characteristic of `∂Δ³`.

    The boundary of a tetrahedron has 4 vertices, 6 edges, 4 faces, and
    χ = 4 − 6 + 4 = 2, matching the 2-sphere it triangulates. We encode
    each cell count directly and verify the alternating sum.
-/

/-- Cell counts of the boundary of a tetrahedron, indexed by dimension. -/
def tetBoundaryCells : Nat → Nat
  | 0 => 4  -- vertices
  | 1 => 6  -- edges
  | 2 => 4  -- faces
  | _ => 0

/-- Signed Euler characteristic of `∂Δ³` as an `Int`:
    `χ = f₀ − f₁ + f₂`. -/
def tetBoundaryEuler : Int :=
  (tetBoundaryCells 0 : Int) - (tetBoundaryCells 1 : Int) + (tetBoundaryCells 2 : Int)

/-- The Euler characteristic of the tetrahedron boundary is `2`,
    consistent with its role as a combinatorial 2-sphere. -/
theorem tet_boundary_euler_eq_two : tetBoundaryEuler = 2 := by
  decide

/-! ### Part 3: Discrete-Morse-flavored inequality on `∂Δ³`.

    A discrete Morse function on `∂Δ³` can be chosen with exactly one
    critical 0-cell and one critical 2-cell (the canonical Morse function
    on `S²`). For this choice, `#crit_k ≥ β_k` holds cell by cell:
    `β_0 = β_2 = 1`, `β_1 = 0`, and the critical counts above meet or
    exceed each Betti number. We verify the inequalities as concrete facts.
-/

/-- Critical-cell count in dimension `k` for the canonical Morse function
    on `∂Δ³` (one source, one sink). -/
def critCount : Nat → Nat
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | _ => 0

/-- Betti numbers of the 2-sphere `∂Δ³`. -/
def betti : Nat → Nat
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | _ => 0

/-- Discrete Morse inequality in dimension 0 for the chosen function on `∂Δ³`. -/
theorem morse_ineq_dim0 : critCount 0 ≥ betti 0 := by
  decide

/-- Discrete Morse inequality in dimension 1 for the chosen function on `∂Δ³`. -/
theorem morse_ineq_dim1 : critCount 1 ≥ betti 1 := by
  decide

/-- Discrete Morse inequality in dimension 2 for the chosen function on `∂Δ³`. -/
theorem morse_ineq_dim2 : critCount 2 ≥ betti 2 := by
  decide

/-- The alternating sum of critical counts recovers the Euler characteristic
    of `∂Δ³`, witnessing the discrete Morse-theoretic identity
    `χ = Σ (−1)^k · #crit_k`. -/
theorem morse_euler_match :
    (critCount 0 : Int) - (critCount 1 : Int) + (critCount 2 : Int)
      = tetBoundaryEuler := by
  decide

end FloerFiniteFixedPoints
