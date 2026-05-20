import Init

/-!
# Triton carrier and Fano incidence

The carrier is the three-bit binary cube `Fin 8`.

* `000` is `godPosition`: the additive identity and root node outside the
  visible projective system.
* the seven Fano points are the nonzero carrier states `001..111`.
* collision is bitwise XOR.
* self-collision exits the visible system back to `godPosition`.
* distinct visible collisions close inside the Fano plane.
-/

namespace Gnosis
namespace FanoIncidence

/-- The full three-bit carrier. Values `0..7` read as binary `000..111`. -/
abbrev TritonState := Fin 8

/-- The root/outside-system position: binary `000`. -/
def godPosition : TritonState :=
  ⟨0, by decide⟩

/-- Visible/projective states are precisely non-root Triton states. -/
def visible (x : TritonState) : Prop :=
  x ≠ godPosition

/-- Three-bit XOR as a table on `0..7`. Inputs outside that range collapse to
`0`; `TritonState` callers never reach those fallback arms. -/
def xorNat : Nat → Nat → Nat
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 2
  | 0, 3 => 3
  | 0, 4 => 4
  | 0, 5 => 5
  | 0, 6 => 6
  | 0, 7 => 7
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 3
  | 1, 3 => 2
  | 1, 4 => 5
  | 1, 5 => 4
  | 1, 6 => 7
  | 1, 7 => 6
  | 2, 0 => 2
  | 2, 1 => 3
  | 2, 2 => 0
  | 2, 3 => 1
  | 2, 4 => 6
  | 2, 5 => 7
  | 2, 6 => 4
  | 2, 7 => 5
  | 3, 0 => 3
  | 3, 1 => 2
  | 3, 2 => 1
  | 3, 3 => 0
  | 3, 4 => 7
  | 3, 5 => 6
  | 3, 6 => 5
  | 3, 7 => 4
  | 4, 0 => 4
  | 4, 1 => 5
  | 4, 2 => 6
  | 4, 3 => 7
  | 4, 4 => 0
  | 4, 5 => 1
  | 4, 6 => 2
  | 4, 7 => 3
  | 5, 0 => 5
  | 5, 1 => 4
  | 5, 2 => 7
  | 5, 3 => 6
  | 5, 4 => 1
  | 5, 5 => 0
  | 5, 6 => 3
  | 5, 7 => 2
  | 6, 0 => 6
  | 6, 1 => 7
  | 6, 2 => 4
  | 6, 3 => 5
  | 6, 4 => 2
  | 6, 5 => 3
  | 6, 6 => 0
  | 6, 7 => 1
  | 7, 0 => 7
  | 7, 1 => 6
  | 7, 2 => 5
  | 7, 3 => 4
  | 7, 4 => 3
  | 7, 5 => 2
  | 7, 6 => 1
  | 7, 7 => 0
  | _, _ => 0

/-- Three-bit XOR on the Triton carrier. -/
def tritonXor (a b : TritonState) : TritonState :=
  ⟨xorNat a.val b.val % 8, Nat.mod_lt _ (by decide)⟩

/-- Collision in the Triton carrier is binary XOR. -/
def collide : TritonState → TritonState → TritonState :=
  tritonXor

theorem godPosition_left_identity (x : TritonState) :
    collide godPosition x = x := by
  revert x
  native_decide

theorem godPosition_right_identity (x : TritonState) :
    collide x godPosition = x := by
  revert x
  native_decide

theorem self_collision_exits_to_godPosition (x : TritonState) :
    collide x x = godPosition := by
  revert x
  native_decide

/-- The seven visible points of the Fano plane, named by their nonzero
three-bit carrier states. -/
inductive FanoPoint
  | b001 | b010 | b011 | b100 | b101 | b110 | b111
  deriving DecidableEq, Repr

open FanoPoint

/-- Interpret a Fano point as its nonzero Triton carrier state. -/
def FanoPoint.state : FanoPoint → TritonState
  | b001 => ⟨1, by decide⟩
  | b010 => ⟨2, by decide⟩
  | b011 => ⟨3, by decide⟩
  | b100 => ⟨4, by decide⟩
  | b101 => ⟨5, by decide⟩
  | b110 => ⟨6, by decide⟩
  | b111 => ⟨7, by decide⟩

instance : Coe FanoPoint TritonState where
  coe p := p.state

theorem fanoPoint_visible (p : FanoPoint) :
    visible p.state := by
  cases p <;> simp [visible, godPosition, FanoPoint.state]

/-- Numerical address for embedding Fano points into larger finite carriers.
The address is the nonzero three-bit value minus one, so visible states
`001..111` map to columns `0..6`. -/
def pointIndex (p : FanoPoint) : Nat :=
  match p with
  | b001 => 0
  | b010 => 1
  | b011 => 2
  | b100 => 3
  | b101 => 4
  | b110 => 5
  | b111 => 6

theorem pointIndex_lt_seven (p : FanoPoint) : pointIndex p < 7 := by
  cases p <;> decide

/-- Collision of visible points, read in the full Triton carrier. -/
def completeState (a b : FanoPoint) : TritonState :=
  collide a.state b.state

theorem distinct_visible_collision_visible (a b : FanoPoint) (hab : a ≠ b) :
    visible (completeState a b) := by
  cases a <;> cases b <;>
    simp [completeState, collide, tritonXor, xorNat, visible, godPosition, FanoPoint.state] at hab ⊢

theorem self_visible_collision_exits_to_root (a : FanoPoint) :
    completeState a a = godPosition := by
  cases a <;> native_decide

/-- Complete a distinct visible pair as a visible Fano point. -/
def completePair : FanoPoint → FanoPoint → FanoPoint
  | b001, b010 => b011
  | b010, b001 => b011
  | b001, b011 => b010
  | b011, b001 => b010
  | b010, b011 => b001
  | b011, b010 => b001
  | b001, b100 => b101
  | b100, b001 => b101
  | b001, b101 => b100
  | b101, b001 => b100
  | b100, b101 => b001
  | b101, b100 => b001
  | b001, b110 => b111
  | b110, b001 => b111
  | b001, b111 => b110
  | b111, b001 => b110
  | b110, b111 => b001
  | b111, b110 => b001
  | b010, b100 => b110
  | b100, b010 => b110
  | b010, b110 => b100
  | b110, b010 => b100
  | b100, b110 => b010
  | b110, b100 => b010
  | b010, b101 => b111
  | b101, b010 => b111
  | b010, b111 => b101
  | b111, b010 => b101
  | b101, b111 => b010
  | b111, b101 => b010
  | b011, b100 => b111
  | b100, b011 => b111
  | b011, b111 => b100
  | b111, b011 => b100
  | b100, b111 => b011
  | b111, b100 => b011
  | b011, b101 => b110
  | b101, b011 => b110
  | b011, b110 => b101
  | b110, b011 => b101
  | b101, b110 => b011
  | b110, b101 => b011
  | a, _ => a

theorem completePair_state_eq_completeState (a b : FanoPoint) (hab : a ≠ b) :
    (completePair a b).state = completeState a b := by
  cases a <;> cases b <;>
    simp [completePair, completeState, collide, tritonXor, xorNat, FanoPoint.state] at hab ⊢

/-- Completing a distinct Fano pair computes exactly the Triton XOR of the two
visible carrier states. -/
theorem completePair_state_eq_xor (a b : FanoPoint) (hab : a ≠ b) :
    (completePair a b).state = collide a.state b.state := by
  simpa [completeState] using completePair_state_eq_completeState a b hab

/-- Incidence relation generated by Triton XOR. For distinct visible `a` and
`b`, `fanoLine a b c` means `c` is the XOR completion of `a` and `b`. -/
def fanoLine (a b c : FanoPoint) : Prop :=
  a ≠ b ∧ c = completePair a b

/-- Any point on the Fano line through a distinct pair is the Triton XOR
completion of that pair. -/
theorem fanoLine_state_eq_xor (a b c : FanoPoint) (h : fanoLine a b c) :
    c.state = collide a.state b.state := by
  rw [h.2]
  exact completePair_state_eq_xor a b h.1

theorem completePair_ne_left (a b : FanoPoint) (hab : a ≠ b) :
    completePair a b ≠ a := by
  cases a <;> cases b <;> simp [completePair] at hab ⊢

theorem completePair_ne_right (a b : FanoPoint) (hab : a ≠ b) :
    completePair a b ≠ b := by
  cases a <;> cases b <;> simp [completePair] at hab ⊢

/-- Every distinct visible pair has a unique third visible point on its Fano line. -/
theorem distinct_pair_unique_completion (a b : FanoPoint) (hab : a ≠ b) :
    completePair a b ≠ a ∧
    completePair a b ≠ b ∧
    fanoLine a b (completePair a b) ∧
    ∀ c, c ≠ a → c ≠ b → fanoLine a b c → c = completePair a b :=
  ⟨completePair_ne_left a b hab,
    completePair_ne_right a b hab,
    ⟨hab, rfl⟩,
    fun _ _ _ hline => hline.2⟩

/-- Existential form of the same incidence contract. -/
theorem distinct_pair_has_unique_completion (a b : FanoPoint) (hab : a ≠ b) :
    ∃ c,
      c ≠ a ∧ c ≠ b ∧ fanoLine a b c ∧
        ∀ d, d ≠ a → d ≠ b → fanoLine a b d → d = c := by
  refine ⟨completePair a b, ?_⟩
  exact distinct_pair_unique_completion a b hab

/-- A Fano line has zero total XOR parity in the Triton carrier: the
completion point `c` cancels the collision of `a` and `b` back to the root. -/
theorem fanoLine_xor_parity_zero (a b c : FanoPoint)
    (h : fanoLine a b c) :
    collide (collide a.state b.state) c.state = godPosition := by
  cases a <;> cases b <;> cases c <;>
    simp [fanoLine, completePair, collide, tritonXor, xorNat,
      godPosition, FanoPoint.state] at h ⊢

/-- The canonical completion of any distinct Fano pair gives zero total XOR
parity with the original pair. -/
theorem completePair_xor_parity_zero (a b : FanoPoint) (hab : a ≠ b) :
    collide (collide a.state b.state) (completePair a b).state = godPosition :=
  fanoLine_xor_parity_zero a b (completePair a b) ⟨hab, rfl⟩

end FanoIncidence
end Gnosis
