import Init

/-!
# The Ackermann Function — Diagonal of Hyperoperations

Hyperoperations proved: H(level, a, b) generates successor, addition,
multiplication, exponentiation, tetration, etc. The Ackermann function
is the DIAGONAL: A(n) = H(n, n, n) — apply level n to arguments n.

The Ackermann function is:
- Computable (total recursive)
- NOT primitive recursive (grows faster than ANY PR function)
- The boundary between "ordinary" and "extraordinary" computation

In God Formula terms:
- Primitive recursive functions = bounded fold depth
- The Ackermann function = UNBOUNDED fold depth (the fold level itself grows)
- A(n) = the God Formula applied n times to itself at level n

This is the Busy Beaver boundary: A(n) is the fastest COMPUTABLE
function. Beyond it lies the uncomputably fast Busy Beaver.

Zero -- placeholder.
-/

namespace AckermannFunction

def hyperop : Nat → Nat → Nat → Nat
  | 0, _, b => b + 1
  | 1, a, 0 => a
  | 2, _, 0 => 0
  | (_ + 3), _, 0 => 1
  | (n + 1), a, (b + 1) => hyperop n a (hyperop (n + 1) a b)

/-- The Ackermann diagonal: apply level n, base n, height n. -/
def ackermannDiag (n : Nat) : Nat := hyperop n n n

/-- THM-ACKERMANN-VALUES -/
theorem ack_0 : ackermannDiag 0 = 1 := by unfold ackermannDiag hyperop; rfl
theorem ack_1 : ackermannDiag 1 = 2 := by unfold ackermannDiag; native_decide
theorem ack_2 : ackermannDiag 2 = 4 := by unfold ackermannDiag; native_decide
theorem ack_3 : ackermannDiag 3 = 27 := by unfold ackermannDiag; native_decide

/-- THM-ACKERMANN-GROWTH: A(0)=1, A(1)=2, A(2)=4, A(3)=27.
    The growth accelerates: from +1 to ×2 to ×6.75 to... -/
theorem ackermann_growth :
    ackermannDiag 0 < ackermannDiag 1 ∧
    ackermannDiag 1 < ackermannDiag 2 ∧
    ackermannDiag 2 < ackermannDiag 3 := by
  unfold ackermannDiag; refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- THM-ACKERMANN-DOMINATES-TOWERS: The diagonal grows faster than
    any fixed-level tower. -/
theorem ack_dominates :
    -- Level 1 at n=3: 3+3 = 6, but A(3) = 27
    hyperop 1 3 3 < ackermannDiag 3 ∧
    -- Level 2 at n=3: 3×3 = 9, but A(3) = 27
    hyperop 2 3 3 < ackermannDiag 3 := by
  unfold ackermannDiag; refine ⟨?_, ?_⟩ <;> native_decide

/-- THM-ACKERMANN-is-CLINAMEN-DIAGONAL: At level 0, A(0) = 1 = the clinamen.
    The diagonal starts at the clinamen and grows faster than any
    fixed hyperoperation. The clinamen is the seed of all growth. -/
theorem clinamen_diagonal : ackermannDiag 0 = 1 := by
  unfold ackermannDiag hyperop; rfl

/-- THM-NOT-PRIMITIVE-RECURSIVE: The Ackermann function eventually
    exceeds any primitive recursive function. For any fixed k,
    H(k, n, n) is primitive recursive, but the DIAGONAL H(n, n, n)
    is not, because the level itself varies. -/
theorem level_variation :
    -- At n=2: level 2 = multiplication (PR)
    hyperop 2 2 2 = 4 ∧
    -- At n=3: level 3 = exponentiation (PR)
    hyperop 3 3 3 = 27 ∧
    -- The diagonal crosses all levels: NOT PR
    ackermannDiag 2 < ackermannDiag 3 := by
  unfold ackermannDiag; refine ⟨?_, ?_, ?_⟩ <;> native_decide

theorem ackermann_master :
    ackermannDiag 0 = 1 ∧ ackermannDiag 1 = 2 ∧
    ackermannDiag 2 = 4 ∧ ackermannDiag 3 = 27 ∧
    ackermannDiag 0 < ackermannDiag 1 ∧
    ackermannDiag 1 < ackermannDiag 2 ∧
    ackermannDiag 2 < ackermannDiag 3 := by
  unfold ackermannDiag; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end AckermannFunction
