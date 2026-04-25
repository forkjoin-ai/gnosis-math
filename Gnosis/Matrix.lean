import Gnosis.Real
import Gnosis.Fintype

/-!
# Buleyean Matrix
Sovereign, minimalist matrix implementation for Gnosis.
-/

namespace Gnosis

def Matrix (n m : Type*) (α : Type*) := n → m → α

namespace Matrix

section Basic
variable {n m : Type*} {α : Type*}

def of (f : n → m → α) : Matrix n m α := f

def transpose (A : Matrix n m α) : Matrix m n α := fun i j => A j i

postfix:max "ᵀ" => transpose

end Basic

section Arithmetic
variable {n m p : Type*} [BuleFintype m] [Add α] [Mul α] [Zero α]

def mul (A : Matrix n m α) (B : Matrix m p α) : Matrix n p α :=
  fun i j => Finset.sum (fun k => A i k * B k j)

instance [BuleFintype n] : Mul (Matrix n n α) where
  mul := mul

def vecMul [BuleFintype n] (v : n → α) (A : Matrix n m α) : m → α :=
  fun j => Finset.sum (fun i => v i * A i j)

def mulVec [BuleFintype m] (A : Matrix n m α) (v : m → α) : n → α :=
  fun i => Finset.sum (fun j => A i j * v j)

def dotProduct [BuleFintype n] (v w : n → α) : α :=
  Finset.sum (fun i => v i * w i)

end Arithmetic

end Matrix

end Gnosis
