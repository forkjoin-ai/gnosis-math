namespace Gnosis.VectorMath

/-- A vector in the Gnosis manifold. -/
structure Vector3 where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr, BEq

def dot (v1 v2 : Vector3) : Int :=
  v1.x * v2.x + v1.y * v2.y + v1.z * v2.z

def cross (v1 v2 : Vector3) : Vector3 :=
  ⟨v1.y * v2.z - v1.z * v2.y,
   v1.z * v2.x - v1.x * v2.z,
   v1.x * v2.y - v1.y * v2.x⟩

end Gnosis.VectorMath
