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

def add (v1 v2 : Vector3) : Vector3 :=
  ⟨v1.x + v2.x, v1.y + v2.y, v1.z + v2.z⟩

def sub (v1 v2 : Vector3) : Vector3 :=
  ⟨v1.x - v2.x, v1.y - v2.y, v1.z - v2.z⟩

def neg (v : Vector3) : Vector3 :=
  ⟨-v.x, -v.y, -v.z⟩

instance : Add Vector3 := ⟨add⟩
instance : Sub Vector3 := ⟨sub⟩
instance : Neg Vector3 := ⟨neg⟩

@[simp] theorem add_x (u v : Vector3) : (u + v).x = u.x + v.x := rfl
@[simp] theorem add_y (u v : Vector3) : (u + v).y = u.y + v.y := rfl
@[simp] theorem add_z (u v : Vector3) : (u + v).z = u.z + v.z := rfl

@[simp] theorem sub_x (u v : Vector3) : (u - v).x = u.x - v.x := rfl
@[simp] theorem sub_y (u v : Vector3) : (u - v).y = u.y - v.y := rfl
@[simp] theorem sub_z (u v : Vector3) : (u - v).z = u.z - v.z := rfl

@[simp] theorem neg_x (u : Vector3) : (-u).x = -u.x := rfl
@[simp] theorem neg_y (u : Vector3) : (-u).y = -u.y := rfl
@[simp] theorem neg_z (u : Vector3) : (-u).z = -u.z := rfl

end Gnosis.VectorMath
