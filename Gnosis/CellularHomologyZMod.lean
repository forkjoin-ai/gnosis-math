import Init

/-!
# Cellular **1-chains** over **ℤ / p ℤ** (Init-only, no Mathlib)

## Coefficients

`Fin p` models **ℤ / p ℤ** for **`0 < p`**, with `zmodAdd` / `zmodNeg` (remainder arithmetic).

## Oriented **3-cycle** boundary `∂₁ : C₁ → C₀`

Edges `e₀ : 0→1`, `e₁ : 1→2`, `e₂ : 2→0`; edge coefficients `x₀, x₁, x₂ : Fin p`.

`triBoundaryApply hp x` is the triple of vertex-row values

* `(∂x)₀ = −x₀ + x₂`
* `(∂x)₁ =  x₀ − x₁`
* `(∂x)₂ =  x₁ − x₂`

## **`p = 2` certificate (fully decidable)**

`tri2_boundary_uniform_iff` classifies **`ker ∂₁`** over **`ℤ/2ℤ`**: vanishing of all three rows **iff**
`x₀ = x₁ = x₂`. The constant `(1,1,1)` chain lies in the kernel and is **non-zero** (`tri2_cycle_nonzero`).

For **general** `p ≥ 2`, the same **algebraic** classification holds in any commutative ring; this
file packages the **decidable** `p = 2` certificate (`tri2_boundary_uniform_iff`) that links
directly to the voting ledger’s `Fin 2` corners.

**Ledger boundary:** no `∂₂`, no general simplicial complex, no Smith normal form over ℤ.
-/

namespace Gnosis
namespace CellularHomologyZMod

abbrev Modulus := Nat

def zmodAdd {p : Modulus} (hp : 0 < p) (a b : Fin p) : Fin p :=
  ⟨(a.val + b.val) % p, Nat.mod_lt _ hp⟩

def zmodNeg {p : Modulus} (hp : 0 < p) (a : Fin p) : Fin p :=
  ⟨(p - a.val) % p, Nat.mod_lt _ (Nat.zero_lt_of_lt hp)⟩

theorem zmodAdd_comm {p : Modulus} (hp : 0 < p) (a b : Fin p) :
    zmodAdd hp a b = zmodAdd hp b a := by
  apply Fin.ext
  simp [zmodAdd, Nat.add_comm]

theorem zmodAdd_zero {p : Modulus} (hp : 0 < p) (a : Fin p) : zmodAdd hp a ⟨0, hp⟩ = a := by
  apply Fin.ext
  simp [zmodAdd, Nat.add_zero, Nat.mod_eq_of_lt a.isLt]

theorem zmodNeg_add_cancel {p : Modulus} (hp : 0 < p) (a : Fin p) :
    zmodAdd hp (zmodNeg hp a) a = ⟨0, hp⟩ := by
  rcases a with ⟨v, hv⟩
  by_cases h : v = 0
  · subst h
    apply Fin.ext
    simp [zmodAdd, zmodNeg, Nat.sub_zero, Nat.zero_mod, Nat.mod_self]
  · apply Fin.ext
    show ((p - v) % p + v) % p = 0
    have hvpos : 0 < v := Nat.pos_of_ne_zero h
    have hsub : p - v < p := Nat.sub_lt (Nat.zero_lt_of_lt hp) hvpos
    rw [Nat.mod_eq_of_lt hsub, Nat.sub_add_cancel (Nat.le_of_lt hv), Nat.mod_self]

theorem zmodAdd_neg_cancel {p : Modulus} (hp : 0 < p) (a : Fin p) :
    zmodAdd hp a (zmodNeg hp a) = ⟨0, hp⟩ := by
  rw [zmodAdd_comm]
  exact zmodNeg_add_cancel hp a

theorem one_lt_of_two_le {p : Modulus} (hp : 2 ≤ p) : 1 < p :=
  Nat.lt_of_succ_le hp

def zmodOne {p : Modulus} (hp : 2 ≤ p) : Fin p :=
  ⟨1, one_lt_of_two_le hp⟩

private theorem hp0 {p : Modulus} (hp : 2 ≤ p) : 0 < p :=
  Nat.zero_lt_of_lt (one_lt_of_two_le hp)

/-- Cellular boundary `∂₁ x` on the oriented 3-cycle (coefficients on the three edges). -/
def triBoundaryApply {p : Modulus} (hp : 2 ≤ p) (x : Fin 3 → Fin p) (i : Fin 3) : Fin p :=
  match i with
  | ⟨0, _⟩ => zmodAdd (hp0 hp) (zmodNeg (hp0 hp) (x ⟨0, by decide⟩)) (x ⟨2, by decide⟩)
  | ⟨1, _⟩ => zmodAdd (hp0 hp) (x ⟨0, by decide⟩) (zmodNeg (hp0 hp) (x ⟨1, by decide⟩))
  | ⟨2, _⟩ => zmodAdd (hp0 hp) (x ⟨1, by decide⟩) (zmodNeg (hp0 hp) (x ⟨2, by decide⟩))

/-! ### Specialized **`p = 2`** complex (F₂ vector space, decidable kernel) -/

abbrev pTwo : Modulus := 2

theorem two_le_pTwo : (2 : Modulus) ≤ pTwo :=
  Nat.le_refl 2

private theorem hp0_two : 0 < pTwo := by decide

/-- Canonical `0` and `1` in `Fin 2` (for exhaustive `match` patterns). -/
private def f2z : Fin pTwo :=
  ⟨0, hp0_two⟩

private def f2o : Fin pTwo :=
  ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩

private theorem fin2_eq (z : Fin pTwo) : z = f2z ∨ z = f2o :=
  match z with
  | ⟨0, _⟩ => Or.inl (Fin.ext rfl)
  | ⟨1, _⟩ => Or.inr (Fin.ext rfl)

/-- Assemble a `Fin 3 → Fin pTwo` from three edge coefficients (the eight cases exhaust all maps). -/
def funOfTripleFn (a b c : Fin pTwo) : Fin 3 → Fin pTwo
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

private theorem fin3_val_eq (i : Fin 3) : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 :=
  match i with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr (Or.inl rfl)
  | ⟨2, _⟩ => Or.inr (Or.inr rfl)

theorem funOfTripleFn_eq (x : Fin 3 → Fin pTwo) :
    x = funOfTripleFn (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) := by
  funext i
  rcases fin3_val_eq i with h0 | h1 | h2
  · rw [show i = ⟨0, by decide⟩ from Fin.ext h0]; rfl
  · rw [show i = ⟨1, by decide⟩ from Fin.ext h1]; rfl
  · rw [show i = ⟨2, by decide⟩ from Fin.ext h2]; rfl

theorem tri2_boundary_uniform_iff_triple (a b c : Fin pTwo) :
    (triBoundaryApply two_le_pTwo (funOfTripleFn a b c) ⟨0, by decide⟩ = ⟨0, hp0_two⟩ ∧
        triBoundaryApply two_le_pTwo (funOfTripleFn a b c) ⟨1, by decide⟩ = ⟨0, hp0_two⟩ ∧
          triBoundaryApply two_le_pTwo (funOfTripleFn a b c) ⟨2, by decide⟩ = ⟨0, hp0_two⟩) ↔
      a = b ∧ b = c := by
  rcases fin2_eq a with ha | ha <;> rcases fin2_eq b with hb | hb <;> rcases fin2_eq c with hc | hc <;>
    (try rw [ha, hb, hc]) <;> native_decide

theorem tri2_boundary_uniform_iff (x : Fin 3 → Fin pTwo) :
    (triBoundaryApply two_le_pTwo x ⟨0, by decide⟩ = ⟨0, hp0_two⟩ ∧
        triBoundaryApply two_le_pTwo x ⟨1, by decide⟩ = ⟨0, hp0_two⟩ ∧
          triBoundaryApply two_le_pTwo x ⟨2, by decide⟩ = ⟨0, hp0_two⟩) ↔
      x ⟨0, by decide⟩ = x ⟨1, by decide⟩ ∧ x ⟨1, by decide⟩ = x ⟨2, by decide⟩ := by
  rw [funOfTripleFn_eq x]
  exact tri2_boundary_uniform_iff_triple (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩)

theorem tri2_cycle_in_kernel :
    triBoundaryApply two_le_pTwo (fun _ => zmodOne two_le_pTwo) ⟨0, by decide⟩ = ⟨0, hp0_two⟩ ∧
      triBoundaryApply two_le_pTwo (fun _ => zmodOne two_le_pTwo) ⟨1, by decide⟩ = ⟨0, hp0_two⟩ ∧
        triBoundaryApply two_le_pTwo (fun _ => zmodOne two_le_pTwo) ⟨2, by decide⟩ = ⟨0, hp0_two⟩ := by
  native_decide

theorem tri2_cycle_nonzero : (fun _ : Fin 3 => zmodOne two_le_pTwo) ≠ fun _ => ⟨0, hp0_two⟩ := by
  intro h
  have h1 := congrArg Fin.val (congrFun h ⟨0, by decide⟩)
  simp [zmodOne] at h1

end CellularHomologyZMod
end Gnosis
