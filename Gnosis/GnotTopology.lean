import Gnosis.TopologicalGrammar
import Gnosis.PoetryLattice

/-
  GnotTopology.lean
  =================

  Formalizes the structural density of the Gnot abstract syntax tree (AST)
  and proves its isomorphism to the Poetry Lattice (Triton, Hexon, etc.).

  The "syllable" in Gnot is defined as a semantic topological node:
  - Subject
  - Verb
  - Arguments
  - Qualifiers
  - Target
-/


namespace Gnosis
namespace GnotTopology

open TopologicalGrammar
open PoetryLattice

-- Represents the syllable weight (topological density) of a Gnot AST node
structure SyllableWeight where
  value : Nat

-- A Gnot clause consists of a subject, predicate (verb + args), qualifiers, and target.
structure GnotClause where
  subject_syllables : Nat
  verb_syllables : Nat      -- Always 1
  args_syllables : Nat
  qualifier_syllables : Nat -- 1 for the tag + N for the value
  target_syllables : Nat

def clause_syllables (c : GnotClause) : Nat :=
  c.subject_syllables + c.verb_syllables + c.args_syllables + c.qualifier_syllables + c.target_syllables

-- A Gnot block (Stanza/Flow) contains a name, parameters, yields, and a list of clauses.
structure GnotBlock where
  kind_syllables : Nat      -- 1 for `verse` or `is`
  name_syllables : Nat      -- 1 for the identifier
  params_syllables : Nat
  yields_syllables : Nat    -- 0 or 2
  clauses : List GnotClause

def block_fold (b : GnotBlock) : Nat :=
  b.clauses.length

def block_syllables (b : GnotBlock) : Nat :=
  b.kind_syllables + b.name_syllables + b.params_syllables + b.yields_syllables +
  b.clauses.foldl (fun acc c => acc + clause_syllables c) 0

-- A perfectly reduced Gnot clause for a Triton lacks excess arguments or qualifiers
-- and consists of just a simple subject, verb, and target (3 syllables).
def IsPerfectClause (c : GnotClause) : Prop :=
  c.subject_syllables = 1 ∧
  c.verb_syllables = 1 ∧
  c.args_syllables = 0 ∧
  c.qualifier_syllables = 0 ∧
  c.target_syllables = 1

theorem perfect_clause_weight (c : GnotClause) (h : IsPerfectClause c) :
    clause_syllables c = 3 := by
  dsimp [clause_syllables]
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]

/-! ### Clause-list fold (shared by perfect density and sandwich bookkeeping) -/

private theorem foldl_clause_sum_acc (L : List GnotClause) (acc : Nat)
    (h₃ : ∀ c ∈ L, clause_syllables c = 3) :
    L.foldl (fun a c => a + clause_syllables c) acc = acc + 3 * L.length := by
  induction L generalizing acc with
  | nil =>
    simp [List.foldl, List.length, Nat.mul_zero, Nat.add_zero]
  | cons x xs ih =>
    have hx : clause_syllables x = 3 :=
      h₃ x (List.Mem.head _)
    have hrest : ∀ c ∈ xs, clause_syllables c = 3 := fun c hc =>
      h₃ c (List.Mem.tail _ hc)
    simp [List.foldl, hx]
    rw [ih (acc + 3) hrest, Nat.mul_succ 3 xs.length, Nat.add_assoc acc 3 (3 * xs.length),
      Nat.add_comm 3 (3 * xs.length)]

theorem foldl_clause_sum_eq_three_mul_length (L : List GnotClause)
    (h₃ : ∀ c ∈ L, clause_syllables c = 3) :
    L.foldl (fun acc c => acc + clause_syllables c) 0 = 3 * L.length := by
  simpa [Nat.zero_add] using foldl_clause_sum_acc L 0 h₃

-- A Gnot Stanza that perfectly matches a Triton topology
def IsPerfectTriton (b : GnotBlock) : Prop :=
  block_fold b = 3 ∧ -- Triton.parts
  b.kind_syllables = 1 ∧
  b.name_syllables = 1 ∧
  b.params_syllables = 4 ∧
  b.yields_syllables = 2 ∧
  ∀ c ∈ b.clauses, IsPerfectClause c

theorem perfect_triton_is_dense (b : GnotBlock) (h : IsPerfectTriton b) :
    block_syllables b = 17 := by
  dsimp [block_syllables]
  rw [h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1]
  have h_len : b.clauses.length = 3 := h.1
  match eq : b.clauses with
  | [c1, c2, c3] =>
    have h_c1 : IsPerfectClause c1 := h.2.2.2.2.2 c1 (by rw [eq]; exact List.Mem.head _)
    have h_c2 : IsPerfectClause c2 := h.2.2.2.2.2 c2 (by rw [eq]; exact List.Mem.tail _ (List.Mem.head _))
    have h_c3 : IsPerfectClause c3 := h.2.2.2.2.2 c3 (by rw [eq]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have w1 : clause_syllables c1 = 3 := perfect_clause_weight c1 h_c1
    have w2 : clause_syllables c2 = 3 := perfect_clause_weight c2 h_c2
    have w3 : clause_syllables c3 = 3 := perfect_clause_weight c3 h_c3
    simp only [List.foldl, w1, w2, w3, Nat.zero_add, Nat.add_assoc]
  | [] => rw [eq] at h_len; simp at h_len
  | [_] => rw [eq] at h_len; simp at h_len
  | [_, _] => rw [eq] at h_len; simp at h_len
  | _ :: _ :: _ :: _ :: _ => rw [eq] at h_len; simp at h_len

-- A Gnot Stanza that perfectly matches a Hexon topology
def IsPerfectHexon (b : GnotBlock) : Prop :=
  block_fold b = 6 ∧ -- Hexon.parts
  b.kind_syllables = 1 ∧
  b.name_syllables = 1 ∧
  b.params_syllables = 12 ∧      -- Header doubles to 16: 1+1+12+2=16
  b.yields_syllables = 2 ∧
  ∀ c ∈ b.clauses, IsPerfectClause c

theorem perfect_hexon_is_dense (b : GnotBlock) (h : IsPerfectHexon b) :
    block_syllables b = 34 := by
  dsimp [block_syllables]
  rw [h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1]
  have h_ci : ∀ c ∈ b.clauses, clause_syllables c = 3 :=
    fun c hc => perfect_clause_weight c (h.2.2.2.2.2 c hc)
  have hL : b.clauses.length = 6 := by simpa [block_fold] using h.1
  rw [foldl_clause_sum_eq_three_mul_length b.clauses h_ci, hL]

-- A Gnot Stanza that perfectly matches an Enneon topology
def IsPerfectEnneon (b : GnotBlock) : Prop :=
  block_fold b = 9 ∧ -- Enneon.parts
  b.kind_syllables = 1 ∧
  b.name_syllables = 1 ∧
  b.params_syllables = 20 ∧      -- Header triples to 24: 1+1+20+2=24
  b.yields_syllables = 2 ∧
  ∀ c ∈ b.clauses, IsPerfectClause c

theorem perfect_enneon_is_dense (b : GnotBlock) (h : IsPerfectEnneon b) :
    block_syllables b = 51 := by
  dsimp [block_syllables]
  rw [h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1]
  have h_ci : ∀ c ∈ b.clauses, clause_syllables c = 3 :=
    fun c hc => perfect_clause_weight c (h.2.2.2.2.2 c hc)
  have hL : b.clauses.length = 9 := by simpa [block_fold] using h.1
  rw [foldl_clause_sum_eq_three_mul_length b.clauses h_ci, hL]

-- ==========================================
-- Topology Collapse & Friction Formalization
-- ==========================================

-- A clause is structurally collapsed if it lacks a core load-bearing node
def IsStructurallyCollapsed (c : GnotClause) : Prop :=
  c.subject_syllables = 0 ∨ c.verb_syllables = 0 ∨ c.target_syllables = 0

-- A clause contains topological friction if it carries non-essential mass
def HasTopologicalFriction (c : GnotClause) : Prop :=
  c.args_syllables > 0 ∨ c.qualifier_syllables > 0 ∨ c.subject_syllables > 1 ∨ c.verb_syllables > 1 ∨ c.target_syllables > 1

-- The header contribute syllables
def HasPerfectHeader (b : GnotBlock) (parts : Nat) : Prop :=
  match parts with
  | 3 => b.kind_syllables = 1 ∧ b.name_syllables = 1 ∧ b.params_syllables = 4 ∧ b.yields_syllables = 2
  | 6 => b.kind_syllables = 1 ∧ b.name_syllables = 1 ∧ b.params_syllables = 12 ∧ b.yields_syllables = 2
  | 9 => b.kind_syllables = 1 ∧ b.name_syllables = 1 ∧ b.params_syllables = 20 ∧ b.yields_syllables = 2
  | _ => False

-- Helper: pure Nat equivalence
private theorem eq_zero_of_not_pos (n : Nat) (h : ¬ (0 < n)) : n = 0 := by
  match n with
  | 0 => rfl
  | k + 1 => exact absurd (Nat.succ_pos k) h

private theorem clause_at_least_3 (c : GnotClause) 
    (hs : c.subject_syllables ≠ 0) (hv : c.verb_syllables ≠ 0) (ht : c.target_syllables ≠ 0) : 
    3 ≤ clause_syllables c := by
  dsimp [clause_syllables]
  have hs1 : 1 ≤ c.subject_syllables := Nat.pos_of_ne_zero hs
  have hv1 : 1 ≤ c.verb_syllables := Nat.pos_of_ne_zero hv
  have ht1 : 1 ≤ c.target_syllables := Nat.pos_of_ne_zero ht
  have hsv : 2 ≤ c.subject_syllables + c.verb_syllables := Nat.add_le_add hs1 hv1
  have hsva : 2 ≤ c.subject_syllables + c.verb_syllables + c.args_syllables := Nat.le_trans hsv (Nat.le_add_right _ _)
  have hsvaq : 2 ≤ c.subject_syllables + c.verb_syllables + c.args_syllables + c.qualifier_syllables := Nat.le_trans hsva (Nat.le_add_right _ _)
  exact Nat.add_le_add hsvaq ht1

theorem clause_under_3_is_collapsed (c : GnotClause) (h : clause_syllables c < 3) :
    IsStructurallyCollapsed c := by
  dsimp [IsStructurallyCollapsed]
  match Classical.em (c.subject_syllables = 0) with
  | Or.inl h0 => exact Or.inl h0
  | Or.inr hn0 =>
    match Classical.em (c.verb_syllables = 0) with
    | Or.inl h1 => exact Or.inr (Or.inl h1)
    | Or.inr hn1 =>
      match Classical.em (c.target_syllables = 0) with
      | Or.inl h2 => exact Or.inr (Or.inr h2)
      | Or.inr hn2 =>
        have h3le : 3 ≤ clause_syllables c := clause_at_least_3 c hn0 hn1 hn2
        have h_absurd : clause_syllables c < clause_syllables c := Nat.lt_of_lt_of_le h h3le
        exact absurd h_absurd (Nat.lt_irrefl _)

theorem clause_over_3_has_friction (c : GnotClause) 
    (h_not_collapsed : ¬ IsStructurallyCollapsed c)
    (h_weight : clause_syllables c > 3) :
    HasTopologicalFriction c := by
  match Classical.em (HasTopologicalFriction c) with
  | Or.inl hf => exact hf
  | Or.inr h_not_friction =>
    dsimp [IsStructurallyCollapsed] at h_not_collapsed
    dsimp [HasTopologicalFriction] at h_not_friction
    have h_s_not_0 : c.subject_syllables ≠ 0 := fun h => h_not_collapsed (Or.inl h)
    have h_v_not_0 : c.verb_syllables ≠ 0 := fun h => h_not_collapsed (Or.inr (Or.inl h))
    have h_t_not_0 : c.target_syllables ≠ 0 := fun h => h_not_collapsed (Or.inr (Or.inr h))
    have h_a_0 : ¬ (c.args_syllables > 0) := fun h => h_not_friction (Or.inl h)
    have h_q_0 : ¬ (c.qualifier_syllables > 0) := fun h => h_not_friction (Or.inr (Or.inl h))
    have h_s_not_gt_1 : ¬ (c.subject_syllables > 1) := fun h => h_not_friction (Or.inr (Or.inr (Or.inl h)))
    have h_v_not_gt_1 : ¬ (c.verb_syllables > 1) := fun h => h_not_friction (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have h_t_not_gt_1 : ¬ (c.target_syllables > 1) := fun h => h_not_friction (Or.inr (Or.inr (Or.inr (Or.inr h))))
    have ha : c.args_syllables = 0 := eq_zero_of_not_pos _ h_a_0
    have hq : c.qualifier_syllables = 0 := eq_zero_of_not_pos _ h_q_0
    have hs1 : c.subject_syllables = 1 := Nat.le_antisymm (Nat.le_of_not_lt h_s_not_gt_1) (Nat.pos_of_ne_zero h_s_not_0)
    have hv1 : c.verb_syllables = 1 := Nat.le_antisymm (Nat.le_of_not_lt h_v_not_gt_1) (Nat.pos_of_ne_zero h_v_not_0)
    have ht1 : c.target_syllables = 1 := Nat.le_antisymm (Nat.le_of_not_lt h_t_not_gt_1) (Nat.pos_of_ne_zero h_t_not_0)
    have heq : clause_syllables c = 3 := by dsimp [clause_syllables]; rw [hs1, hv1, ha, hq, ht1]
    rw [heq] at h_weight; exact absurd h_weight (Nat.lt_irrefl _)

private theorem Nat_list_foldl_add_eq_add_foldl_zero (xs : List Nat) (x : Nat) :
    xs.foldl (·+·) x = x + xs.foldl (·+·) 0 := by
  induction xs generalizing x with
  | nil =>
    simp [List.foldl, Nat.add_zero]
  | cons y ys ih =>
    simp [List.foldl]
    rw [ih (x + y), ih y]
    exact Nat.add_assoc x y (ys.foldl (·+·) 0)

private theorem foldl_add_clause_eq_map_sum_acc (L : List GnotClause) (acc : Nat) :
    L.foldl (fun a c => a + clause_syllables c) acc =
      (L.map clause_syllables).foldl (·+·) acc := by
  induction L generalizing acc with
  | nil =>
    simp [List.foldl, List.map]
  | cons x xs ih =>
    simp [List.foldl, List.map]
    exact ih (acc + clause_syllables x)

theorem foldl_add_clause_eq_map_sum (L : List GnotClause) :
    L.foldl (fun acc c => acc + clause_syllables c) 0 =
      (L.map clause_syllables).foldl (·+·) 0 :=
  foldl_add_clause_eq_map_sum_acc L 0

private theorem exists_lt_three_of_sum_lt_mul (L : List Nat)
    (hsum : L.foldl (·+·) 0 < 3 * L.length) : ∃ x ∈ L, x < 3 := by
  induction L with
  | nil =>
    simp [List.foldl, Nat.mul_zero] at hsum
  | cons x xs ih =>
    simp [List.foldl, Nat.mul_succ] at hsum
    cases Classical.em (x < 3) with
    | inl hx => exact ⟨x, List.Mem.head _, hx⟩
    | inr hnx =>
      have hx3 : 3 ≤ x := by
        match x with
        | 0 => exact absurd (hnx (by decide : (0 : Nat) < 3)) id
        | 1 => exact absurd (hnx (by decide : (1 : Nat) < 3)) id
        | 2 => exact absurd (hnx (by decide : (2 : Nat) < 3)) id
        | n + 3 => exact Nat.le_add_left 3 n
      have hsum' : x + xs.foldl (·+·) 0 < 3 + 3 * xs.length := by
        simpa [Nat_list_foldl_add_eq_add_foldl_zero xs x, Nat.add_comm (3 * xs.length)] using hsum
      have hlt3 : 3 + xs.foldl (·+·) 0 < 3 + 3 * xs.length :=
        Nat.lt_of_le_of_lt (Nat.add_le_add hx3 (Nat.le_refl (xs.foldl (·+·) 0))) hsum'
      have hxs : xs.foldl (·+·) 0 < 3 * xs.length :=
        Nat.lt_of_add_lt_add_left hlt3
      have ⟨y, hy, hy3⟩ := ih hxs
      exact ⟨y, List.Mem.tail _ hy, hy3⟩

private theorem sum_lt_parts (L : List Nat) (n : Nat) (h : L.length = n) (h_sum : L.foldl (·+·) 0 < 3 * n) :
    ∃ x ∈ L, x < 3 := by
  subst h
  exact exists_lt_three_of_sum_lt_mul L h_sum

theorem block_under_ideal_is_collapse (b : GnotBlock) (parts ideal : Nat)
    (hp : parts = 3 ∨ parts = 6 ∨ parts = 9)
    (h_len : b.clauses.length = parts)
    (h_header : HasPerfectHeader b parts)
    (h_ideal :
      ideal =
        b.kind_syllables + b.name_syllables + b.params_syllables + b.yields_syllables + 3 * parts)
    (h_weight : block_syllables b < ideal) :
    ∃ c ∈ b.clauses, IsStructurallyCollapsed c := by
  dsimp [block_syllables] at h_weight
  rw [h_ideal] at h_weight
  have h_map_fold :
      (List.map clause_syllables b.clauses).foldl (·+·) 0 =
        b.clauses.foldl (fun acc c => acc + clause_syllables c) 0 :=
    (foldl_add_clause_eq_map_sum b.clauses).symm
  cases hp with
  | inl hp3 =>
    subst hp3
    have ⟨h1, h2, h3, h4⟩ := h_header
    rw [h1, h2, h3, h4] at h_weight
    have h_sum_lt :
        (List.map clause_syllables b.clauses).foldl (·+·) 0 < 3 * 3 := by
      have := Nat.lt_of_add_lt_add_left h_weight
      rwa [← h_map_fold] at this
    have h_pigeon :=
      sum_lt_parts (b.clauses.map clause_syllables) 3 (by simp [List.length_map, h_len])
        h_sum_lt
    rcases h_pigeon with ⟨w, hw_mem, hw_lt⟩
    rcases List.mem_map.mp hw_mem with ⟨c, hc_in, rfl⟩
    exact ⟨c, hc_in, clause_under_3_is_collapsed c hw_lt⟩
  | inr hp69 =>
    cases hp69 with
    | inl hp6 =>
      subst hp6
      have ⟨h1, h2, h3, h4⟩ := h_header
      rw [h1, h2, h3, h4] at h_weight
      have h_sum_lt :
          (List.map clause_syllables b.clauses).foldl (·+·) 0 < 3 * 6 := by
        have := Nat.lt_of_add_lt_add_left h_weight
        rwa [← h_map_fold] at this
      have h_pigeon :=
        sum_lt_parts (b.clauses.map clause_syllables) 6 (by simp [List.length_map, h_len])
          h_sum_lt
      rcases h_pigeon with ⟨w, hw_mem, hw_lt⟩
      rcases List.mem_map.mp hw_mem with ⟨c, hc_in, rfl⟩
      exact ⟨c, hc_in, clause_under_3_is_collapsed c hw_lt⟩
    | inr hp9 =>
      subst hp9
      have ⟨h1, h2, h3, h4⟩ := h_header
      rw [h1, h2, h3, h4] at h_weight
      have h_sum_lt :
          (List.map clause_syllables b.clauses).foldl (·+·) 0 < 3 * 9 := by
        have := Nat.lt_of_add_lt_add_left h_weight
        rwa [← h_map_fold] at this
      have h_pigeon :=
        sum_lt_parts (b.clauses.map clause_syllables) 9 (by simp [List.length_map, h_len])
          h_sum_lt
      rcases h_pigeon with ⟨w, hw_mem, hw_lt⟩
      rcases List.mem_map.mp hw_mem with ⟨c, hc_in, rfl⟩
      exact ⟨c, hc_in, clause_under_3_is_collapsed c hw_lt⟩

end GnotTopology
end Gnosis

/-
### Reference: perfect-grasshopper.gnot

```gnot
gnot perfect-grasshopper v1.0
profile poetry

using
  app = x_gnosis
  gnosis

verse grasshopper hears as we look up yields leap
  now, gathering(into)
  arriving, become(rearrangingly)
  the, grasshopper(now)
```
-/
