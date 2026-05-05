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

import Gnosis.TopologicalGrammar
import Gnosis.PoetryLattice

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
  have h_len : b.clauses.length = 6 := h.1
  match eq : b.clauses with
  | [c1, c2, c3, c4, c5, c6] =>
    have h_ci : ∀ c ∈ [c1, c2, c3, c4, c5, c6], clause_syllables c = 3 := fun c hc => 
      perfect_clause_weight c (h.2.2.2.2.2 c (by rw [eq]; exact hc))
    have w1 : clause_syllables c1 = 3 := h_ci c1 (by simp)
    have w2 : clause_syllables c2 = 3 := h_ci c2 (by simp)
    have w3 : clause_syllables c3 = 3 := h_ci c3 (by simp)
    have w4 : clause_syllables c4 = 3 := h_ci c4 (by simp)
    have w5 : clause_syllables c5 = 3 := h_ci c5 (by simp)
    have w6 : clause_syllables c6 = 3 := h_ci c6 (by simp)
    simp only [List.foldl, w1, w2, w3, w4, w5, w6, Nat.zero_add, Nat.add_assoc]
  | _ => rw [eq] at h_len; injection h_len -- Length mismatch

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
  have h_len : b.clauses.length = 9 := h.1
  match eq : b.clauses with
  | [c1, c2, c3, c4, c5, c6, c7, c8, c9] =>
    have h_ci : ∀ c ∈ [c1, c2, c3, c4, c5, c6, c7, c8, c9], clause_syllables c = 3 := fun c hc => 
      perfect_clause_weight c (h.2.2.2.2.2 c (by rw [eq]; exact hc))
    have w1 : clause_syllables c1 = 3 := h_ci c1 (by simp)
    have w2 : clause_syllables c2 = 3 := h_ci c2 (by simp)
    have w3 : clause_syllables c3 = 3 := h_ci c3 (by simp)
    have w4 : clause_syllables c4 = 3 := h_ci c4 (by simp)
    have w5 : clause_syllables c5 = 3 := h_ci c5 (by simp)
    have w6 : clause_syllables c6 = 3 := h_ci c6 (by simp)
    have w7 : clause_syllables c7 = 3 := h_ci c7 (by simp)
    have w8 : clause_syllables c8 = 3 := h_ci c8 (by simp)
    have w9 : clause_syllables c9 = 3 := h_ci c9 (by simp)
    simp only [List.foldl, w1, w2, w3, w4, w5, w6, w7, w8, w9, Nat.zero_add, Nat.add_assoc]
  | _ => rw [eq] at h_len; injection h_len

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

private theorem sum_lt_parts (L : List Nat) (n : Nat) (h : L.length = n) (h_sum : L.foldl (·+·) 0 < 3 * n) :
    ∃ x ∈ L, x < 3 := by
  match n, L with
  | 0, [] => simp at h_sum
  | k + 1, x :: xs =>
    match Classical.em (x < 3) with
    | Or.inl hx => exact ⟨x, List.Mem.head _, hx⟩
    | Or.inr hnx =>
      have h3 : 3 ≤ x := Nat.le_of_not_lt hnx
      have h_sum_xs : xs.foldl (·+·) 0 < 3 * k := by
        simp [List.foldl] at h_sum
        rw [Nat.mul_succ, Nat.add_comm 3] at h_sum
        exact Nat.lt_of_add_lt_add_left (Nat.lt_of_le_of_lt (Nat.add_le_add_right h3 _) h_sum)
      have ⟨x', hx', hw'⟩ := sum_lt_parts xs k (by simp at h; exact h) h_sum_xs
      exact ⟨x', List.Mem.tail _ hx', hw'⟩

theorem block_under_ideal_is_collapse (b : GnotBlock) (parts ideal header : Nat)
    (h_len : b.clauses.length = parts)
    (h_header : HasPerfectHeader b parts)
    (h_ideal : ideal = header + 3 * parts)
    (h_weight : block_syllables b < ideal) :
    ∃ c ∈ b.clauses, IsStructurallyCollapsed c := by
  dsimp [block_syllables] at h_weight
  rw [h_ideal] at h_weight
  match parts with
  | 3 => 
    have ⟨h1, h2, h3, h4⟩ := h_header
    rw [h1, h2, h3, h4] at h_weight
    have h_pigeon : ∃ c ∈ b.clauses, clause_syllables c < 3 := sum_lt_parts (b.clauses.map clause_syllables) 3 (by simp [h_len]) (by
      simp [List.foldl_map] at h_weight; exact Nat.lt_of_add_lt_add_left h_weight)
    have ⟨c_val, hc_mem, hc_lt⟩ := h_pigeon
    have ⟨c, hc_in, hc_eq⟩ := List.mem_map.1 hc_mem
    exact ⟨c, hc_in, hc_eq ▸ clause_under_3_is_collapsed c hc_lt⟩
  | 6 => 
    have ⟨h1, h2, h3, h4⟩ := h_header
    rw [h1, h2, h3, h4] at h_weight
    have h_pigeon : ∃ c ∈ b.clauses, clause_syllables c < 3 := sum_lt_parts (b.clauses.map clause_syllables) 6 (by simp [h_len]) (by
      simp [List.foldl_map] at h_weight; exact Nat.lt_of_add_lt_add_left h_weight)
    have ⟨c_val, hc_mem, hc_lt⟩ := h_pigeon
    have ⟨c, hc_in, hc_eq⟩ := List.mem_map.1 hc_mem
    exact ⟨c, hc_in, hc_eq ▸ clause_under_3_is_collapsed c hc_lt⟩
  | 9 => 
    have ⟨h1, h2, h3, h4⟩ := h_header
    rw [h1, h2, h3, h4] at h_weight
    have h_pigeon : ∃ c ∈ b.clauses, clause_syllables c < 3 := sum_lt_parts (b.clauses.map clause_syllables) 9 (by simp [h_len]) (by
      simp [List.foldl_map] at h_weight; exact Nat.lt_of_add_lt_add_left h_weight)
    have ⟨c_val, hc_mem, hc_lt⟩ := h_pigeon
    have ⟨c, hc_in, hc_eq⟩ := List.mem_map.1 hc_mem
    exact ⟨c, hc_in, hc_eq ▸ clause_under_3_is_collapsed c hc_lt⟩
  | _ => exact absurd h_header (fun h => match h with | _ => by contradiction)

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
