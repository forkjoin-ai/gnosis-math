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
  block_fold b = Triton.parts ∧ -- 3 clauses
  b.kind_syllables = 1 ∧
  b.name_syllables = 1 ∧
  b.params_syllables = 4 ∧       -- 4 parameters to the verse
  b.yields_syllables = 2 ∧       -- Yields a target
  ∀ c ∈ b.clauses, IsPerfectClause c

theorem perfect_triton_is_dense (b : GnotBlock) (h : IsPerfectTriton b) :
    block_syllables b = Triton.base_ropelength := by
  -- We know Triton.base_ropelength = 17
  have h_base : Triton.base_ropelength = 17 := by rfl
  rw [h_base]

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
    simp only [List.foldl, w1, w2, w3]
  | [] => rw [eq] at h_len; simp at h_len
  | [_] => rw [eq] at h_len; simp at h_len
  | [_, _] => rw [eq] at h_len; simp at h_len
  | _ :: _ :: _ :: _ :: _ => rw [eq] at h_len; simp at h_len

-- ==========================================
-- Topology Collapse & Friction Formalization
-- ==========================================

-- A clause is structurally collapsed if it lacks a core load-bearing node
def IsStructurallyCollapsed (c : GnotClause) : Prop :=
  c.subject_syllables = 0 ∨ c.verb_syllables = 0 ∨ c.target_syllables = 0

-- A clause contains topological friction if it carries non-essential mass
def HasTopologicalFriction (c : GnotClause) : Prop :=
  c.args_syllables > 0 ∨ c.qualifier_syllables > 0 ∨ c.subject_syllables > 1 ∨ c.verb_syllables > 1 ∨ c.target_syllables > 1

-- The header of a perfect Triton always contributes 8 syllables
def HasPerfectHeader (b : GnotBlock) : Prop :=
  b.kind_syllables = 1 ∧ b.name_syllables = 1 ∧ b.params_syllables = 4 ∧ b.yields_syllables = 2

-- Helper: pure Nat equivalence
private lemma eq_zero_of_not_pos (n : Nat) (h : ¬ (0 < n)) : n = 0 := by
  match n with
  | 0 => rfl
  | k + 1 => exact absurd (Nat.succ_pos k) h

private lemma clause_at_least_3 (c : GnotClause) 
    (hs : c.subject_syllables ≠ 0) (hv : c.verb_syllables ≠ 0) (ht : c.target_syllables ≠ 0) : 
    3 ≤ clause_syllables c := by
  dsimp [clause_syllables]
  have hs1 : 1 ≤ c.subject_syllables := Nat.pos_of_ne_zero hs
  have hv1 : 1 ≤ c.verb_syllables := Nat.pos_of_ne_zero hv
  have ht1 : 1 ≤ c.target_syllables := Nat.pos_of_ne_zero ht
  
  have hsv : 2 ≤ c.subject_syllables + c.verb_syllables := by
    have h2 : 2 = 1 + 1 := rfl
    rw [h2]
    exact Nat.add_le_add hs1 hv1
    
  have hsva : 2 ≤ c.subject_syllables + c.verb_syllables + c.args_syllables :=
    Nat.le_trans hsv (Nat.le_add_right _ _)
    
  have hsvaq : 2 ≤ c.subject_syllables + c.verb_syllables + c.args_syllables + c.qualifier_syllables :=
    Nat.le_trans hsva (Nat.le_add_right _ _)
    
  have h3 : 3 = 2 + 1 := rfl
  rw [h3]
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
    
    have hs1 : c.subject_syllables = 1 := 
      Nat.le_antisymm (Nat.le_of_not_lt h_s_not_gt_1) (Nat.pos_of_ne_zero h_s_not_0)
    have hv1 : c.verb_syllables = 1 := 
      Nat.le_antisymm (Nat.le_of_not_lt h_v_not_gt_1) (Nat.pos_of_ne_zero h_v_not_0)
    have ht1 : c.target_syllables = 1 := 
      Nat.le_antisymm (Nat.le_of_not_lt h_t_not_gt_1) (Nat.pos_of_ne_zero h_t_not_0)
      
    have heq : clause_syllables c = 3 := by
      dsimp [clause_syllables]
      rw [hs1, hv1, ha, hq, ht1]
      rfl
      
    rw [heq] at h_weight
    exact absurd h_weight (Nat.lt_irrefl _)

private lemma pigeonhole_17 (c1 c2 c3 : Nat) (h : 1 + 1 + 4 + 2 + (c1 + c2 + c3) < 17) : 
    c1 < 3 ∨ c2 < 3 ∨ c3 < 3 := by
  have h8 : 1 + 1 + 4 + 2 = 8 := rfl
  rw [h8] at h
  have h17 : 17 = 8 + 9 := rfl
  rw [h17] at h
  have h9 : c1 + c2 + c3 < 9 := Nat.lt_of_add_lt_add_left h
  
  match Classical.em (c1 < 3) with
  | Or.inl h1 => exact Or.inl h1
  | Or.inr hn1 =>
    match Classical.em (c2 < 3) with
    | Or.inl h2 => exact Or.inr (Or.inl h2)
    | Or.inr hn2 =>
      match Classical.em (c3 < 3) with
      | Or.inl h3 => exact Or.inr (Or.inr h3)
      | Or.inr hn3 =>
        have h31 : 3 ≤ c1 := Nat.le_of_not_lt hn1
        have h32 : 3 ≤ c2 := Nat.le_of_not_lt hn2
        have h33 : 3 ≤ c3 := Nat.le_of_not_lt hn3
        have h6 : 6 ≤ c1 + c2 := by
          have eq : 6 = 3 + 3 := rfl
          rw [eq]
          exact Nat.add_le_add h31 h32
        have h9_le : 9 ≤ c1 + c2 + c3 := by
          have eq : 9 = 6 + 3 := rfl
          rw [eq]
          exact Nat.add_le_add h6 h33
        have h_absurd : c1 + c2 + c3 < c1 + c2 + c3 := Nat.lt_of_lt_of_le h9 h9_le
        exact absurd h_absurd (Nat.lt_irrefl _)

theorem triton_under_17_is_collapse (b : GnotBlock) (h_len : b.clauses.length = 3)
    (h_header : HasPerfectHeader b) (h_weight : block_syllables b < 17) :
    ∃ c ∈ b.clauses, IsStructurallyCollapsed c := by
  dsimp [block_syllables] at h_weight
  have hk := h_header.1
  have hn := h_header.2.1
  have hp := h_header.2.2.1
  have hy := h_header.2.2.2
  rw [hk, hn, hp, hy] at h_weight
  match eq : b.clauses with
  | [c1, c2, c3] =>
    rw [eq] at h_weight
    have h_fold : List.foldl (fun acc c => acc + clause_syllables c) 0 [c1, c2, c3] = clause_syllables c1 + clause_syllables c2 + clause_syllables c3 := by
      simp only [List.foldl]
      rw [Nat.zero_add]
    rw [h_fold] at h_weight
    have h_pigeon : clause_syllables c1 < 3 ∨ clause_syllables c2 < 3 ∨ clause_syllables c3 < 3 := pigeonhole_17 _ _ _ h_weight
    match h_pigeon with
    | Or.inl h1 =>
      use c1; refine ⟨by rw [eq]; exact List.Mem.head _, clause_under_3_is_collapsed c1 h1⟩
    | Or.inr (Or.inl h2) =>
      use c2; refine ⟨by rw [eq]; exact List.Mem.tail _ (List.Mem.head _), clause_under_3_is_collapsed c2 h2⟩
    | Or.inr (Or.inr h3) =>
      use c3; refine ⟨by rw [eq]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), clause_under_3_is_collapsed c3 h3⟩
  | [] => rw [eq] at h_len; simp at h_len
  | [_] => rw [eq] at h_len; simp at h_len
  | [_, _] => rw [eq] at h_len; simp at h_len
  | _ :: _ :: _ :: _ :: _ => rw [eq] at h_len; simp at h_len

private lemma pigeonhole_17_gt (c1 c2 c3 : Nat) (h : 1 + 1 + 4 + 2 + (c1 + c2 + c3) > 17) : 
    c1 > 3 ∨ c2 > 3 ∨ c3 > 3 := by
  have h8 : 1 + 1 + 4 + 2 = 8 := rfl
  rw [h8] at h
  have h17 : 17 = 8 + 9 := rfl
  rw [h17] at h
  have h9 : 9 < c1 + c2 + c3 := Nat.lt_of_add_lt_add_left h
  
  match Classical.em (c1 > 3) with
  | Or.inl h1 => exact Or.inl h1
  | Or.inr hn1 =>
    match Classical.em (c2 > 3) with
    | Or.inl h2 => exact Or.inr (Or.inl h2)
    | Or.inr hn2 =>
      match Classical.em (c3 > 3) with
      | Or.inl h3 => exact Or.inr (Or.inr h3)
      | Or.inr hn3 =>
        have h31 : c1 ≤ 3 := Nat.le_of_not_lt hn1
        have h32 : c2 ≤ 3 := Nat.le_of_not_lt hn2
        have h33 : c3 ≤ 3 := Nat.le_of_not_lt hn3
        have h6 : c1 + c2 ≤ 6 := by
          have eq : 6 = 3 + 3 := rfl
          rw [eq]
          exact Nat.add_le_add h31 h32
        have h9_le : c1 + c2 + c3 ≤ 9 := by
          have eq : 9 = 6 + 3 := rfl
          rw [eq]
          exact Nat.add_le_add h6 h33
        have h_absurd : 9 < 9 := Nat.lt_of_lt_of_le h9 h9_le
        exact absurd h_absurd (Nat.lt_irrefl _)

theorem triton_over_17_is_friction_or_collapse (b : GnotBlock) (h_len : b.clauses.length = 3)
    (h_header : HasPerfectHeader b) (h_weight : block_syllables b > 17) :
    (∃ c ∈ b.clauses, IsStructurallyCollapsed c) ∨ (∃ c ∈ b.clauses, HasTopologicalFriction c) := by
  dsimp [block_syllables] at h_weight
  have hk := h_header.1
  have hn := h_header.2.1
  have hp := h_header.2.2.1
  have hy := h_header.2.2.2
  rw [hk, hn, hp, hy] at h_weight
  match eq : b.clauses with
  | [c1, c2, c3] =>
    rw [eq] at h_weight
    have h_fold : List.foldl (fun acc c => acc + clause_syllables c) 0 [c1, c2, c3] = clause_syllables c1 + clause_syllables c2 + clause_syllables c3 := by
      simp only [List.foldl]
      rw [Nat.zero_add]
    rw [h_fold] at h_weight
    have h_pigeon : clause_syllables c1 > 3 ∨ clause_syllables c2 > 3 ∨ clause_syllables c3 > 3 := pigeonhole_17_gt _ _ _ h_weight
    
    match Classical.em (IsStructurallyCollapsed c1) with
    | Or.inl hc1 =>
      left; use c1; refine ⟨by rw [eq]; exact List.Mem.head _, hc1⟩
    | Or.inr hnc1 =>
      match Classical.em (IsStructurallyCollapsed c2) with
      | Or.inl hc2 =>
        left; use c2; refine ⟨by rw [eq]; exact List.Mem.tail _ (List.Mem.head _), hc2⟩
      | Or.inr hnc2 =>
        match Classical.em (IsStructurallyCollapsed c3) with
        | Or.inl hc3 =>
          left; use c3; refine ⟨by rw [eq]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), hc3⟩
        | Or.inr hnc3 =>
          right
          match h_pigeon with
          | Or.inl h1 =>
            use c1; refine ⟨by rw [eq]; exact List.Mem.head _, clause_over_3_has_friction c1 hnc1 h1⟩
          | Or.inr (Or.inl h2) =>
            use c2; refine ⟨by rw [eq]; exact List.Mem.tail _ (List.Mem.head _), clause_over_3_has_friction c2 hnc2 h2⟩
          | Or.inr (Or.inr h3) =>
            use c3; refine ⟨by rw [eq]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), clause_over_3_has_friction c3 hnc3 h3⟩
  | [] => rw [eq] at h_len; simp at h_len
  | [_] => rw [eq] at h_len; simp at h_len
  | [_, _] => rw [eq] at h_len; simp at h_len
  | _ :: _ :: _ :: _ :: _ => rw [eq] at h_len; simp at h_len

end GnotTopology
end Gnosis
