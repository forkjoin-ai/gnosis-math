import Init
import Gnosis.RankingFrfBridge
import Gnosis.FrfInherentGestalt
import Gnosis.FrfWitnessTower

/-!
# Triton primary constraint — triangle-first carrier, pentadic loom, hostile schedules

`Triton` is the spine; `Nat` appears only as **`shadow`**. `void` is **no fork**.

`WellFormed` forbids `cons void ⟨0⟩`.

`pentFork` uniqueness; `loomEmbed`/`loomSplit` for `Fin 15 ≃ Fin 5 × Fin 3`.

Hostile commuting merges on swapped blocks.

Init-only. Zero `sorry`.
-/

namespace Gnosis
namespace TritonAudacious

open Gnosis.RankingFrfBridge
open Gnosis.FrfInherentGestalt
open Gnosis.FrfWitnessTower

inductive Triton : Type where
  | void : Triton
  | cons : Triton → Fin 3 → Triton

def Triton.shadow : Triton → Nat
  | void => 0
  | cons t r => r.val + 3 * t.shadow

def Triton.WellFormed : Triton → Prop
  | void => True
  | cons t r => WellFormed t ∧ ¬ (t = void ∧ r.val = 0)

def Triton.fromShadow (n : Nat) : Triton :=
  if h : n = 0 then
    void
  else
    have _lt : n / 3 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : 1 < 3)
    cons (fromShadow (n / 3)) ⟨n % 3, Nat.mod_lt n (by decide : 0 < 3)⟩
termination_by n

theorem Triton.cons_ne_void (t : Triton) (r : Fin 3) : cons t r ≠ void :=
  fun he => nomatch he

theorem Triton.shadow_void : void.shadow = 0 :=
  rfl

theorem Triton.shadow_cons (t : Triton) (r : Fin 3) :
    (cons t r).shadow = frfFork t.shadow r.val := by
  simp [shadow, frfFork]
  rw [Nat.add_comm]

theorem Triton.fromShadow_eq_void_iff (m : Nat) : fromShadow m = void ↔ m = 0 := by
  constructor
  · intro he
    by_cases hm : m = 0
    · exact hm
    · unfold fromShadow at he
      simp only [dif_neg hm] at he
      exact False.elim (Ne.elim (cons_ne_void _ _) he)
  · rintro rfl
    delta fromShadow
    rfl

theorem Triton.shadow_fromShadow (n : Nat) : (fromShadow n).shadow = n := by
  refine Nat.strongRecOn n fun n ih => ?_
  unfold fromShadow
  by_cases h : n = 0
  · subst h
    rfl
  · simp only [dif_neg h]
    simp only [shadow]
    rw [ih (n / 3) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : 1 < 3))]
    calc
      n % 3 + 3 * (n / 3) = 3 * (n / 3) + n % 3 := Nat.add_comm _ _
      _ = n := Nat.div_add_mod n 3

theorem Triton.wellFormed_fromShadow (n : Nat) : WellFormed (fromShadow n) := by
  refine Nat.strongRecOn n fun n ih => ?_
  unfold fromShadow
  by_cases h : n = 0
  · subst h
    trivial
  · simp only [dif_neg h]
    refine And.intro (ih (n / 3) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : 1 < 3))) ?_
    intro ⟨hv, hd⟩
    have hn3 : n / 3 = 0 := (fromShadow_eq_void_iff (n / 3)).mp hv
    have hnlt : n < 3 := Nat.lt_of_div_eq_zero (by decide : 0 < 3) hn3
    have hnmod : n % 3 = 0 := hd
    have hn0 : n = 0 := by
      rcases n with _ | _ | _ | m
      · rfl
      · simp at hnmod
      · simp at hnmod
      · simp [Nat.succ_lt_succ_iff, Nat.succ_lt_succ_iff] at hnlt
    exact h hn0

private theorem Triton.shadow_pos_of_wf_cons {t : Triton} {r : Fin 3}
    (hwf : WellFormed (cons t r)) : 0 < (cons t r).shadow := by
  rcases hwf with ⟨hwfTail, hnf⟩
  rcases t with _ | ⟨t2, r2⟩
  · simp only [shadow]
    exact Nat.pos_of_ne_zero (fun hz => hnf ⟨rfl, hz⟩)
  · simp only [shadow]
    have hb : 0 < (cons t2 r2).shadow := shadow_pos_of_wf_cons hwfTail
    by_cases hrz : r.val = 0
    · rw [hrz, Nat.zero_add]
      exact Nat.mul_pos (by decide : 0 < 3) hb
    · exact Nat.add_pos_left (Nat.pos_of_ne_zero hrz) (3 * (cons t2 r2).shadow)

theorem Triton.fromShadow_shadow {t : Triton} (hwf : WellFormed t) :
    fromShadow t.shadow = t := by
  cases t
  case void =>
    simp only [shadow]
    delta fromShadow
    rfl
  case cons t r =>
      have hwfc := hwf
      rcases hwf with ⟨hwf_tail, _⟩
      have hnz := Nat.ne_of_gt (shadow_pos_of_wf_cons hwfc)
      unfold fromShadow
      simp only [dif_neg hnz]
      have hs := shadow_cons t r
      have hq : (cons t r).shadow / 3 = t.shadow := by
        rw [hs]
        exact frf_fold_recovers_base t.shadow r.val r.isLt
      have hrmod : (cons t r).shadow % 3 = r.val := by
        rw [hs]
        unfold frfFork
        simp [Nat.mod_eq_of_lt r.isLt]
      have hqfp : fromShadow ((cons t r).shadow / 3) = t := by
        rw [hq]
        exact fromShadow_shadow hwf_tail
      have hm : (⟨(cons t r).shadow % 3, Nat.mod_lt _ (by decide : 0 < 3)⟩ : Fin 3) = r :=
        Fin.ext hrmod
      rw [hqfp, hm]

theorem Triton.cons_void_zero_not_WellFormed :
    ¬ WellFormed (cons void ⟨0, by decide⟩) := by
  simp [WellFormed]

/-! ## Pentagon spine -/

inductive Pent : Type where
  | void : Pent
  | cons : Pent → Fin 5 → Pent

def Pent.shadow : Pent → Nat
  | void => 0
  | cons p r => r.val + 5 * p.shadow

def Pent.pentFork (k : Nat) (r : Fin 5) : Nat :=
  5 * k + r.val

theorem Pent.shadow_cons (p : Pent) (r : Fin 5) :
    Pent.shadow (Pent.cons p r) = pentFork p.shadow r := by
  dsimp [shadow, pentFork]
  rw [Nat.add_comm]

def Pent.fromShadow (n : Nat) : Pent :=
  if h : n = 0 then
    void
  else
    have _lt : n / 5 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : 1 < 5)
    cons (fromShadow (n / 5)) ⟨n % 5, Nat.mod_lt n (by decide : 0 < 5)⟩
termination_by n

theorem Pent.pent_fork_unique (k k' : Nat) (r r' : Fin 5)
    (h : pentFork k r = pentFork k' r') : k = k' ∧ r = r' := by
  unfold pentFork at h
  have hr : r.val < 5 := r.isLt
  have hr' : r'.val < 5 := r'.isLt
  have hl : (5 * k + r.val) % 5 = r.val % 5 := by
    simp [Nat.mul_comm 5 k, Nat.add_comm]
  have hrEq : r.val = r'.val := by
    calc
      r.val = r.val % 5 := (Nat.mod_eq_of_lt hr).symm
      _ = (5 * k + r.val) % 5 := hl.symm
      _ = (5 * k' + r'.val) % 5 := congrArg (fun n => n % 5) h
      _ = r'.val % 5 := by simp [Nat.mul_comm 5 k', Nat.add_comm]
      _ = r'.val := Nat.mod_eq_of_lt hr'
  have hrFin : r = r' := Fin.ext hrEq
  subst hrFin
  have hk : 5 * k = 5 * k' := Nat.add_right_cancel h
  exact ⟨Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5) hk, rfl⟩

/-! ## Loom -/

private theorem loom_embed_lt_fifteen (i : Fin 5) (d : Fin 3) :
    i.val * 3 + d.val < 15 := by
  have hi : i.val ≤ 4 := Nat.le_of_lt_succ i.isLt
  have hd : d.val ≤ 2 := Nat.le_of_lt_succ d.isLt
  have hsum : i.val * 3 + d.val ≤ 4 * 3 + 2 :=
    Nat.add_le_add (Nat.mul_le_mul_right 3 hi) hd
  exact Nat.lt_of_le_of_lt hsum (by decide)

def loomEmbed (i : Fin 5) (d : Fin 3) : Fin 15 :=
  ⟨i.val * 3 + d.val, loom_embed_lt_fifteen i d⟩

def loomSplit (k : Fin 15) : Fin 5 × Fin 3 :=
  ⟨⟨k.val / 3, (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mpr k.isLt⟩,
    ⟨k.val % 3, Nat.mod_lt _ (by decide : 0 < 3)⟩⟩

theorem loom_embed_split (k : Fin 15) : loomEmbed (loomSplit k).1 (loomSplit k).2 = k := by
  apply Fin.ext
  dsimp [loomEmbed, loomSplit]
  calc
    k.val / 3 * 3 + k.val % 3 = 3 * (k.val / 3) + k.val % 3 := by rw [Nat.mul_comm]
    _ = k.val := Nat.div_add_mod _ _

theorem loom_split_embed (i : Fin 5) (d : Fin 3) :
    loomSplit (loomEmbed i d) = (i, d) := by
  refine Prod.ext ?_ ?_
  · apply Fin.ext
    dsimp [loomEmbed, loomSplit]
    rw [Nat.add_comm (i.val * 3) d.val]
    rw [Nat.add_mul_div_right _ _ (by decide : 0 < 3)]
    rw [Nat.div_eq_of_lt d.isLt]
    simp [Nat.zero_add]
  · apply Fin.ext
    dsimp [loomEmbed, loomSplit]
    rw [Nat.add_comm (i.val * 3) d.val]
    simp [Nat.mod_eq_of_lt d.isLt]

/-! ## Hostile block interchange -/

theorem xor_merge_append_comm (xs ys : List Bool) :
    xorMerge (xs ++ ys) = xorMerge (ys ++ xs) := by
  rw [xorMerge_append, xorMerge_append, Bool.xor_comm]

theorem triad_merge_append_comm (xs ys : List (Fin 3)) :
    triadMerge (xs ++ ys) = triadMerge (ys ++ xs) := by
  rw [triad_merge_append, triad_merge_append, triadAdd_comm]

/-! ## Certificate -/

theorem triton_audacious_certificate (n : Nat) (t : Triton) (hwf : Triton.WellFormed t)
    (xs ys : List Bool) (xs' ys' : List (Fin 3)) (i : Fin 5) (d : Fin 3) (k : Fin 15) :
    Triton.shadow (Triton.fromShadow n) = n ∧
      Triton.WellFormed (Triton.fromShadow n) ∧
        Triton.fromShadow (Triton.shadow t) = t ∧
          xorMerge (xs ++ ys) = xorMerge (ys ++ xs) ∧
            triadMerge (xs' ++ ys') = triadMerge (ys' ++ xs') ∧
              loomSplit (loomEmbed i d) = (i, d) ∧
                loomEmbed (loomSplit k).1 (loomSplit k).2 = k :=
  ⟨Triton.shadow_fromShadow n,
    Triton.wellFormed_fromShadow n,
    Triton.fromShadow_shadow hwf,
    xor_merge_append_comm xs ys,
    triad_merge_append_comm xs' ys',
    loom_split_embed i d,
    loom_embed_split k⟩

end TritonAudacious
end Gnosis
