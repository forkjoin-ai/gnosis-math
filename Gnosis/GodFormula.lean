import Init

namespace Gnosis

/-!
# God Formula — Init-only, +1-pure kernel

Single source for the universal weighting rule

  w(R, v) = R - min(v, R) + 1

and its base identities. **Every proof in this file uses only definitional
unfolding plus Init-level `Nat` lemmas that are themselves provable by
`+1` induction on `Nat`** — no `omega`, no `decide`, no `simp`. The kernel
is therefore self-bootstrapping from `Nat.succ` / structural recursion.

Downstream files in `Gnosis/` should `import Gnosis.GodFormula` and `open Gnosis`
instead of redefining `godWeight` locally, so the formula's definition stays
pinned to one canonical form.

## Topological derivation

`Gnosis.BuleSpider` derives this formula from the BuleSpider primitives:
build the budget by `R` clinamen lifts on the waste face, apply `v`
contracts (vent's per-face filter), apply the universal pentad-closure
`+1` lift, project to face score. See
`god_formula_is_pentad_face_projection` for the master derivation, and
`pentad_costs_clinamen_plus_one_with_aperiodicity` for the proof that
the trailing `+1` is exactly the cost of 5-foldness — the same `+1`
that the `UniversalClinamenPlusOne` catalog records as universal across
seven independent phase reconstructions.
-/

/-- The God Formula: `w(R, v) = R − min(v, R) + 1`.

    Read as: weight = budget − rejection (clamped to budget) + clinamen. -/
def godWeight (R v : Nat) : Nat := R - min v R + 1

/-- Conservation: when rejections fit the budget, `w + v = R + 1`.
    Proof: unfold, collapse `min`, commute `+`, then `Nat.sub_add_cancel`. -/
theorem godWeight_conservation (R v : Nat) (h : v ≤ R) :
    godWeight R v + v = R + 1 := by
  show R - min v R + 1 + v = R + 1
  rw [Nat.min_eq_left h, Nat.add_right_comm, Nat.sub_add_cancel h]

/-- Ceiling: zero rejection ⇒ maximum weight `R + 1`. -/
theorem godWeight_ceiling (R : Nat) : godWeight R 0 = R + 1 := by
  show R - min 0 R + 1 = R + 1
  rw [Nat.min_eq_left (Nat.zero_le R), Nat.sub_zero]

/-- Floor / clinamen: full rejection ⇒ weight collapses to `1`. -/
theorem godWeight_floor (R : Nat) : godWeight R R = 1 := by
  show R - min R R + 1 = 1
  rw [Nat.min_self, Nat.sub_self]

/-- Strict positivity (the clinamen +1): every weight is at least `1`. -/
theorem godWeight_pos (R v : Nat) : 1 ≤ godWeight R v := by
  show 1 ≤ R - min v R + 1
  exact Nat.le_add_left 1 (R - min v R)

/-- Upper bound: `w ≤ R + 1`. -/
theorem godWeight_le_succ (R v : Nat) : godWeight R v ≤ R + 1 := by
  show R - min v R + 1 ≤ R + 1
  exact Nat.add_le_add_right (Nat.sub_le R (min v R)) 1

/-- Sandwich: `1 ≤ w(R, v) ≤ R + 1` always. -/
theorem godWeight_sandwich (R v : Nat) :
    1 ≤ godWeight R v ∧ godWeight R v ≤ R + 1 :=
  ⟨godWeight_pos R v, godWeight_le_succ R v⟩

/-- Antitone in `v`: more rejection ⇒ less weight. -/
theorem godWeight_antitone (R v₁ v₂ : Nat) (h₁ : v₁ ≤ R) (h₂ : v₂ ≤ R)
    (h : v₁ ≤ v₂) : godWeight R v₂ ≤ godWeight R v₁ := by
  show R - min v₂ R + 1 ≤ R - min v₁ R + 1
  rw [Nat.min_eq_left h₁, Nat.min_eq_left h₂]
  exact Nat.add_le_add_right (Nat.sub_le_sub_left h R) 1

/-- **Ordered weight gap**: along a fixed budget `R`, the drop in God-weight
    from the lower-rejection side `a` to the higher-rejection side `b` equals
    exactly the extra rejections `b - a` when `a ≤ b ≤ R`.

    This is the algebraic spine behind VCG-style externality accounting
    (`MechanismDesign.vcg_externality`) and Goodhart wedge bookkeeping
    (`Gnosis.GoodhartsLaw`). Init-only: same `Nat.sub_sub` / `Nat.sub_sub_self`
    chain as the mechanism-design proof. -/
theorem godWeight_ordered_difference (R a b : Nat)
    (ha : a ≤ R) (hb : b ≤ R) (hab : a ≤ b) :
    godWeight R a - godWeight R b = b - a := by
  unfold godWeight
  rw [Nat.min_eq_left ha, Nat.min_eq_left hb]
  rw [Nat.add_sub_add_right]
  have hAdd : a + (b - a) = b := Nat.add_sub_of_le hab
  have hKey : R - a - (b - a) = R - b := by
    rw [Nat.sub_sub, hAdd]
  rw [← hKey]
  have hCommAdd : (b - a) + a ≤ R := by
    rw [Nat.sub_add_cancel hab]; exact hb
  have hDeltaLe : b - a ≤ R - a := Nat.le_sub_of_add_le hCommAdd
  exact Nat.sub_sub_self hDeltaLe

/-! ## Internal consistency

These small theorems show that the four base laws above derive each other
where they overlap. If `lake build` accepts this file, the formula's
identity, conservation, ceiling, floor, and antitone laws all agree at the
boundary — the +1 algebra is self-consistent. -/

/-- Conservation specialised at `v = 0` recovers the ceiling. -/
theorem consistency_conservation_at_zero (R : Nat) :
    godWeight R 0 = R + 1 - 0 := by
  rw [godWeight_ceiling, Nat.sub_zero]

/-- Conservation specialised at `v = R` recovers the floor. -/
theorem consistency_conservation_at_R (R : Nat) :
    godWeight R R + R = R + 1 :=
  godWeight_conservation R R (Nat.le_refl R)

/-- Floor + conservation at `v = R` together force `1 + R = R + 1`. -/
theorem consistency_floor_via_conservation (R : Nat) :
    godWeight R R + R = R + 1 := by
  rw [godWeight_floor]
  exact Nat.add_comm 1 R

/-- Antitone applied between `0` and `R` recovers ceiling ≥ floor. -/
theorem consistency_ceiling_dominates_floor (R : Nat) :
    godWeight R R ≤ godWeight R 0 :=
  godWeight_antitone R 0 R (Nat.zero_le R) (Nat.le_refl R) (Nat.zero_le R)

/-- Legacy ledger anchor preserved for downstream references. -/
theorem god_formula_ledger_anchor : ∀ n : Nat, ∃ witness : Nat, witness = n := by
  intro n
  exact ⟨n, rfl⟩

end Gnosis
