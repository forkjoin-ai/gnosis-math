import Init
-- MakoQueryInjectionRisk.lean
-- Anti-thesis: Mako template engine (Python) rendering of user-controlled
-- template strings carries no code execution risk.
-- Refutation: Mako's <%...%> and ${...} tags execute Python expressions,
-- so user-controlled templates yield a strictly positive vulnerability window.

namespace MakoQueryInjection

-- SSTI risk: Template(user_template).render() executes Python
def makoSstiRisk (templateLen : Nat) (staticFile : Bool) : Nat :=
  if staticFile then 0 else templateLen + 1

-- Static template file rendering is safe
theorem mako_static_template_safe (n : Nat) :
    makoSstiRisk n true = 0 := by { simp [makoSstiRisk]

-- Template(user_string).render() is strictly vulnerable
theorem mako_user_template_risk (n : Nat) :
    0 < makoSstiRisk n false := by
  simp [makoSstiRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- <%! ...%> module-level code block injection
def moduleBlockRisk (codeLen : Nat) (blocked : Bool) : Nat :=
  if blocked then 0 else codeLen + 1

theorem mako_module_block_blocked_safe (n : Nat) :
    moduleBlockRisk n true = 0 := by { simp [moduleBlockRisk]

theorem mako_module_block_allowed_risk (n : Nat) :
    0 < moduleBlockRisk n false := by
  simp [moduleBlockRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- ${expr} expression injection: user-controlled expression in ${}
def exprBlockRisk (exprLen : Nat) (filtered : Bool) : Nat :=
  if filtered then 0 else exprLen + 1

theorem mako_expr_filtered_safe (n : Nat) :
    exprBlockRisk n true = 0 := by { simp [exprBlockRisk]

theorem mako_expr_unfiltered_risk (n : Nat) :
    0 < exprBlockRisk n false := by
  simp [exprBlockRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Template lookup injection: TemplateLookup with user-controlled filename
def lookupFilenameRisk (nameLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else nameLen + 1

theorem mako_lookup_validated_safe (n : Nat) :
    lookupFilenameRisk n true = 0 := by { simp [lookupFilenameRisk]

theorem mako_lookup_unvalidated_risk (n : Nat) :
    0 < lookupFilenameRisk n false := by
  simp [lookupFilenameRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- <%def> block injection: user-controlled def block names
def defBlockRisk (nameLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else nameLen + 1

theorem mako_def_allowlisted_safe (n : Nat) :
    defBlockRisk n true = 0 := by { simp [defBlockRisk]

theorem mako_def_unvalidated_risk (n : Nat) :
    0 < defBlockRisk n false := by
  simp [defBlockRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in template length
theorem mako_ssti_risk_monotone (n m : Nat) (h : n ≤ m) :
    makoSstiRisk n false ≤ makoSstiRisk m false := by { simp [makoSstiRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires static template files AND blocked module blocks
def netMakoRisk (inputLen : Nat) (staticFile : Bool) (moduleBlocked : Bool) : Nat :=
  makoSstiRisk inputLen staticFile + moduleBlockRisk inputLen moduleBlocked

theorem mako_net_risk_zero_fully_mitigated (n : Nat) :
    netMakoRisk n true true = 0 := by { simp [netMakoRisk, makoSstiRisk, moduleBlockRisk]

theorem mako_net_risk_pos_unmitigated (n : Nat) :
    0 < netMakoRisk n false false := by
  simp [netMakoRisk, makoSstiRisk, moduleBlockRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end MakoQueryInjection
