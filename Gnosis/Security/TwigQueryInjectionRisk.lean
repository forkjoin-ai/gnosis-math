import Init
-- TwigQueryInjectionRisk.lean
-- Anti-thesis: Twig template engine (PHP) rendering of user-controlled
-- template strings carries no code execution risk.
-- Refutation: twig->createTemplate(user_template)->render() executes Twig
-- expressions, yielding a strictly positive vulnerability window.

namespace TwigQueryInjection

-- SSTI risk: createTemplate(user_template)->render() executes Twig code
def twigSstiRisk (templateLen : Nat) (staticFile : Bool) : Nat :=
  if staticFile then 0 else templateLen + 1

-- Static template file (twig->load('file.twig')) is safe
theorem twig_static_template_safe (n : Nat) :
    twigSstiRisk n true = 0 := by { simp [twigSstiRisk]

-- createTemplate(user_string) is strictly vulnerable
theorem twig_create_template_risk (n : Nat) :
    0 < twigSstiRisk n false := by
  simp [twigSstiRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Sandbox escape: Twig sandbox policy bypass via attribute access
def sandboxEscapeRisk (inputLen : Nat) (sandboxEnabled : Bool) : Nat :=
  if sandboxEnabled then 0 else inputLen + 1

theorem twig_sandbox_enabled_safe (n : Nat) :
    sandboxEscapeRisk n true = 0 := by { simp [sandboxEscapeRisk]

theorem twig_no_sandbox_full_risk (n : Nat) :
    0 < sandboxEscapeRisk n false := by
  simp [sandboxEscapeRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Filter injection: user-controlled filter in {{ value | user_filter }}
def filterInjectionRisk (filterLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else filterLen + 1

theorem twig_filter_allowlisted_safe (n : Nat) :
    filterInjectionRisk n true = 0 := by { simp [filterInjectionRisk]

theorem twig_filter_unvalidated_risk (n : Nat) :
    0 < filterInjectionRisk n false := by
  simp [filterInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Function injection: user-controlled function call in {{ user_func() }}
def functionInjectionRisk (funcLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else funcLen + 1

theorem twig_function_allowlisted_safe (n : Nat) :
    functionInjectionRisk n true = 0 := by { simp [functionInjectionRisk]

theorem twig_function_unvalidated_risk (n : Nat) :
    0 < functionInjectionRisk n false := by
  simp [functionInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Macro injection: user-controlled macro definition or call
def macroInjectionRisk (macroLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else macroLen + 1

theorem twig_macro_allowlisted_safe (n : Nat) :
    macroInjectionRisk n true = 0 := by { simp [macroInjectionRisk]

theorem twig_macro_unvalidated_risk (n : Nat) :
    0 < macroInjectionRisk n false := by
  simp [macroInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in template length
theorem twig_ssti_risk_monotone (n m : Nat) (h : n ≤ m) :
    twigSstiRisk n false ≤ twigSstiRisk m false := by { simp [twigSstiRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires static templates AND sandbox enabled
def netTwigRisk (inputLen : Nat) (staticFile : Bool) (sandboxEnabled : Bool) : Nat :=
  twigSstiRisk inputLen staticFile + sandboxEscapeRisk inputLen sandboxEnabled

theorem twig_net_risk_zero_fully_mitigated (n : Nat) :
    netTwigRisk n true true = 0 := by { simp [netTwigRisk, twigSstiRisk, sandboxEscapeRisk]

theorem twig_net_risk_pos_unmitigated (n : Nat) :
    0 < netTwigRisk n false false := by
  simp [netTwigRisk, twigSstiRisk, sandboxEscapeRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end TwigQueryInjection
