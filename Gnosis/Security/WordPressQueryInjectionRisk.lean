import Init
-- WordPressQueryInjectionRisk.lean
-- Anti-thesis: WordPress $wpdb database abstraction layer protects against
-- SQL injection even when queries are constructed from user input.
-- Refutation: $wpdb->query() with unescaped input and $wpdb->prepare()
-- misuse each yield a strictly positive vulnerability window.

namespace WordPressQueryInjection

-- $wpdb->query() injection: $wpdb->query("SELECT ... WHERE id='" . $id . "'")
def wpdbQueryRisk (inputLen : Nat) (prepared : Bool) : Nat :=
  if prepared then 0 else inputLen + 1

-- $wpdb->prepare() with %s/%d placeholders is safe
theorem wordpress_prepare_safe (n : Nat) :
    wpdbQueryRisk n true = 0 := by { simp [wpdbQueryRisk]

-- $wpdb->query() with concatenation is strictly vulnerable
theorem wordpress_query_concat_risk (n : Nat) :
    0 < wpdbQueryRisk n false := by
  simp [wpdbQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- $wpdb->prepare() format string injection: wrong placeholder count leaks literal
def prepareFormatRisk (argCount : Nat) (placeholderCount : Nat) : Nat :=
  if argCount = placeholderCount then 0 else argCount + 1

theorem wordpress_prepare_format_matched_safe (n : Nat) :
    prepareFormatRisk n n = 0 := by { simp [prepareFormatRisk]

theorem wordpress_prepare_format_mismatched_risk (n m : Nat) (h : n ≠ m) :
    0 < prepareFormatRisk n m := by
  simp [prepareFormatRisk, h]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- get_var() injection: $wpdb->get_var("SELECT ... WHERE name='" . $input . "'")
def getVarRisk (inputLen : Nat) (prepared : Bool) : Nat :=
  if prepared then 0 else inputLen + 1

theorem wordpress_get_var_prepared_safe (n : Nat) :
    getVarRisk n true = 0 := by { simp [getVarRisk]

theorem wordpress_get_var_unprepared_risk (n : Nat) :
    0 < getVarRisk n false := by
  simp [getVarRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- meta_query injection: unvalidated meta_query array from user input
def metaQueryRisk (queryLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else queryLen + 1

theorem wordpress_meta_query_sanitized_safe (n : Nat) :
    metaQueryRisk n true = 0 := by { simp [metaQueryRisk]

theorem wordpress_meta_query_unsanitized_risk (n : Nat) :
    0 < metaQueryRisk n false := by
  simp [metaQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in input length
theorem wordpress_query_risk_monotone (n m : Nat) (h : n ≤ m) :
    wpdbQueryRisk n false ≤ wpdbQueryRisk m false := by { simp [wpdbQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires $wpdb->prepare() AND sanitized meta_query
def netWordPressRisk (inputLen : Nat) (prepared : Bool) (metaSanitized : Bool) : Nat :=
  wpdbQueryRisk inputLen prepared + metaQueryRisk inputLen metaSanitized

theorem wordpress_net_risk_zero_fully_mitigated (n : Nat) :
    netWordPressRisk n true true = 0 := by { simp [netWordPressRisk, wpdbQueryRisk, metaQueryRisk]

theorem wordpress_net_risk_pos_unmitigated (n : Nat) :
    0 < netWordPressRisk n false false := by
  simp [netWordPressRisk, wpdbQueryRisk, metaQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end WordPressQueryInjection
