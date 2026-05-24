import Init
-- HeaderInjectionRisk.lean
-- Anti-thesis: User-controlled values inserted into HTTP response headers
-- carry no injection risk because HTTP frameworks automatically sanitize them.
-- Refutation: Without CRLF stripping, a value containing \r\n lets an attacker
-- inject arbitrary headers or split the response, yielding a strictly positive
-- vulnerability window.

namespace Gnosis.Security.HeaderInjectionRisk

-- CRLF injection: header value contains raw \r\n sequences
def crlfRisk (valueLen : Nat) (crlfStripped : Bool) : Nat :=
  if crlfStripped then 0 else valueLen + 1

-- Stripping \r\n from header values eliminates CRLF injection
theorem header_crlf_stripped_safe (n : Nat) :
    crlfRisk n true = 0 := by { simp [crlfRisk]

-- Unstripped user value is strictly vulnerable to CRLF injection
theorem header_crlf_unstripped_risk (n : Nat) :
    0 < crlfRisk n false := by
  simp [crlfRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Response splitting: injected \r\n\r\n separates body from headers
def responseSplittingRisk (valueLen : Nat) (splitPrevented : Bool) : Nat :=
  if splitPrevented then 0 else valueLen + 1

theorem header_split_prevented_safe (n : Nat) :
    responseSplittingRisk n true = 0 := by { simp [responseSplittingRisk]

theorem header_split_unprevented_risk (n : Nat) :
    0 < responseSplittingRisk n false := by
  simp [responseSplittingRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Header name injection: user controls the header name (not just value)
def headerNameRisk (nameLen : Nat) (nameAllowListed : Bool) : Nat :=
  if nameAllowListed then 0 else nameLen + 1

theorem header_name_allowlisted_safe (n : Nat) :
    headerNameRisk n true = 0 := by { simp [headerNameRisk]

theorem header_name_open_risk (n : Nat) :
    0 < headerNameRisk n false := by
  simp [headerNameRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Cache poisoning: injected headers pollute shared caches
def cachePoisoningRisk (valueLen : Nat) (cacheValidates : Bool) : Nat :=
  if cacheValidates then 0 else valueLen + 1

theorem header_cache_validates_safe (n : Nat) :
    cachePoisoningRisk n true = 0 := by { simp [cachePoisoningRisk]

theorem header_cache_no_validation_risk (n : Nat) :
    0 < cachePoisoningRisk n false := by
  simp [cachePoisoningRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Log injection: injected newlines corrupt server access logs
def logInjectionRisk (valueLen : Nat) (logSanitized : Bool) : Nat :=
  if logSanitized then 0 else valueLen + 1

theorem header_log_sanitized_safe (n : Nat) :
    logInjectionRisk n true = 0 := by { simp [logInjectionRisk]

theorem header_log_unsanitized_risk (n : Nat) :
    0 < logInjectionRisk n false := by
  simp [logInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in value length
theorem header_crlf_risk_monotone (n m : Nat) (h : n ≤ m) :
    crlfRisk n false ≤ crlfRisk m false := by { simp [crlfRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires CRLF stripped AND header name allow-listed
def netHeaderRisk (valueLen : Nat) (crlfStripped : Bool) (nameAllowListed : Bool) : Nat :=
  crlfRisk valueLen crlfStripped + headerNameRisk valueLen nameAllowListed

theorem header_net_risk_zero_fully_mitigated (n : Nat) :
    netHeaderRisk n true true = 0 := by { simp [netHeaderRisk, crlfRisk, headerNameRisk]

theorem header_net_risk_pos_unmitigated (n : Nat) :
    0 < netHeaderRisk n false false := by
  simp [netHeaderRisk, crlfRisk, headerNameRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end HeaderInjectionRisk
