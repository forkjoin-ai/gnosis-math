import Init
-- SetCookieInjectionRisk.lean
-- Anti-thesis: User-controlled data in Set-Cookie headers carries no injection
-- risk because browsers ignore malformed cookie syntax.
-- Refutation: An unescaped semicolon or CRLF in a cookie name or value allows
-- an attacker to inject additional cookie attributes or split the response,
-- yielding a strictly positive vulnerability window.

namespace Gnosis.Security.SetCookieInjectionRisk

-- Cookie value injection: unescaped semicolons allow attribute smuggling
def cookieValueRisk (valueLen : Nat) (valueEncoded : Bool) : Nat :=
  if valueEncoded then 0 else valueLen + 1

-- Proper URL-encoding of cookie value eliminates attribute injection
theorem cookie_value_encoded_safe (n : Nat) :
    cookieValueRisk n true = 0 := by { simp [cookieValueRisk]

-- Unencoded cookie value is strictly vulnerable
theorem cookie_value_unencoded_risk (n : Nat) :
    0 < cookieValueRisk n false := by
  simp [cookieValueRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Cookie name injection: user controls cookie name containing = or ;
def cookieNameRisk (nameLen : Nat) (nameValidated : Bool) : Nat :=
  if nameValidated then 0 else nameLen + 1

theorem cookie_name_validated_safe (n : Nat) :
    cookieNameRisk n true = 0 := by { simp [cookieNameRisk]

theorem cookie_name_unvalidated_risk (n : Nat) :
    0 < cookieNameRisk n false := by
  simp [cookieNameRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- HttpOnly missing: cookie accessible via document.cookie (XSS amplifier)
def httpOnlyRisk (sensitive : Bool) (httpOnlySet : Bool) : Nat :=
  if !sensitive || httpOnlySet then 0 else 1

theorem cookie_httponly_set_safe :
    httpOnlyRisk true true = 0 := by { simp [httpOnlyRisk]

theorem cookie_httponly_missing_risk :
    0 < httpOnlyRisk true false := by
  simp [httpOnlyRisk]

-- Secure flag missing: cookie transmitted over HTTP (MITM exposure)
def secureFlagRisk (isHttps : Bool) (secureFlagSet : Bool) : Nat :=
  if !isHttps || secureFlagSet then 0 else 1

theorem cookie_secure_set_safe :
    secureFlagRisk true true = 0 := by
  simp [secureFlagRisk]

theorem cookie_secure_missing_risk :
    0 < secureFlagRisk true false := by
  simp [secureFlagRisk]

-- SameSite missing: cookie sent cross-origin (CSRF amplifier)
def sameSiteRisk (crossOriginAllowed : Bool) (sameSiteSet : Bool) : Nat :=
  if !crossOriginAllowed || sameSiteSet then 0 else 1

theorem cookie_samesite_set_safe :
    sameSiteRisk true true = 0 := by
  simp [sameSiteRisk]

theorem cookie_samesite_missing_risk :
    0 < sameSiteRisk true false := by
  simp [sameSiteRisk]

-- Risk monotone in value length
theorem cookie_value_risk_monotone (n m : Nat) (h : n ≤ m) :
    cookieValueRisk n false ≤ cookieValueRisk m false := by
  simp [cookieValueRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires encoding AND HttpOnly AND Secure
def netCookieRisk (valueLen : Nat) (valueEncoded : Bool) (httpOnly : Bool) (secure : Bool) : Nat :=
  cookieValueRisk valueLen valueEncoded +
  httpOnlyRisk true httpOnly +
  secureFlagRisk true secure

theorem cookie_net_risk_zero_fully_mitigated (n : Nat) :
    netCookieRisk n true true true = 0 := by { simp [netCookieRisk, cookieValueRisk, httpOnlyRisk, secureFlagRisk]

theorem cookie_net_risk_pos_unmitigated (n : Nat) :
    0 < netCookieRisk n false false false := by
  simp [netCookieRisk, cookieValueRisk, httpOnlyRisk, secureFlagRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end SetCookieInjectionRisk
