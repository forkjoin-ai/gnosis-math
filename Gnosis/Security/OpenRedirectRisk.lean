import Init
-- OpenRedirectRisk.lean
-- Anti-thesis: Redirecting users to a URL from a query parameter carries no
-- risk because browsers warn users before following external redirects.
-- Refutation: Without allow-list validation of the destination, an attacker
-- crafts a trusted-looking link that redirects to a phishing site, yielding a
-- strictly positive vulnerability window.

namespace Gnosis.Security.OpenRedirectRisk

-- Open redirect: Location header set from unvalidated user parameter
def openRedirectRisk (urlLen : Nat) (destinationValidated : Bool) : Nat :=
  if destinationValidated then 0 else urlLen + 1

-- Allow-list validation of redirect destination eliminates open redirect
theorem redirect_destination_validated_safe (n : Nat) :
    openRedirectRisk n true = 0 := by { simp [openRedirectRisk]

-- Unvalidated redirect destination is strictly vulnerable
theorem redirect_destination_unvalidated_risk (n : Nat) :
    0 < openRedirectRisk n false := by
  simp [openRedirectRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Relative-only redirect: reject absolute URLs in redirect target
def absoluteUrlRisk (urlLen : Nat) (absoluteRejected : Bool) : Nat :=
  if absoluteRejected then 0 else urlLen + 1

theorem redirect_absolute_rejected_safe (n : Nat) :
    absoluteUrlRisk n true = 0 := by { simp [absoluteUrlRisk]

theorem redirect_absolute_allowed_risk (n : Nat) :
    0 < absoluteUrlRisk n false := by
  simp [absoluteUrlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Protocol-relative URL bypass: //evil.com bypasses http:// check
def protocolRelativeRisk (urlLen : Nat) (protocolRelativeBlocked : Bool) : Nat :=
  if protocolRelativeBlocked then 0 else urlLen + 1

theorem redirect_protocol_relative_blocked_safe (n : Nat) :
    protocolRelativeRisk n true = 0 := by { simp [protocolRelativeRisk]

theorem redirect_protocol_relative_open_risk (n : Nat) :
    0 < protocolRelativeRisk n false := by
  simp [protocolRelativeRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- URL confusion: https://trusted.com@evil.com/ passes naive prefix check
def urlConfusionRisk (urlLen : Nat) (hostExtractedAndChecked : Bool) : Nat :=
  if hostExtractedAndChecked then 0 else urlLen + 1

theorem redirect_host_checked_safe (n : Nat) :
    urlConfusionRisk n true = 0 := by { simp [urlConfusionRisk]

theorem redirect_host_unchecked_risk (n : Nat) :
    0 < urlConfusionRisk n false := by
  simp [urlConfusionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Double-encoded slash: %2f%2fevil.com bypasses single-decode check
def doubleEncodingRisk (urlLen : Nat) (fullyDecoded : Bool) : Nat :=
  if fullyDecoded then 0 else urlLen + 1

theorem redirect_fully_decoded_safe (n : Nat) :
    doubleEncodingRisk n true = 0 := by { simp [doubleEncodingRisk]

theorem redirect_double_encoding_bypass_risk (n : Nat) :
    0 < doubleEncodingRisk n false := by
  simp [doubleEncodingRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in URL length
theorem redirect_risk_monotone (n m : Nat) (h : n ≤ m) :
    openRedirectRisk n false ≤ openRedirectRisk m false := by { simp [openRedirectRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires destination validated AND absolute URLs rejected
def netRedirectRisk (urlLen : Nat) (destValidated : Bool) (absoluteRejected : Bool) : Nat :=
  openRedirectRisk urlLen destValidated + absoluteUrlRisk urlLen absoluteRejected

theorem redirect_net_risk_zero_fully_mitigated (n : Nat) :
    netRedirectRisk n true true = 0 := by { simp [netRedirectRisk, openRedirectRisk, absoluteUrlRisk]

theorem redirect_net_risk_pos_unmitigated (n : Nat) :
    0 < netRedirectRisk n false false := by
  simp [netRedirectRisk, openRedirectRisk, absoluteUrlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end OpenRedirectRisk
