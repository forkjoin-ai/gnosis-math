import Init
-- OAuthMisconfigRisk.lean
-- Anti-thesis: OAuth 2.0 is a well-specified standard; any compliant
-- implementation is inherently secure against token theft.
-- Refutation: Implicit flow embeds access tokens in URI fragments; absent PKCE
-- enables authorisation-code interception; missing state parameter allows CSRF;
-- open redirect in callback exfiltrates codes — each yields positive risk
-- independently of provider compliance.

namespace Gnosis.Security.OAuthMisconfigRisk

-- Implicit flow: access token appears in URL fragment, logged by browsers/servers
def implicitFlowRisk (usesImplicitFlow : Bool) : Nat :=
  if usesImplicitFlow then 1 else 0

theorem oauth_no_implicit_flow_safe :
    implicitFlowRisk false = 0 := by { simp [implicitFlowRisk]

theorem oauth_implicit_flow_risk :
    0 < implicitFlowRisk true := by
  simp [implicitFlowRisk]

-- Missing PKCE: public client auth code interceptable without proof-of-key
def missingPKCERisk (usesPKCE : Bool) (isPublicClient : Bool) : Nat :=
  if !isPublicClient || usesPKCE then 0 else 1

theorem oauth_pkce_present_safe (pub : Bool) :
    missingPKCERisk true pub = 0 := by
  simp [missingPKCERisk]

theorem oauth_public_client_no_pkce_risk :
    0 < missingPKCERisk false true := by
  simp [missingPKCERisk]

theorem oauth_confidential_client_no_pkce_safe :
    missingPKCERisk false false = 0 := by
  simp [missingPKCERisk]

-- Open redirect in callback URI: attacker registers redirect_uri prefix
def openRedirectRisk (redirectUriValidated : Bool) (exactMatch : Bool) : Nat :=
  if redirectUriValidated && exactMatch then 0 else 1

theorem oauth_exact_match_redirect_safe :
    openRedirectRisk true true = 0 := by
  simp [openRedirectRisk]

theorem oauth_prefix_match_redirect_risk :
    0 < openRedirectRisk true false := by
  simp [openRedirectRisk]

theorem oauth_no_validation_redirect_risk :
    0 < openRedirectRisk false false := by
  simp [openRedirectRisk]

-- Missing state parameter: CSRF forces user to authorise attacker's session
def missingStateRisk (stateParamUsed : Bool) : Nat :=
  if stateParamUsed then 0 else 1

theorem oauth_state_param_safe :
    missingStateRisk true = 0 := by
  simp [missingStateRisk]

theorem oauth_no_state_csrf_risk :
    0 < missingStateRisk false := by
  simp [missingStateRisk]

-- Token leakage via Referer header: token in URL sent in Referer to third parties
def tokenRefererLeakRisk (tokenInURL : Bool) (referrerPolicy : Bool) : Nat :=
  if !tokenInURL || referrerPolicy then 0 else 1

theorem oauth_token_not_in_url_safe (rp : Bool) :
    tokenRefererLeakRisk false rp = 0 := by
  simp [tokenRefererLeakRisk]

theorem oauth_token_in_url_no_policy_risk :
    0 < tokenRefererLeakRisk true false := by
  simp [tokenRefererLeakRisk]

-- Token scope: over-privileged scope amplifies breach impact
def scopeOverprovisioningRisk (requestedScopes : Nat) (minRequired : Nat) : Nat :=
  if requestedScopes ≤ minRequired then 0 else requestedScopes - minRequired

theorem oauth_minimal_scope_safe (s m : Nat) (h : s ≤ m) :
    scopeOverprovisioningRisk s m = 0 := by
  simp [scopeOverprovisioningRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem oauth_excess_scope_risk (s m : Nat) (h : m < s) :
    0 < scopeOverprovisioningRisk s m := by { simp [scopeOverprovisioningRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires auth-code + PKCE + state + no open-redirect + minimal scope
def netOAuthRisk (usesImplicit : Bool) (usesPKCE : Bool) (stateUsed : Bool)
    (exactRedirect : Bool) (scopes : Nat) (minScopes : Nat) : Nat :=
  implicitFlowRisk usesImplicit +
  missingPKCERisk usesPKCE true +
  missingStateRisk stateUsed +
  openRedirectRisk true exactRedirect +
  scopeOverprovisioningRisk scopes minScopes

theorem oauth_net_risk_zero_fully_mitigated (m : Nat) :
    netOAuthRisk false true true true m m = 0 := by { simp [netOAuthRisk, implicitFlowRisk, missingPKCERisk, missingStateRisk,
        openRedirectRisk, scopeOverprovisioningRisk]

theorem oauth_net_risk_pos_unmitigated :
    0 < netOAuthRisk true false false false 10 2 := by
  simp [netOAuthRisk, implicitFlowRisk, missingPKCERisk, missingStateRisk,
        openRedirectRisk, scopeOverprovisioningRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end OAuthMisconfigRisk
