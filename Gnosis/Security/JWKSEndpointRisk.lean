import Init
-- JWKSEndpointRisk.lean
-- Anti-thesis: JWKS (JSON Web Key Set) endpoints are a standard OAuth 2.0 /
-- OpenID Connect mechanism for key distribution; because they are public and
-- read-only, they introduce no security risk beyond publishing the public keys
-- that are already used to verify tokens.
-- Refutation: An unrestricted `jku` or `x5u` JWT header parameter allows an
-- attacker to point the verifier at an attacker-controlled JWKS URL, replacing
-- the trusted key set. Algorithm confusion between RS256 and HS256 allows the
-- attacker to sign tokens with the public key as an HMAC secret. Caching a
-- JWKS response without integrity checking allows poisoning via a MITM between
-- the verifier and the JWKS endpoint. Key rotation gaps (old key still valid
-- after rotation) allow replay of tokens signed with a compromised key.

namespace Gnosis.Security.JWKSEndpointRisk

-- Unrestricted JWK URL: jku/x5u not validated against allowlist
def jwkURLInjectionRisk (jkuHeaderAccepted : Bool) (jkuValidatedAgainstAllowlist : Bool) : Bool :=
  jkuHeaderAccepted && !jkuValidatedAgainstAllowlist

theorem jku_not_accepted_safe (validated : Bool) :
    jwkURLInjectionRisk false validated = false := by { simp [jwkURLInjectionRisk]

theorem jku_allowlist_validated_safe (accepted : Bool) :
    jwkURLInjectionRisk accepted true = false := by
  simp [jwkURLInjectionRisk]

theorem unvalidated_jku_accepted_risky :
    jwkURLInjectionRisk true false = true := by
  simp [jwkURLInjectionRisk]

-- Algorithm confusion: RS256 public key used as HS256 HMAC secret
def algConfusionRisk (algFromHeader : Bool) (serverEnforcesExpectedAlg : Bool) : Bool :=
  algFromHeader && !serverEnforcesExpectedAlg

theorem server_enforces_alg_safe (algFromHeader : Bool) :
    algConfusionRisk algFromHeader true = false := by
  simp [algConfusionRisk]

theorem alg_not_from_header_safe (enforces : Bool) :
    algConfusionRisk false enforces = false := by
  simp [algConfusionRisk]

theorem alg_from_header_unenforced_risky :
    algConfusionRisk true false = true := by
  simp [algConfusionRisk]

-- JWKS cache poisoning: cached response accepted without integrity check
def jwksCachePoisoningRisk (jwksCached : Bool) (integrityCheckOnCache : Bool)
    (mitmPossible : Bool) : Bool :=
  jwksCached && !integrityCheckOnCache && mitmPossible

theorem integrity_check_prevents_cache_poison (cached mitmPossible : Bool) :
    jwksCachePoisoningRisk cached true mitmPossible = false := by
  simp [jwksCachePoisoningRisk]

theorem jwks_not_cached_safe (integrityCheck mitmPossible : Bool) :
    jwksCachePoisoningRisk false integrityCheck mitmPossible = false := by
  simp [jwksCachePoisoningRisk]

theorem no_mitm_path_safe (cached integrityCheck : Bool) :
    jwksCachePoisoningRisk cached integrityCheck false = false := by
  simp [jwksCachePoisoningRisk]

theorem cached_no_integrity_with_mitm_risky :
    jwksCachePoisoningRisk true false true = true := by
  simp [jwksCachePoisoningRisk]

-- Key rotation gap: old key still accepted after rotation, enabling replay
def keyRotationGapRisk (oldKeyStillAccepted : Bool) (oldKeyCompromised : Bool)
    (gracePeriodExpired : Bool) : Bool :=
  oldKeyStillAccepted && oldKeyCompromised && gracePeriodExpired

theorem old_key_revoked_safe (compromised gracePeriod : Bool) :
    keyRotationGapRisk false compromised gracePeriod = false := by
  simp [keyRotationGapRisk]

theorem old_key_not_compromised_safe (accepted gracePeriod : Bool) :
    keyRotationGapRisk accepted false gracePeriod = false := by
  simp [keyRotationGapRisk]

theorem grace_period_still_active_safe (accepted compromised : Bool) :
    keyRotationGapRisk accepted compromised false = false := by
  simp [keyRotationGapRisk]

theorem expired_grace_period_compromised_key_risky :
    keyRotationGapRisk true true true = true := by
  simp [keyRotationGapRisk]

-- Key ID (kid) injection: unsanitised kid used in database or OS command
def kidInjectionRisk (kidFromToken : Bool) (kidSanitized : Bool)
    (kidUsedInDBQuery : Bool) : Bool :=
  kidFromToken && !kidSanitized && kidUsedInDBQuery

theorem kid_sanitized_safe (fromToken inDB : Bool) :
    kidInjectionRisk fromToken true inDB = false := by
  simp [kidInjectionRisk]

theorem kid_not_from_token_safe (sanitized inDB : Bool) :
    kidInjectionRisk false sanitized inDB = false := by
  simp [kidInjectionRisk]

theorem kid_not_used_in_query_safe (fromToken sanitized : Bool) :
    kidInjectionRisk fromToken sanitized false = false := by
  simp [kidInjectionRisk]

theorem unsanitized_kid_in_db_query_risky :
    kidInjectionRisk true false true = true := by
  simp [kidInjectionRisk]

-- Aggregate JWKS risk count
def aggregateJWKSRisk
    (jkuAccepted jkuValidated : Bool)
    (algFromHeader algEnforced : Bool)
    (jwksCached integrityCheck mitmPossible : Bool)
    (oldKeyAccepted oldKeyCompromised gracePeriodExpired : Bool)
    (kidFromToken kidSanitized kidInDB : Bool) : Nat :=
  (if jwkURLInjectionRisk jkuAccepted jkuValidated then 1 else 0) +
  (if algConfusionRisk algFromHeader algEnforced then 1 else 0) +
  (if jwksCachePoisoningRisk jwksCached integrityCheck mitmPossible then 1 else 0) +
  (if keyRotationGapRisk oldKeyAccepted oldKeyCompromised gracePeriodExpired then 1 else 0) +
  (if kidInjectionRisk kidFromToken kidSanitized kidInDB then 1 else 0)

theorem fully_hardened_zero_jwks_risk :
    aggregateJWKSRisk
      false true
      false true
      false true false
      false false false
      false true false = 0 := by
  simp [aggregateJWKSRisk, jwkURLInjectionRisk, algConfusionRisk,
        jwksCachePoisoningRisk, keyRotationGapRisk, kidInjectionRisk]

theorem all_jwks_vectors_max_risk :
    aggregateJWKSRisk
      true false
      true false
      true false true
      true true true
      true false true = 5 := by
  simp [aggregateJWKSRisk, jwkURLInjectionRisk, algConfusionRisk,
        jwksCachePoisoningRisk, keyRotationGapRisk, kidInjectionRisk]

theorem jwks_risk_bounded
    (jkuAccepted jkuValidated : Bool)
    (algFromHeader algEnforced : Bool)
    (jwksCached integrityCheck mitmPossible : Bool)
    (oldKeyAccepted oldKeyCompromised gracePeriodExpired : Bool)
    (kidFromToken kidSanitized kidInDB : Bool) :
    aggregateJWKSRisk
      jkuAccepted jkuValidated algFromHeader algEnforced
      jwksCached integrityCheck mitmPossible
      oldKeyAccepted oldKeyCompromised gracePeriodExpired
      kidFromToken kidSanitized kidInDB ≤ 5 := by
  simp [aggregateJWKSRisk]
  split <;> split <;> split <;> split <;> split <;> decide

-- Scanner ROI: JWKS misconfiguration detection prevents token forgery breach
def jwksDetectionValueCents (tokenForgeryBreachCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (tokenForgeryBreachCostCents : Int) - (scannerCostCents : Int)

theorem jwks_scanner_profitable (breach scan : Nat) (h : scan < breach) :
    0 < jwksDetectionValueCents breach scan := by
  simp [jwksDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem jwks_scanner_break_even (cost : Nat) :
    0 ≤ jwksDetectionValueCents cost cost := by
  simp [jwksDetectionValueCents]

-- Fleet ROI: JWKS scan across all OAuth/OIDC deployments
def jwksFleetROI (detectionValueCents : Nat) (oauthDeployments : Nat) : Nat :=
  detectionValueCents * oauthDeployments

theorem jwks_fleet_roi_monotone (v d1 d2 : Nat) (h : d1 ≤ d2) :
    jwksFleetROI v d1 ≤ jwksFleetROI v d2 := by
  simp [jwksFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_jwks_fleet_roi (v d : Nat) (hv : 0 < v) (hd : 0 < d) :
    0 < jwksFleetROI v d := by
  simp [jwksFleetROI]
  exact Nat.mul_pos hv hd

end JWKSEndpointRisk
