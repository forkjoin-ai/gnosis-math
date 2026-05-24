import Init
-- XMLSignatureWrappingRisk.lean
-- Anti-thesis: XML Signature validation per W3C XMLDSIG guarantees document integrity;
-- SAML SSO using XMLDSIG is provably secure against message tampering because the
-- signature covers the entire assertion.
-- Refutation: XML Signature Wrapping (XSW) exploits the gap between which element is
-- signed and which element the application processes. XPath injection in signature
-- references allows reference confusion. Duplicate XML ID attributes create ambiguous
-- signature scope. SAML assertions can be wrapped with attacker-controlled content
-- outside the signed scope, granting elevated privileges without invalidating the
-- signature — demonstrated against Shibboleth, OneLogin, and GitHub Enterprise SAML.

namespace Gnosis.Security.XMLSignatureWrappingRisk

-- XSW: signed element vs application-processed element mismatch
def xswRisk (signedElementVerified : Bool) (processedElementMatches : Bool) : Bool :=
  !signedElementVerified || !processedElementMatches

theorem both_verified_and_matched_safe :
    xswRisk true true = false := by
  simp [xswRisk]

theorem unverified_signed_element_risky (matches_ : Bool) :
    xswRisk false matches_ = true := by
  simp [xswRisk]

theorem mismatched_processed_element_risky (verified : Bool) :
    xswRisk verified false = true := by
  simp [xswRisk]
  cases verified <;> simp

-- XPath injection: attacker-controlled XPath reference in SignedInfo
def xpathInjectionRisk (xpathUserControlled : Bool) (xpathSanitized : Bool) : Bool :=
  xpathUserControlled && !xpathSanitized

theorem sanitized_xpath_safe (controlled : Bool) :
    xpathInjectionRisk controlled true = false := by
  simp [xpathInjectionRisk]
  cases controlled <;> simp

theorem user_controlled_unsanitized_xpath_risky :
    xpathInjectionRisk true false = true := by
  simp [xpathInjectionRisk]

theorem no_user_xpath_no_injection (san : Bool) :
    xpathInjectionRisk false san = false := by
  simp [xpathInjectionRisk]

-- Duplicate ID: ambiguous ID resolution allows reference confusion
def duplicateIDRisk (idUniquenessEnforced : Bool) (idResolutionDeterministic : Bool) : Bool :=
  !idUniquenessEnforced && !idResolutionDeterministic

theorem id_uniqueness_prevents_confusion (det : Bool) :
    duplicateIDRisk true det = false := by
  simp [duplicateIDRisk]

theorem deterministic_resolution_safe (unique : Bool) :
    duplicateIDRisk unique true = false := by
  simp [duplicateIDRisk]
  cases unique <;> simp

theorem non_unique_non_deterministic_id_risky :
    duplicateIDRisk false false = true := by
  simp [duplicateIDRisk]

-- SAML wrapping: assertion content wrapped outside signed scope
def samlWrappingRisk (assertionBoundChecked : Bool) (envelopeValidated : Bool) : Bool :=
  !assertionBoundChecked && !envelopeValidated

theorem assertion_bound_check_prevents_wrapping (env : Bool) :
    samlWrappingRisk true env = false := by
  simp [samlWrappingRisk]

theorem envelope_validation_prevents_wrapping (bound : Bool) :
    samlWrappingRisk bound true = false := by
  simp [samlWrappingRisk]
  cases bound <;> simp

theorem unchecked_unvalidated_saml_wrapping_risk :
    samlWrappingRisk false false = true := by
  simp [samlWrappingRisk]

-- Unsigned node count: nodes outside signature scope are attacker-controllable
def unsignedNodes (signedNodes : Nat) (totalNodes : Nat) : Nat :=
  if totalNodes ≤ signedNodes then 0 else totalNodes - signedNodes

theorem no_unsigned_when_fully_signed (n : Nat) :
    unsignedNodes n n = 0 := by
  simp [unsignedNodes]

theorem unsigned_nodes_positive_when_partial (sn tn : Nat) (h : sn < tn) :
    0 < unsignedNodes sn tn := by
  simp [unsignedNodes]
  split_ifs with h1
  · omega
  · omega

theorem more_signed_fewer_unsigned (sn1 sn2 tn : Nat) (h : sn1 ≤ sn2) :
    unsignedNodes sn2 tn ≤ unsignedNodes sn1 tn := by
  simp [unsignedNodes]
  split_ifs with h1 h2
  · omega
  · omega
  · omega
  · omega

theorem zero_signed_all_unsigned (tn : Nat) :
    unsignedNodes 0 tn = tn := by
  simp [unsignedNodes]

-- Privilege escalation: unsigned claims grant elevated access
def wrappingPrivilegeRisk (unsignedClaimsProcessed : Bool) (privilegeFromClaims : Bool) : Bool :=
  unsignedClaimsProcessed && privilegeFromClaims

theorem no_unsigned_claims_no_privilege_escalation (priv : Bool) :
    wrappingPrivilegeRisk false priv = false := by
  simp [wrappingPrivilegeRisk]

theorem no_privilege_from_claims_safe (unsigned : Bool) :
    wrappingPrivilegeRisk unsigned false = false := by
  simp [wrappingPrivilegeRisk]
  cases unsigned <;> simp

theorem unsigned_claims_with_privilege_risky :
    wrappingPrivilegeRisk true true = true := by
  simp [wrappingPrivilegeRisk]

-- Aggregate XML signature wrapping risk
def xmlSignatureTotalRisk (sigVerified sigMatches xpathControlled xpathSan
    idUnique idDet assertionBound envValidated unsignedClaims privFromClaims : Bool) : Nat :=
  (if xswRisk sigVerified sigMatches then 1 else 0) +
  (if xpathInjectionRisk xpathControlled xpathSan then 1 else 0) +
  (if duplicateIDRisk idUnique idDet then 1 else 0) +
  (if samlWrappingRisk assertionBound envValidated then 1 else 0) +
  (if wrappingPrivilegeRisk unsignedClaims privFromClaims then 1 else 0)

theorem xml_sig_risk_zero_full_controls :
    xmlSignatureTotalRisk true true false true true true true true false false = 0 := by
  simp [xmlSignatureTotalRisk, xswRisk, xpathInjectionRisk,
        duplicateIDRisk, samlWrappingRisk, wrappingPrivilegeRisk]

theorem xml_sig_risk_positive_no_verification :
    0 < xmlSignatureTotalRisk false false false false false false false false false false := by
  simp [xmlSignatureTotalRisk, xswRisk, xpathInjectionRisk,
        duplicateIDRisk, samlWrappingRisk, wrappingPrivilegeRisk]

theorem xml_sig_risk_positive_mismatch_only :
    0 < xmlSignatureTotalRisk true false false true true true true true false false := by
  simp [xmlSignatureTotalRisk, xswRisk, xpathInjectionRisk,
        duplicateIDRisk, samlWrappingRisk, wrappingPrivilegeRisk]

-- Defence: XSW requires both signature verification and element binding checks
theorem xsw_requires_both_controls :
    xswRisk false false = true ∧ xswRisk true true = false := by
  simp [xswRisk]

-- Defence: SAML defence-in-depth — assertion bound check is independently sufficient
theorem saml_bound_check_sufficient (env : Bool) :
    samlWrappingRisk true env = false := by
  simp [samlWrappingRisk]

-- Defence: ID uniqueness alone prevents reference confusion
theorem id_uniqueness_sufficient (det : Bool) :
    duplicateIDRisk true det = false := by
  simp [duplicateIDRisk]

end XMLSignatureWrappingRisk
