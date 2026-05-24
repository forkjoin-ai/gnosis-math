import Init
-- XSSStoredRisk.lean
-- Anti-thesis: XSS only steals cookies when HttpOnly is not set; modern browsers
-- sandbox JavaScript execution so XSS has limited real-world impact on well-
-- configured applications with Content Security Policy headers.
-- Refutation: Stored XSS executes as the victim: it can exfiltrate tokens from
-- localStorage, forge API requests under the victim's session, keylog form inputs,
-- and redirect to phishing pages. CSP is frequently bypassed via JSONP endpoints,
-- CDN whitelisting, or is_unsafe-inline. DOM-based XSS bypasses server-side sanitizers.

namespace Gnosis.Security.XSSStoredRisk

-- Stored XSS: unsanitized input or unencoded output allows injection
def storedXSSRisk (inputSanitized : Bool) (outputEncoded : Bool) : Bool :=
  !inputSanitized || !outputEncoded

theorem sanitized_and_encoded_no_stored_xss :
    storedXSSRisk true true = false := by
  simp [storedXSSRisk]

theorem unsanitized_input_stored_xss_risk (enc : Bool) :
    storedXSSRisk false enc = true := by
  simp [storedXSSRisk]

theorem unencoded_output_stored_xss_risk (san : Bool) :
    storedXSSRisk san false = true := by
  simp [storedXSSRisk]
  cases san <;> simp

-- Reflected XSS: URL parameter reflected without encoding and no CSP
def reflectedXSSRisk (urlParamEncoded : Bool) (cspEnforced : Bool) : Bool :=
  !urlParamEncoded && !cspEnforced

theorem encoded_url_no_reflected_xss (csp : Bool) :
    reflectedXSSRisk true csp = false := by
  simp [reflectedXSSRisk]

theorem csp_blocks_reflected_xss (enc : Bool) :
    reflectedXSSRisk enc true = false := by
  simp [reflectedXSSRisk]
  cases enc <;> simp

theorem no_encoding_no_csp_reflected_risky :
    reflectedXSSRisk false false = true := by
  simp [reflectedXSSRisk]

-- DOM-based XSS: dangerous sink used with untrusted input
def domXSSRisk (dangerousSinkPresent : Bool) (inputUntrusted : Bool) : Bool :=
  dangerousSinkPresent && inputUntrusted

theorem no_dangerous_sink_no_dom_xss (untrusted : Bool) :
    domXSSRisk false untrusted = false := by
  simp [domXSSRisk]

theorem trusted_input_no_dom_xss (sink : Bool) :
    domXSSRisk sink false = false := by
  simp [domXSSRisk]
  cases sink <;> simp

theorem dangerous_sink_with_untrusted_input_risky :
    domXSSRisk true true = true := by
  simp [domXSSRisk]

-- CSP bypass: weak or absent CSP fails to mitigate XSS
def cspBypassRisk (cspPresent : Bool) (unsafeInlineAllowed : Bool)
    (jsonpEndpointWhitelisted : Bool) : Bool :=
  !cspPresent || unsafeInlineAllowed || jsonpEndpointWhitelisted

theorem no_csp_bypassable (ui jw : Bool) :
    cspBypassRisk false ui jw = true := by
  simp [cspBypassRisk]

theorem strong_csp_no_bypass :
    cspBypassRisk true false false = false := by
  simp [cspBypassRisk]

theorem unsafe_inline_weakens_csp (jw : Bool) :
    cspBypassRisk true true jw = true := by
  simp [cspBypassRisk]

theorem jsonp_whitelist_weakens_csp (ui : Bool) :
    cspBypassRisk true ui true = true := by
  simp [cspBypassRisk]
  cases ui <;> simp

-- Mutation XSS: HTML parser normalises sanitized output into new XSS
def mutationXSSRisk (htmlParserUsed : Bool) (sanitizerDOMSafe : Bool) : Bool :=
  htmlParserUsed && !sanitizerDOMSafe

theorem no_html_parser_no_mutation_xss (safe : Bool) :
    mutationXSSRisk false safe = false := by
  simp [mutationXSSRisk]

theorem dom_safe_sanitizer_no_mutation_xss (parser : Bool) :
    mutationXSSRisk parser true = false := by
  simp [mutationXSSRisk]
  cases parser <;> simp

theorem html_parser_without_dom_safe_sanitizer_risky :
    mutationXSSRisk true false = true := by
  simp [mutationXSSRisk]

-- XSS impact: stored XSS scales with victim session count
def xssImpactCents (victimCount : Nat) (tokenValueCents : Nat) : Nat :=
  victimCount * tokenValueCents

theorem xss_impact_zero_victims (v : Nat) :
    xssImpactCents 0 v = 0 := by
  simp [xssImpactCents]

theorem xss_impact_scales_with_victims (v1 v2 t : Nat) (h : v1 ≤ v2) :
    xssImpactCents v1 t ≤ xssImpactCents v2 t := by
  simp [xssImpactCents]
  exact Nat.mul_le_mul_right t h

-- Aggregate XSS risk score
def xssTotalRisk (inputSanitized outputEncoded urlEncoded cspEnforced
    dangerousSink sanitizerDOMSafe : Bool) : Nat :=
  (if storedXSSRisk inputSanitized outputEncoded then 1 else 0) +
  (if reflectedXSSRisk urlEncoded cspEnforced then 1 else 0) +
  (if domXSSRisk dangerousSink (!sanitizerDOMSafe) then 1 else 0)

theorem xss_total_risk_zero_full_controls :
    xssTotalRisk true true true true false true = 0 := by
  simp [xssTotalRisk, storedXSSRisk, reflectedXSSRisk, domXSSRisk]

theorem xss_total_risk_positive_no_output_encoding :
    0 < xssTotalRisk true false true true false true := by
  simp [xssTotalRisk, storedXSSRisk, reflectedXSSRisk, domXSSRisk]

-- Defence: output encoding is strictly necessary
theorem output_encoding_necessary :
    storedXSSRisk true false = true ∧ storedXSSRisk true true = false := by
  simp [storedXSSRisk]

-- Defence: CSP reduces both reflected and DOM XSS surfaces
theorem csp_reduces_reflected_risk :
    reflectedXSSRisk false true = false ∧ reflectedXSSRisk false false = true := by
  simp [reflectedXSSRisk]

end XSSStoredRisk
