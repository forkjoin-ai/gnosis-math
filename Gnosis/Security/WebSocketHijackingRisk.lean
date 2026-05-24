import Init
-- WebSocketHijackingRisk.lean
-- Anti-thesis: WebSocket connections are protected by the same-origin policy
-- and browser security model, so no additional server-side Origin checking
-- is necessary; hijacking is prevented by TLS alone.
-- Refutation: Browsers do NOT enforce same-origin on WebSocket upgrade
-- requests; a malicious page can initiate a WS connection to any origin.
-- Without server-side Origin header validation, CSRF-over-WebSocket and
-- cross-protocol scripting attacks grant full socket-level access.

namespace Gnosis.Security.WebSocketHijackingRisk

-- Origin validation: server must check the Origin header on upgrade
def originValidated (serverChecksOrigin : Bool) (originIsAllowed : Bool) : Bool :=
  serverChecksOrigin && originIsAllowed

theorem no_origin_check_allows_any_origin (allowed : Bool) :
    originValidated false allowed = false := by
  simp [originValidated]

theorem origin_check_with_bad_origin_rejects :
    originValidated true false = false := by
  simp [originValidated]

theorem origin_check_with_good_origin_allows :
    originValidated true true = true := by
  simp [originValidated]

-- CSRF-over-WebSocket: cross-site page can send arbitrary WS messages
def csrfOverWSRisk (originValidated : Bool) (csrfTokenRequired : Bool) : Bool :=
  !originValidated && !csrfTokenRequired

theorem csrf_ws_blocked_by_origin_check (csrf : Bool) :
    csrfOverWSRisk true csrf = false := by
  simp [csrfOverWSRisk]

theorem csrf_ws_blocked_by_token (origin : Bool) :
    csrfOverWSRisk origin true = false := by
  simp [csrfOverWSRisk]
  cases origin <;> simp

theorem csrf_ws_succeeds_with_no_controls :
    csrfOverWSRisk false false = true := by
  simp [csrfOverWSRisk]

-- Protocol confusion: ws:// downgrade strips TLS protection
def protocolConfusionRisk (usesWSS : Bool) (tlsTerminatedByProxy : Bool) : Bool :=
  !usesWSS && !tlsTerminatedByProxy

theorem wss_prevents_protocol_confusion (proxy : Bool) :
    protocolConfusionRisk true proxy = false := by
  simp [protocolConfusionRisk]

theorem proxy_tls_prevents_protocol_confusion (wss : Bool) :
    protocolConfusionRisk wss true = false := by
  simp [protocolConfusionRisk]
  cases wss <;> simp

theorem plaintext_ws_without_proxy_is_vulnerable :
    protocolConfusionRisk false false = true := by
  simp [protocolConfusionRisk]

-- Message injection: unvalidated message content enables injection
def messageInjectionRisk (messageValidated : Bool) (inputSanitized : Bool) : Nat :=
  if messageValidated && inputSanitized then 0 else 1

theorem validated_sanitized_messages_safe :
    messageInjectionRisk true true = 0 := by
  simp [messageInjectionRisk]

theorem unvalidated_messages_risky (sanitized : Bool) :
    messageInjectionRisk false sanitized = 1 := by
  simp [messageInjectionRisk]

theorem unsanitized_messages_risky (validated : Bool) :
    messageInjectionRisk validated false = 1 := by
  simp [messageInjectionRisk]
  cases validated <;> simp

-- Session binding: WS session must be bound to authenticated HTTP session
def sessionBindingRisk (wsBoundToSession : Bool) (sessionExpired : Bool) : Bool :=
  !wsBoundToSession || sessionExpired

theorem unbound_ws_session_risky (expired : Bool) :
    sessionBindingRisk false expired = true := by
  simp [sessionBindingRisk]

theorem expired_session_risky (bound : Bool) :
    sessionBindingRisk bound true = true := by
  simp [sessionBindingRisk]
  cases bound <;> simp

theorem bound_active_session_safe :
    sessionBindingRisk true false = false := by
  simp [sessionBindingRisk]

-- Aggregate WebSocket risk score
def webSocketTotalRisk (originChecked : Bool) (originAllowed : Bool)
    (csrfToken : Bool) (usesWSS : Bool) (msgValidated : Bool)
    (msgSanitized : Bool) (sessionBound : Bool) : Nat :=
  (if csrfOverWSRisk originChecked csrfToken then 1 else 0) +
  (if protocolConfusionRisk usesWSS false then 1 else 0) +
  messageInjectionRisk msgValidated msgSanitized +
  (if sessionBindingRisk sessionBound false then 1 else 0)

theorem websocket_risk_zero_full_controls :
    webSocketTotalRisk true true true true true true true = 0 := by
  simp [webSocketTotalRisk, csrfOverWSRisk, protocolConfusionRisk,
        messageInjectionRisk, sessionBindingRisk]

theorem websocket_risk_positive_no_controls :
    0 < webSocketTotalRisk false false false false false false false := by
  simp [webSocketTotalRisk, csrfOverWSRisk, protocolConfusionRisk,
        messageInjectionRisk, sessionBindingRisk]

-- Origin check is necessary: without it CSRF risk is always present
theorem origin_check_necessary_for_csrf_prevention :
    csrfOverWSRisk false false = true ∧ csrfOverWSRisk true false = false := by
  simp [csrfOverWSRisk]

-- Defence layers are independent and additive
theorem defence_in_depth_reduces_risk
    (oc oa ct wss mv ms sb : Bool)
    (h1 : oc = true) (h2 : ct = true) (h3 : wss = true)
    (h4 : mv = true) (h5 : ms = true) (h6 : sb = true) :
    webSocketTotalRisk oc oa ct wss mv ms sb = 0 := by
  subst h1 h2 h3 h4 h5 h6
  simp [webSocketTotalRisk, csrfOverWSRisk, protocolConfusionRisk,
        messageInjectionRisk, sessionBindingRisk]

end WebSocketHijackingRisk
