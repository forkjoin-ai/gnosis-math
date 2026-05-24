import Init
-- EventDrivenInjectionRisk.lean
-- Anti-thesis: Event-driven architectures improve security posture by decoupling
-- producers and consumers; because message queues act as a buffer, the consumer
-- never directly receives user input, and event payloads are structured data
-- (JSON/Avro) that parsers handle safely without injection concerns.
-- Refutation: Message payloads often contain user-controlled strings that are
-- later rendered by template engines or interpolated into database queries in
-- downstream consumers — a classic second-order injection pattern. Deserialization
-- of event payloads without schema validation allows gadget-chain exploitation
-- when Java/Python/Ruby pickle consumers process attacker-controlled messages.
-- Schema registry misconfigurations allow producers to register malicious
-- schemas. Event sourcing replays can re-execute injection payloads stored in
-- the event log. Missing dead-letter-queue monitoring allows silent injection
-- attempts to accumulate.

namespace Gnosis.Security.EventDrivenInjectionRisk

-- Second-order injection: user-controlled payload stored in queue, injected downstream
def secondOrderInjectionRisk (payloadContainsUserInput : Bool)
    (downstreamConsumerSanitizes : Bool) : Bool :=
  payloadContainsUserInput && !downstreamConsumerSanitizes

theorem downstream_sanitizes_safe (userInput : Bool) :
    secondOrderInjectionRisk userInput true = false := by { simp [secondOrderInjectionRisk]

theorem payload_no_user_input_safe (sanitizes : Bool) :
    secondOrderInjectionRisk false sanitizes = false := by
  simp [secondOrderInjectionRisk]

theorem user_input_payload_unsanitized_downstream_risky :
    secondOrderInjectionRisk true false = true := by
  simp [secondOrderInjectionRisk]

-- Deserialization without schema validation: gadget-chain exploitation
def eventDeserializationRisk (deserializesWithoutSchema : Bool)
    (payloadFromUntrustedSource : Bool) : Bool :=
  deserializesWithoutSchema && payloadFromUntrustedSource

theorem schema_validation_prevents_deserialization_exploit (untrusted : Bool) :
    eventDeserializationRisk false untrusted = false := by
  simp [eventDeserializationRisk]

theorem trusted_source_payload_safe (schemaless : Bool) :
    eventDeserializationRisk schemaless false = false := by
  simp [eventDeserializationRisk]

theorem schemaless_untrusted_payload_risky :
    eventDeserializationRisk true true = true := by
  simp [eventDeserializationRisk]

-- Schema registry misconfig: attacker registers malicious schema
def schemaRegistryRisk (schemaRegistryAccessPublic : Bool)
    (schemaRegistryAuthRequired : Bool) : Bool :=
  schemaRegistryAccessPublic && !schemaRegistryAuthRequired

theorem schema_registry_auth_required_safe (publicAccess : Bool) :
    schemaRegistryRisk publicAccess true = false := by
  simp [schemaRegistryRisk]

theorem schema_registry_not_public_safe (authRequired : Bool) :
    schemaRegistryRisk false authRequired = false := by
  simp [schemaRegistryRisk]

theorem public_registry_no_auth_risky :
    schemaRegistryRisk true false = true := by
  simp [schemaRegistryRisk]

-- Event replay injection: replaying event log re-executes historical injection
def eventReplayInjectionRisk (eventReplayEnabled : Bool)
    (replayedEventsRevalidated : Bool) : Bool :=
  eventReplayEnabled && !replayedEventsRevalidated

theorem replayed_events_revalidated_safe (replayEnabled : Bool) :
    eventReplayInjectionRisk replayEnabled true = false := by
  simp [eventReplayInjectionRisk]

theorem event_replay_disabled_safe (revalidated : Bool) :
    eventReplayInjectionRisk false revalidated = false := by
  simp [eventReplayInjectionRisk]

theorem replay_enabled_not_revalidated_risky :
    eventReplayInjectionRisk true false = true := by
  simp [eventReplayInjectionRisk]

-- Dead letter queue: failed injection attempts accumulate unmonitored
def deadLetterQueueRisk (dlqMonitored : Bool) (injectionAttemptInDLQ : Bool) : Bool :=
  !dlqMonitored && injectionAttemptInDLQ

theorem dlq_monitored_safe (injectionInDLQ : Bool) :
    deadLetterQueueRisk true injectionInDLQ = false := by
  simp [deadLetterQueueRisk]

theorem no_injection_in_dlq_safe (monitored : Bool) :
    deadLetterQueueRisk monitored false = false := by
  simp [deadLetterQueueRisk]

theorem unmonitored_dlq_with_injection_attempts_risky :
    deadLetterQueueRisk false true = true := by
  simp [deadLetterQueueRisk]

-- Aggregate event-driven injection risk count
def aggregateEventDrivenInjectionRisk
    (payloadUserInput downstreamSanitizes : Bool)
    (schemaless untrustedSource : Bool)
    (registryPublic registryAuth : Bool)
    (replayEnabled replayRevalidated : Bool)
    (dlqMonitored injectionInDLQ : Bool) : Nat :=
  (if secondOrderInjectionRisk payloadUserInput downstreamSanitizes then 1 else 0) +
  (if eventDeserializationRisk schemaless untrustedSource then 1 else 0) +
  (if schemaRegistryRisk registryPublic registryAuth then 1 else 0) +
  (if eventReplayInjectionRisk replayEnabled replayRevalidated then 1 else 0) +
  (if deadLetterQueueRisk dlqMonitored injectionInDLQ then 1 else 0)

theorem fully_hardened_zero_event_injection_risk :
    aggregateEventDrivenInjectionRisk
      false true
      false false
      false true
      false true
      true false = 0 := by
  simp [aggregateEventDrivenInjectionRisk, secondOrderInjectionRisk, eventDeserializationRisk,
        schemaRegistryRisk, eventReplayInjectionRisk, deadLetterQueueRisk]

theorem all_event_injection_vectors_max_risk :
    aggregateEventDrivenInjectionRisk
      true false
      true true
      true false
      true false
      false true = 5 := by
  simp [aggregateEventDrivenInjectionRisk, secondOrderInjectionRisk, eventDeserializationRisk,
        schemaRegistryRisk, eventReplayInjectionRisk, deadLetterQueueRisk]

theorem event_injection_risk_bounded
    (payloadUserInput downstreamSanitizes : Bool)
    (schemaless untrustedSource : Bool)
    (registryPublic registryAuth : Bool)
    (replayEnabled replayRevalidated : Bool)
    (dlqMonitored injectionInDLQ : Bool) :
    aggregateEventDrivenInjectionRisk
      payloadUserInput downstreamSanitizes
      schemaless untrustedSource
      registryPublic registryAuth
      replayEnabled replayRevalidated
      dlqMonitored injectionInDLQ ≤ 5 := by
  simp [aggregateEventDrivenInjectionRisk]
  split <;> split <;> split <;> split <;> split <;> decide

-- Scanner ROI: event-driven injection detection prevents second-order breach cost
def eventInjectionDetectionValueCents (secondOrderBreachCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (secondOrderBreachCostCents : Int) - (scannerCostCents : Int)

theorem event_injection_scanner_profitable (breach scan : Nat) (h : scan < breach) :
    0 < eventInjectionDetectionValueCents breach scan := by
  simp [eventInjectionDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem event_injection_scanner_break_even (cost : Nat) :
    0 ≤ eventInjectionDetectionValueCents cost cost := by
  simp [eventInjectionDetectionValueCents]

-- Fleet ROI: event-driven injection scan across all message-queue consumers
def eventInjectionFleetROI (detectionValueCents : Nat) (queueConsumers : Nat) : Nat :=
  detectionValueCents * queueConsumers

theorem event_injection_fleet_roi_monotone (v c1 c2 : Nat) (h : c1 ≤ c2) :
    eventInjectionFleetROI v c1 ≤ eventInjectionFleetROI v c2 := by
  simp [eventInjectionFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_event_injection_fleet_roi (v c : Nat) (hv : 0 < v) (hc : 0 < c) :
    0 < eventInjectionFleetROI v c := by
  simp [eventInjectionFleetROI]
  exact Nat.mul_pos hv hc

end EventDrivenInjectionRisk
