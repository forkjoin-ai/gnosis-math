import Init
-- NoSQLInjectionRisk.lean
-- Anti-thesis: NoSQL databases like MongoDB don't use SQL, so SQL injection
-- is impossible; query structures are document-based and parameterized by
-- default in modern drivers, making injection a non-issue for applications
-- that have migrated away from relational databases.
-- Refutation: MongoDB's query operators ($where, $gt, $ne, $regex) accept
-- JavaScript or complex expressions when user input is merged directly into
-- query objects. The $where clause executes arbitrary JavaScript server-side.
-- CouchDB Mango queries and Redis EVAL accept scripts that can be manipulated
-- with unsanitized input. NoSQL injection can bypass authentication (e.g.,
-- {"username": {"$ne": ""}, "password": {"$ne": ""}}) and exfiltrate entire
-- collections. These vectors are distinct from SQL injection and require
-- NoSQL-specific detection rules.

namespace Gnosis.Security.NoSQLInjectionRisk

-- MongoDB operator injection: user input merged directly into query object
def mongoOperatorInjectionRisk (queryObjectSanitized : Bool)
    (operatorKeysFiltered : Bool) (inputIsString : Bool) : Bool :=
  !queryObjectSanitized && (!operatorKeysFiltered || !inputIsString)

theorem sanitized_query_safe (filtered string : Bool) :
    mongoOperatorInjectionRisk true filtered string = false := by { simp [mongoOperatorInjectionRisk]

theorem filtered_operators_and_string_input_safe :
    mongoOperatorInjectionRisk false true true = false := by
  simp [mongoOperatorInjectionRisk]

theorem unsanitized_unfiltered_risky (string : Bool) :
    mongoOperatorInjectionRisk false false string = true := by
  simp [mongoOperatorInjectionRisk]

theorem unsanitized_non_string_risky (filtered : Bool) :
    mongoOperatorInjectionRisk false filtered false = true := by
  simp [mongoOperatorInjectionRisk]

-- $where JavaScript injection: arbitrary JS execution in MongoDB query context
def mongoWhereJSRisk (whereClauseDisabled : Bool) (jsEngineEnabled : Bool) : Bool :=
  !whereClauseDisabled && jsEngineEnabled

theorem where_clause_disabled_safe (jsEnabled : Bool) :
    mongoWhereJSRisk true jsEnabled = false := by
  simp [mongoWhereJSRisk]

theorem js_engine_disabled_safe (whereEnabled : Bool) :
    mongoWhereJSRisk whereEnabled false = false := by
  simp [mongoWhereJSRisk]

theorem enabled_where_js_engine_risky :
    mongoWhereJSRisk false true = true := by
  simp [mongoWhereJSRisk]

-- Authentication bypass: {"$ne": ""} pattern bypasses username/password checks
def mongoAuthBypassRisk (operatorInjectionPossible : Bool)
    (authQueryParameterized : Bool) : Bool :=
  operatorInjectionPossible && !authQueryParameterized

theorem parameterized_auth_query_safe (injection : Bool) :
    mongoAuthBypassRisk injection true = false := by
  simp [mongoAuthBypassRisk]

theorem no_injection_possible_safe (parameterized : Bool) :
    mongoAuthBypassRisk false parameterized = false := by
  simp [mongoAuthBypassRisk]

theorem injection_with_unparam_auth_risky :
    mongoAuthBypassRisk true false = true := by
  simp [mongoAuthBypassRisk]

-- CouchDB Mango injection: selector operators with unvalidated input
def couchDBMangoInjectionRisk (selectorSanitized : Bool) (selectorTypeChecked : Bool) : Bool :=
  !selectorSanitized || !selectorTypeChecked

theorem sanitized_and_type_checked_safe :
    couchDBMangoInjectionRisk true true = false := by
  simp [couchDBMangoInjectionRisk]

theorem unsanitized_risky (typed : Bool) :
    couchDBMangoInjectionRisk false typed = true := by
  simp [couchDBMangoInjectionRisk]

theorem untyped_risky (sanitized : Bool) :
    couchDBMangoInjectionRisk sanitized false = true := by
  simp [couchDBMangoInjectionRisk]

-- Redis EVAL injection: Lua script constructed from user input
def redisEvalInjectionRisk (evalDisabled : Bool) (luaScriptParameterized : Bool)
    (userInputInScript : Bool) : Bool :=
  !evalDisabled && (!luaScriptParameterized && userInputInScript)

theorem eval_disabled_safe (param input : Bool) :
    redisEvalInjectionRisk true param input = false := by
  simp [redisEvalInjectionRisk]

theorem parameterized_script_safe (evalOk input : Bool) :
    redisEvalInjectionRisk evalOk true input = false := by
  simp [redisEvalInjectionRisk]

theorem eval_enabled_unparam_with_input_risky :
    redisEvalInjectionRisk false false true = true := by
  simp [redisEvalInjectionRisk]

theorem eval_enabled_no_user_input_safe (param : Bool) :
    redisEvalInjectionRisk false param false = false := by
  simp [redisEvalInjectionRisk]

-- $regex injection: unbounded regex from user input causes ReDoS
def mongoRegexInjectionRisk (regexFromUserInput : Bool) (regexComplexityLimited : Bool)
    (inputSanitized : Bool) : Bool :=
  regexFromUserInput && !regexComplexityLimited && !inputSanitized

theorem complexity_limited_safe (user sanitized : Bool) :
    mongoRegexInjectionRisk user true sanitized = false := by
  simp [mongoRegexInjectionRisk]

theorem input_sanitized_safe (user limited : Bool) :
    mongoRegexInjectionRisk user limited true = false := by
  simp [mongoRegexInjectionRisk]

theorem no_user_input_regex_safe (limited sanitized : Bool) :
    mongoRegexInjectionRisk false limited sanitized = false := by
  simp [mongoRegexInjectionRisk]

theorem user_input_regex_no_limits_risky :
    mongoRegexInjectionRisk true false false = true := by
  simp [mongoRegexInjectionRisk]

-- Aggregate NoSQL injection risk
def aggregateNoSQLInjectionRisk
    (sanitized filtered isString : Bool)
    (whereDisabled jsEnabled : Bool)
    (operatorOk paramAuth : Bool)
    (evalDisabled luaParam userInput : Bool) : Nat :=
  (if mongoOperatorInjectionRisk sanitized filtered isString then 1 else 0) +
  (if mongoWhereJSRisk whereDisabled jsEnabled then 1 else 0) +
  (if mongoAuthBypassRisk operatorOk paramAuth then 1 else 0) +
  (if redisEvalInjectionRisk evalDisabled luaParam userInput then 1 else 0)

theorem fully_hardened_zero_nosql_risk :
    aggregateNoSQLInjectionRisk true true true true false false true true false = 0 := by
  simp [aggregateNoSQLInjectionRisk, mongoOperatorInjectionRisk, mongoWhereJSRisk,
        mongoAuthBypassRisk, redisEvalInjectionRisk]

theorem all_nosql_vectors_max_risk :
    aggregateNoSQLInjectionRisk false false false false true true false false true = 4 := by
  simp [aggregateNoSQLInjectionRisk, mongoOperatorInjectionRisk, mongoWhereJSRisk,
        mongoAuthBypassRisk, redisEvalInjectionRisk]

-- Economic: NoSQL injection scanner detection value
def noSQLInjectionDetectionValueCents (dataBreachCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (dataBreachCostCents : Int) - (scannerCostCents : Int)

theorem nosql_detection_profitable (breach scan : Nat) (h : scan < breach) :
    0 < noSQLInjectionDetectionValueCents breach scan := by
  simp [noSQLInjectionDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem nosql_break_even (cost : Nat) :
    0 ≤ noSQLInjectionDetectionValueCents cost cost := by
  simp [noSQLInjectionDetectionValueCents]

-- Fleet ROI: NoSQL injection scan across MongoDB/Redis/CouchDB services
def noSQLFleetROI (detectionValue : Nat) (noSQLServices : Nat) : Nat :=
  detectionValue * noSQLServices

theorem nosql_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    noSQLFleetROI v s1 ≤ noSQLFleetROI v s2 := by
  simp [noSQLFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_nosql_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < noSQLFleetROI v s := by
  simp [noSQLFleetROI]
  exact Nat.mul_pos hv hs

end NoSQLInjectionRisk
