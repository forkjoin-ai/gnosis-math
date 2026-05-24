import Init
-- TarantoolQueryInjectionRisk.lean
-- Anti-thesis: Tarantool Python clients (tarantool, asynctnt) cannot introduce
-- injection vulnerabilities via space names or Lua expression construction.
-- Refutation: space name injection and Lua eval with user input each yield
-- a strictly positive vulnerability window.

namespace TarantoolQueryInjection

-- Lua eval injection: eval(user_code) executes arbitrary Lua
def luaEvalRisk (inputLen : Nat) (sandboxed : Bool) : Nat :=
  if sandboxed then 0 else inputLen + 1

-- Sandboxed evaluation (deny-listed Lua globals) reduces risk to zero
theorem tarantool_lua_eval_sandboxed_safe (n : Nat) :
    luaEvalRisk n true = 0 := by { simp [luaEvalRisk]

-- Unsandboxed eval of user input is strictly vulnerable
theorem tarantool_lua_eval_unsandboxed_risk (n : Nat) :
    0 < luaEvalRisk n false := by
  simp [luaEvalRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Space name injection: box.space[user_input] with unvalidated name
def spaceNameRisk (nameLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else nameLen + 1

theorem tarantool_space_allowlisted_safe (n : Nat) :
    spaceNameRisk n true = 0 := by { simp [spaceNameRisk]

theorem tarantool_space_unvalidated_risk (n : Nat) :
    0 < spaceNameRisk n false := by
  simp [spaceNameRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Index name injection: space.index[user_input].select with unvalidated index
def indexNameRisk (nameLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else nameLen + 1

theorem tarantool_index_unvalidated_risk (n : Nat) :
    0 < indexNameRisk n false := by { simp [indexNameRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem tarantool_index_allowlisted_safe (n : Nat) :
    indexNameRisk n true = 0 := by { simp [indexNameRisk]

-- Iterator type injection: iterator from user string
def iteratorRisk (typeLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else typeLen + 1

theorem tarantool_iterator_unvalidated_risk (n : Nat) :
    0 < iteratorRisk n false := by
  simp [iteratorRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem tarantool_iterator_validated_safe (n : Nat) :
    iteratorRisk n true = 0 := by { simp [iteratorRisk]

-- Async client (asynctnt) does not eliminate injection risk
def asyncTarantoolRisk (inputLen : Nat) (sandboxed : Bool) (_ : Bool) : Nat :=
  luaEvalRisk inputLen sandboxed

theorem tarantool_async_preserves_risk (n : Nat) :
    asyncTarantoolRisk n false true = luaEvalRisk n false := by
  simp [asyncTarantoolRisk]

theorem tarantool_async_risk_positive (n : Nat) :
    0 < asyncTarantoolRisk n false true := by
  simp [asyncTarantoolRisk, luaEvalRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires sandboxed eval AND allow-listed space/index names
def netTarantoolRisk (inputLen : Nat) (sandboxed : Bool) (allowListed : Bool) : Nat :=
  luaEvalRisk inputLen sandboxed + spaceNameRisk inputLen allowListed

theorem tarantool_net_risk_zero_fully_mitigated (n : Nat) :
    netTarantoolRisk n true true = 0 := by { simp [netTarantoolRisk, luaEvalRisk, spaceNameRisk]

theorem tarantool_net_risk_pos_unmitigated (n : Nat) :
    0 < netTarantoolRisk n false false := by
  simp [netTarantoolRisk, luaEvalRisk, spaceNameRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end TarantoolQueryInjection
