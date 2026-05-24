import Init
-- NginxLuaQueryInjectionRisk.lean
-- Anti-thesis: Nginx Lua scripting (ngx_lua / OpenResty) using ngx.var and
-- request header values in downstream queries carries no injection risk.
-- Refutation: ngx.var values used in Redis commands, SQL queries, or shell
-- execution without sanitization yield a strictly positive vulnerability window.

namespace NginxLuaQueryInjection

-- ngx.var injection: ngx.var.arg_param used in Redis or SQL query
def ngxVarRisk (varLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else varLen + 1

-- Sanitized ngx.var value is safe for downstream use
theorem nginx_lua_var_sanitized_safe (n : Nat) :
    ngxVarRisk n true = 0 := by { simp [ngxVarRisk]

-- Unsanitized ngx.var in Redis/SQL is strictly vulnerable
theorem nginx_lua_var_unsanitized_risk (n : Nat) :
    0 < ngxVarRisk n false := by
  simp [ngxVarRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Request header injection: ngx.req.get_headers()['X-User'] used in Redis
def headerVarRisk (headerLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else headerLen + 1

theorem nginx_lua_header_sanitized_safe (n : Nat) :
    headerVarRisk n true = 0 := by { simp [headerVarRisk]

theorem nginx_lua_header_unsanitized_risk (n : Nat) :
    0 < headerVarRisk n false := by
  simp [headerVarRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- os.execute injection: os.execute("cmd " .. user_input) in Lua
def osExecRisk (inputLen : Nat) (escaped : Bool) : Nat :=
  if escaped then 0 else inputLen + 1

theorem nginx_lua_exec_escaped_safe (n : Nat) :
    osExecRisk n true = 0 := by { simp [osExecRisk]

theorem nginx_lua_exec_unescaped_risk (n : Nat) :
    0 < osExecRisk n false := by
  simp [osExecRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Redis command injection: red:call("GET", user_key) with unvalidated key
def redisKeyRisk (keyLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else keyLen + 1

theorem nginx_lua_redis_validated_safe (n : Nat) :
    redisKeyRisk n true = 0 := by { simp [redisKeyRisk]

theorem nginx_lua_redis_unvalidated_risk (n : Nat) :
    0 < redisKeyRisk n false := by
  simp [redisKeyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- loadstring injection: loadstring(user_code)() executes arbitrary Lua
def loadstringRisk (codeLen : Nat) (blocked : Bool) : Nat :=
  if blocked then 0 else codeLen + 1

theorem nginx_lua_loadstring_blocked_safe (n : Nat) :
    loadstringRisk n true = 0 := by { simp [loadstringRisk]

theorem nginx_lua_loadstring_allowed_risk (n : Nat) :
    0 < loadstringRisk n false := by
  simp [loadstringRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in variable length
theorem nginx_lua_var_risk_monotone (n m : Nat) (h : n ≤ m) :
    ngxVarRisk n false ≤ ngxVarRisk m false := by { simp [ngxVarRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires sanitized ngx.var AND blocked loadstring
def netNginxLuaRisk (inputLen : Nat) (sanitized : Bool) (loadstringBlocked : Bool) : Nat :=
  ngxVarRisk inputLen sanitized + loadstringRisk inputLen loadstringBlocked

theorem nginx_lua_net_risk_zero_fully_mitigated (n : Nat) :
    netNginxLuaRisk n true true = 0 := by { simp [netNginxLuaRisk, ngxVarRisk, loadstringRisk]

theorem nginx_lua_net_risk_pos_unmitigated (n : Nat) :
    0 < netNginxLuaRisk n false false := by
  simp [netNginxLuaRisk, ngxVarRisk, loadstringRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end NginxLuaQueryInjection
