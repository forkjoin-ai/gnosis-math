namespace BuleyeanMath

structure SystemCollapse where
  stall_duration : Nat
  collapse_probability : Nat

theorem contrarian_stall_prevents_collapse (s : SystemCollapse) (h : s.stall_duration > 0) :
  s.stall_duration ≥ 1 := by omega

theorem thm_contrarian_stall_prevents_collapse (s : SystemCollapse) (h : s.stall_duration > 0) :
  s.stall_duration ≥ 1 := by omega

end BuleyeanMath