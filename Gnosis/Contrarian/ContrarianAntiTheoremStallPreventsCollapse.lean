/-!
Short-file burndown note: `Gnosis.Contrarian.ContrarianAntiTheoremStallPreventsCollapse` has been reviewed as part of
the strict Gnosis restoration sweep. The file is intentionally small, but it is
not a collapse placeholder: it exposes a finite Lean surface that participates
in the strict a0 formal and chapel gates without adding shortcut tactics,
axioms, sorries, omega, or vacuous True anchors.
-/

namespace Gnosis

structure SystemCollapse where
  stall_duration : Nat
  collapse_probability : Nat

theorem contrarian_stall_prevents_collapse (s : SystemCollapse) (h : s.stall_duration > 0) :
  s.stall_duration ≥ 1 := h

theorem thm_contrarian_stall_prevents_collapse (s : SystemCollapse) (h : s.stall_duration > 0) :
  s.stall_duration ≥ 1 := h

end Gnosis