import Init

/-
  TimeDilation.lean
  =================

  The twin paradox on the light-cone lattice, continuing the time / time-travel
  thread (`InformationLightCone`, `TimeTravelLightCone`).

  A worldline assigns a spatial position to each integer tick. The same
  speed-of-light constraint as `InformationLightCone` (`|Δx| ≤ 1` per tick)
  governs it. PROPER TIME along a worldline is the number of REST steps
  (`x(t+1) = x(t)`): a light-speed step (`|Δx| = 1`) is lightlike and carries no
  proper time, the discrete shadow of `dτ = √(dt² − dr²) = 0` on the cone.

  Consequences, all proved:
    * `properTime_le`      — proper time never exceeds coordinate time
                             (the rest frame maximizes aging).
    * `home_twin`          — the resting twin's proper time equals `N`.
    * `proper_time_lt_of_motion` — any spatial motion strictly reduces aging.
    * `twin_paradox`       — a twin that leaves the origin and returns ages
                             STRICTLY less than the one who stayed.

  Init-only. Zero `sorry`, zero new `axiom`.
-/

namespace TimeDilation

/-- A worldline: spatial position at each integer tick. -/
def Worldline := Nat → Int

/-- The speed-of-light constraint: at most one cell of spatial motion per tick. -/
def Lightspeed (w : Worldline) : Prop :=
  ∀ t, (w (t + 1) - w t).natAbs ≤ 1

/-- Proper time over the first `N` ticks: the number of REST steps. A
    light-speed step contributes nothing (lightlike). -/
def properTime (w : Worldline) : Nat → Nat
  | 0 => 0
  | N + 1 => properTime w N + (if w (N + 1) = w N then 1 else 0)

/-- **Proper time never exceeds coordinate time.** The rest frame maximizes
    aging: you cannot age more than the clock on the wall. -/
theorem properTime_le (w : Worldline) (N : Nat) : properTime w N ≤ N := by
  induction N with
  | zero => simp [properTime]
  | succ N ih =>
    unfold properTime
    by_cases h : w (N + 1) = w N <;> simp [h] <;> omega

/-- The resting (home) twin ages by exactly the coordinate time. -/
theorem home_twin (N : Nat) : properTime (fun _ => 0) N = N := by
  induction N with
  | zero => simp [properTime]
  | succ N ih => unfold properTime; simp [ih]

/-- **Any motion strictly reduces aging.** If the worldline moves on some step
    in `[0, N)`, its proper time is strictly less than `N` — the moving twin
    ages less. -/
theorem proper_time_lt_of_motion (w : Worldline) (N : Nat)
    (h : ∃ t, t < N ∧ w (t + 1) ≠ w t) : properTime w N < N := by
  induction N with
  | zero => obtain ⟨t, ht, _⟩ := h; omega
  | succ N ih =>
    obtain ⟨t, ht, hmove⟩ := h
    unfold properTime
    rcases Nat.lt_or_ge t N with htN | htN
    · -- motion happens before the last step: use IH, last step adds ≤ 1
      have hlt : properTime w N < N := ih ⟨t, htN, hmove⟩
      by_cases hb : w (N + 1) = w N <;> simp [hb] <;> omega
    · -- the witnessed step is the last one (t = N): it is a motion step, adds 0
      have ht' : t = N := by omega
      have hb : w (N + 1) ≠ w N := by rw [← ht']; exact hmove
      simp [hb]
      have := properTime_le w N
      omega

/-- If the position differs from its start, some step was a motion step. -/
theorem motion_of_ne (w : Worldline) (t : Nat) (h : w t ≠ w 0) :
    ∃ s, s < t ∧ w (s + 1) ≠ w s := by
  induction t with
  | zero => exact absurd rfl h
  | succ t ih =>
    by_cases hb : w (t + 1) = w t
    · have hne : w t ≠ w 0 := by rw [hb] at h; exact h
      obtain ⟨s, hs, hmove⟩ := ih hne
      exact ⟨s, by omega, hmove⟩
    · exact ⟨t, by omega, hb⟩

/-- **The twin paradox.** A twin who starts at the origin, leaves it at some
    point, and returns to it by tick `N` ages STRICTLY less than the twin who
    never left (whose proper time is `N`). Travel costs aging. -/
theorem twin_paradox (w : Worldline) (N t : Nat)
    (hstart : w 0 = 0) (ht : t < N) (hleft : w t ≠ 0) :
    properTime w N < N := by
  apply proper_time_lt_of_motion
  have hne : w t ≠ w 0 := by rw [hstart]; exact hleft
  obtain ⟨s, hs, hmove⟩ := motion_of_ne w t hne
  exact ⟨s, by omega, hmove⟩

end TimeDilation
