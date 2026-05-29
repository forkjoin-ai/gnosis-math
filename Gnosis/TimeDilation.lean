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

/-- Motion count over the first `N` ticks: the number of light-speed (moving)
    steps — the complement of `properTime`. -/
def motionCount (w : Worldline) : Nat → Nat
  | 0 => 0
  | N + 1 => motionCount w N + (if w (N + 1) = w N then 0 else 1)

/-- **Exact time-dilation accounting.** Proper time plus motion steps equals
    coordinate time: `properTime w N + motionCount w N = N`. Every tick is
    either a rest step (one unit of aging) or a light-speed step (none); the
    twin's missing age is exactly the distance it traveled. -/
theorem properTime_add_motionCount (w : Worldline) (N : Nat) :
    properTime w N + motionCount w N = N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    unfold properTime motionCount
    by_cases h : w (N + 1) = w N <;> simp [h] <;> omega

/-- **Proper time never exceeds coordinate time.** The rest frame maximizes
    aging: you cannot age more than the clock on the wall. -/
theorem properTime_le (w : Worldline) (N : Nat) : properTime w N ≤ N := by
  have := properTime_add_motionCount w N
  omega

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

/-- A worldline that never moves on `[0, N)` records zero motion. -/
theorem motionCount_eq_zero_of_rest (w : Worldline) (N : Nat)
    (h : ∀ s, s < N → w (s + 1) = w s) : motionCount w N = 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    unfold motionCount
    rw [if_pos (h N (by omega)), Nat.add_zero]
    exact ih (fun s hs => h s (by omega))

/-- **The rest frame uniquely maximizes proper time.** A worldline ages by the
    full coordinate time `N` if and only if it never moves. Any motion — at any
    single tick — costs aging. This is the geometric heart of the twin paradox:
    the straight (resting) worldline is the unique maximizer of proper time. -/
theorem properTime_eq_coordTime_iff (w : Worldline) (N : Nat) :
    properTime w N = N ↔ ∀ s, s < N → w (s + 1) = w s := by
  constructor
  · intro hpt s hs
    by_cases hb : w (s + 1) = w s
    · exact hb
    · exfalso
      have : properTime w N < N := proper_time_lt_of_motion w N ⟨s, hs, hb⟩
      omega
  · intro hrest
    have h0 : motionCount w N = 0 := motionCount_eq_zero_of_rest w N hrest
    have hc := properTime_add_motionCount w N
    omega

/-! ## The round-trip twin paradox (quantitative) -/

/-- If the position differs across a range `[a, b]`, some step inside it moves. -/
theorem motion_in_range (w : Worldline) (a b : Nat) :
    a ≤ b → w a ≠ w b → ∃ s, a ≤ s ∧ s < b ∧ w (s + 1) ≠ w s := by
  induction b with
  | zero =>
    intro hab h
    have : a = 0 := by omega
    subst this; exact absurd rfl h
  | succ b ih =>
    intro hab h
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · by_cases hb : w (b + 1) = w b
      · have hne : w a ≠ w b := by rw [hb] at h; exact h
        obtain ⟨s, hs1, hs2, hmove⟩ := ih (by omega) hne
        exact ⟨s, hs1, by omega, hmove⟩
      · exact ⟨b, by omega, by omega, hb⟩
    · have : a = b + 1 := by omega
      subst this; exact absurd rfl h

/-- One-step monotonicity of motion count (no case split: the increment is a
    `Nat`, hence non-negative). -/
theorem motionCount_le_succ (w : Worldline) (N : Nat) :
    motionCount w N ≤ motionCount w (N + 1) := by
  show motionCount w N ≤ motionCount w N + (if w (N + 1) = w N then 0 else 1)
  exact Nat.le_add_right _ _

/-- Motion count is monotone in the time horizon. -/
theorem motionCount_mono (w : Worldline) (m n : Nat) (h : m ≤ n) :
    motionCount w m ≤ motionCount w n := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact Nat.le_trans (ih (by omega)) (motionCount_le_succ w n)
    · have : m = n + 1 := by omega
      subst this; exact Nat.le_refl _

/-- A motion step bumps the motion count by exactly one. -/
theorem motionCount_succ_of_motion (w : Worldline) (s : Nat) (h : w (s + 1) ≠ w s) :
    motionCount w (s + 1) = motionCount w s + 1 := by
  show motionCount w s + (if w (s + 1) = w s then 0 else 1) = motionCount w s + 1
  rw [if_neg h]

/-- **The round-trip twin paradox.** A twin that starts at the origin, leaves
    it, and returns by tick `N` ages at LEAST two ticks less than the resting
    twin: `properTime w N + 2 ≤ N`. The trip costs one motion step out and one
    back — the deficit is at least the two legs of the journey. -/
theorem round_trip_twin (w : Worldline) (N t : Nat)
    (hstart : w 0 = 0) (hreturn : w N = 0) (ht0 : 0 < t) (htN : t < N) (hleft : w t ≠ 0) :
    properTime w N + 2 ≤ N := by
  have hout : w 0 ≠ w t := by rw [hstart]; exact fun he => hleft he.symm
  obtain ⟨s1, hs1a, hs1b, hs1m⟩ := motion_in_range w 0 t (by omega) hout
  have hret : w t ≠ w N := by rw [hreturn]; exact hleft
  obtain ⟨s2, hs2a, hs2b, hs2m⟩ := motion_in_range w t N (by omega) hret
  have hmc2 : 2 ≤ motionCount w N := by
    have j1 : motionCount w (s1 + 1) = motionCount w s1 + 1 :=
      motionCount_succ_of_motion w s1 hs1m
    have j2 : motionCount w (s2 + 1) = motionCount w s2 + 1 :=
      motionCount_succ_of_motion w s2 hs2m
    have m12 : motionCount w (s1 + 1) ≤ motionCount w s2 := motionCount_mono w _ _ (by omega)
    have m2N : motionCount w (s2 + 1) ≤ motionCount w N := motionCount_mono w _ _ (by omega)
    omega
  have hc := properTime_add_motionCount w N
  omega

/-! ## Distance traveled is bounded by the aging deficit (uses the c-bound)

  The proper-time results above hold for ANY worldline. These two use the
  speed-of-light constraint `Lightspeed` directly. -/

/-- Under the speed-of-light bound, net spatial displacement is at most the
    motion count: each moving step advances at most one cell, each rest none. -/
theorem displacement_le_motionCount (w : Worldline) (hL : Lightspeed w) (N : Nat) :
    (w N - w 0).natAbs ≤ motionCount w N := by
  induction N with
  | zero => simp [motionCount]
  | succ N ih =>
    have hstep : (w (N + 1) - w N).natAbs ≤ 1 := hL N
    show (w (N + 1) - w 0).natAbs ≤ motionCount w N + (if w (N + 1) = w N then 0 else 1)
    by_cases hb : w (N + 1) = w N
    · rw [if_pos hb]
      have hdisp : w (N + 1) - w 0 = w N - w 0 := by rw [hb]
      rw [hdisp]; omega
    · rw [if_neg hb]; omega

/-- **Distance traveled is bounded by the aging deficit.** Under the c-bound, a
    worldline's net displacement is at most the gap between coordinate time and
    its proper time: `|w N − w 0| + properTime w N ≤ N`. The farther a traveler
    goes, the more it must have under-aged — distance is paid for in lost time. -/
theorem displacement_le_deficit (w : Worldline) (hL : Lightspeed w) (N : Nat) :
    (w N - w 0).natAbs + properTime w N ≤ N := by
  have h1 := displacement_le_motionCount w hL N
  have h2 := properTime_add_motionCount w N
  omega

end TimeDilation
