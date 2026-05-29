import Init
import Gnosis.CausalDiamond

/-
  InformationLightCone.lean
  =========================

  Obligation 2 — the keystone — of the "Ackermann ceiling occupies the role
  of c" program (see `AckermannLightConeBridge`, `AckermannIsLightSpeed`).

  ## The intuition (Taylor): "light is information, just moving really fast"

  A spacetime constant `c` is dimensionful (length / time); the Ackermann
  ceiling is a bare number. They are identified only through a UNIT BRIDGE:
  a physical principle converting one computational step into one spacetime
  interval. That principle is the discrete form of the Margolus–Levitin
  bound — a physical system advances through at most `ν = 2E/(πℏ)`
  distinguishable states per unit time, so moving information one lattice
  cell costs at least one state-transition (one "tick"). Hence:

      maximum information-propagation speed  =  1 cell / tick  =  c.

  This module formalizes that statement directly on a discrete spacetime
  lattice. Information is a set of occupied cells evolving in ticks; the
  Margolus–Levitin / causality constraint is "a cell can only be lit at
  `t+1` if it or a neighbour was lit at `t`" (at most one cell of spread
  per tick). The theorem `info_within_cone` proves the front after `t`
  ticks is confined to `|x| ≤ t` — exactly the light cone. The photon
  (`photon`) saturates it: it sits on `|x| = t` at every tick. Light is
  the information front moving at the maximal admissible rate.

  We then connect this lattice cone to the `CausalDiamond` relativistic cone
  (`cell_in_causal_cone`): every reachable information cell is inside the
  future light cone of the origin event. The continuum derivation
  `ν_max · ℓ_P = c` from the full Margolus–Levitin / Bekenstein bounds is
  the cited physics input (real-valued; not mechanized in Init-only Lean) —
  what is mechanized is its discrete, dimensionless skeleton.

  Init + `CausalDiamond`. Zero `sorry`, zero new `axiom`.
-/

namespace InformationLightCone

open Gnosis.CausalDiamond

/-! ## Discrete spacetime: information as occupied lattice cells

  A `Signal` records, for each tick `t : Nat` and cell `x : Int`, whether
  the cell carries information. -/

abbrev Signal := Nat → Int → Bool

/-- The Margolus–Levitin lattice rate: a physical system advances through at
    most this many distinguishable cell-transitions per tick. At the Planck
    scale the bound is one. This `1` is the entire dimensionless content of
    the speed limit `c`. -/
def mlMaxCellsPerTick : Nat := 1

/-- **The speed-of-light / Margolus–Levitin constraint.** A cell can become
    occupied at tick `t+1` only if it, or an immediate neighbour, was
    occupied at tick `t`. Information spreads at most `mlMaxCellsPerTick = 1`
    cell per tick. -/
def RespectsLightSpeed (sig : Signal) : Prop :=
  ∀ t x, sig (t + 1) x = true →
    (sig t x = true ∨ sig t (x - 1) = true ∨ sig t (x + 1) = true)

/-- Information is seeded at the spatial origin at tick `0`. -/
def StartsAtOrigin (sig : Signal) : Prop :=
  ∀ x, sig 0 x = true → x = 0

/-! ## The information light cone -/

/-- **KEYSTONE.** Any signal that respects the speed-of-light constraint and
    starts at the origin is confined, after `t` ticks, to cells within
    distance `t`: `|x| ≤ t`. The maximum information-propagation speed is
    exactly one cell per tick — the discrete `c`. -/
theorem info_within_cone (sig : Signal)
    (hc : RespectsLightSpeed sig) (h0 : StartsAtOrigin sig) :
    ∀ t x, sig t x = true → x.natAbs ≤ t := by
  intro t
  induction t with
  | zero =>
    intro x hx
    have hx0 : x = 0 := h0 x hx
    subst hx0
    simp
  | succ t ih =>
    intro x hx
    rcases hc t x hx with h | h | h
    · have := ih x h; omega
    · have := ih (x - 1) h; omega
    · have := ih (x + 1) h; omega

/-! ## The photon: information at exactly c

  `photon t x` is lit exactly on the cell `x = t`. It is a valid signal
  (`photon_respects`, `photon_starts`), and it sits on the boundary of the
  cone at every tick (`photon_is_luminal`). Light is the saturating front. -/

/-- The photon worldline: occupied iff `x = t`. -/
def photon : Signal := fun t x => decide ((x : Int) = (t : Int))

theorem photon_starts : StartsAtOrigin photon := by
  intro x hx
  simp only [photon, decide_eq_true_iff] at hx
  exact_mod_cast hx

theorem photon_respects : RespectsLightSpeed photon := by
  intro t x hx
  simp only [photon, decide_eq_true_iff] at hx
  -- hx : (x : Int) = ((t + 1 : Nat) : Int)
  right; left
  simp only [photon, decide_eq_true_iff]
  -- goal : (x - 1 : Int) = (t : Int)
  omega

/-- **Saturation = lightlike.** The photon is lit on `x = t`, whose distance
    is exactly `t` — it rides the cone boundary at every tick. This is the
    information-theoretic twin of `AckermannLightConeBridge.front_is_lightlike`. -/
theorem photon_is_luminal (t : Nat) :
    photon t (t : Int) = true ∧ (t : Int).natAbs = t := by
  refine ⟨?_, ?_⟩
  · simp [photon]
  · simp

/-! ## Connecting the lattice cone to the relativistic CausalDiamond cone

  Every reachable information cell is inside the future light cone of the
  origin event, in the literal `CausalDiamond` sense. The discrete
  information cone and the spacetime light cone are the same cone. -/

/-- A reachable cell `(t, x)` with `|x| ≤ t` sits in the future light cone of
    the origin event `{time := 0, space := 0}`. -/
theorem cell_in_causal_cone (t : Nat) (x : Int) (h : x.natAbs ≤ t) :
    inFutureLightCone { time := 0, space := 0 } { time := (t : Int), space := x } = true := by
  unfold inFutureLightCone
  rw [decide_eq_true_iff]
  refine ⟨by omega, ?_⟩
  -- intervalSquared origin {time := t, space := x} = x*x - t*t ≤ 0
  have hsq : x * x ≤ (t : Int) * (t : Int) := by
    have hnat : x.natAbs * x.natAbs ≤ t * t := Nat.mul_self_le_mul_self h
    have hcast : ((x.natAbs * x.natAbs : Nat) : Int) ≤ ((t * t : Nat) : Int) := by
      exact_mod_cast hnat
    have hxabs : ((x.natAbs * x.natAbs : Nat) : Int) = x * x := by
      push_cast [Int.natAbs_mul_self]
      exact Int.natAbs_mul_self
    rw [hxabs] at hcast
    have htt : ((t * t : Nat) : Int) = (t : Int) * (t : Int) := by push_cast; ring
    rw [htt] at hcast
    exact hcast
  show intervalSquared { time := 0, space := 0 } { time := (t : Int), space := x } ≤ 0
  rw [show intervalSquared { time := 0, space := 0 } { time := (t : Int), space := x }
        = x * x - (t : Int) * (t : Int) from by
        show (x - 0) * (x - 0) - ((t : Int) - 0) * ((t : Int) - 0) = _
        simp [Int.sub_zero]]
  omega

/-- **The unit bridge, stated.** Maximum information speed equals the cone
    slope `c = 1`: the largest distance any origin-seeded, light-speed-
    respecting signal reaches by tick `t` is `t`, and the photon attains it.
    The dimensionless `c` is `mlMaxCellsPerTick`. -/
theorem max_information_speed_is_c :
    mlMaxCellsPerTick = 1 ∧
    -- nothing outruns the cone …
    (∀ sig, RespectsLightSpeed sig → StartsAtOrigin sig →
      ∀ t x, sig t x = true → x.natAbs ≤ t) ∧
    -- … and the photon attains it (saturation realizable).
    (∀ t, photon t (t : Int) = true ∧ (t : Int).natAbs = t) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro sig hc h0; exact info_within_cone sig hc h0
  · intro t; exact photon_is_luminal t

end InformationLightCone
