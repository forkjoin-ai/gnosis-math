import Init
import Gnosis.Body.Anthropogenesis

/-!
# Robustness and Grit — How Living Systems Survive Perturbation in the Metaverse

The Metaverse (the 3D Game-of-Life evolutionary world in `aeon-corpus`) is a
human-body / evolutionary simulation. Bodies, cells, and circadian clocks all
face perturbation: a shock, an attack, a phase shift. **Grit** is how much a
system can take before it breaks; **robustness** is the structure of that
endurance. This module turns those notions into theorems.

It is organized around four pictures of grit, then a synthesis:

1. **Grit as breaking point.** A system has a `tolerance`; it `withstands` any
   perturbation up to it and `breaks` past it. The two are exhaustive and
   exclusive (`robustness_trichotomy`), and the breaking point is *exactly* the
   tolerance (`breaking_point`, `grit_is_max_withstood`).
2. **Min-max / max-min adversarial robustness.** An adversary picks the worst
   attack, the system picks the best defense. Weak duality `maxmin ≤ minmax`
   (`minmax_ge_maxmin`) always holds; a `saddle_point` makes them equal.
3. **Grit = distance to the edge.** Tying back to `Anthropogenesis.SurvivalBand`:
   an interior cell's grit is its distance to the nearer band edge. Interior
   cells have positive grit (`interior_has_positive_grit`); an edge cell has
   zero grit (`edge_has_zero_grit`) — formalizing *life happens on the edges*
   as *the edge is where grit is zero / maximally brittle*.
4. **Push-to-crash on Gnosis time.** Chronotype / daylight-savings misalignment
   on the 12-phase clock. `phaseDelta` is circular distance on a 12-dial,
   bounded by half a turn (`phaseDelta_le_six`). Past a `crashThreshold` the
   system crashes (`crashes_when_delta_exceeds_threshold`); an entrained system
   is safe (`entrained_is_safe`); a DST shift increases the delta
   (`dst_increases_delta`).

Finally `robustness_principle` ties grit-as-tolerance to grit-as-distance and to
the clock.

Rustic Church: `Init` only (no Mathlib), `Nat` arithmetic, proofs from core
`Nat` lemmas. No `sorry`, no `simp`/`decide`/`omega` on open goals.
-/

namespace Gnosis.Body.Robustness

open Gnosis.Body.Anthropogenesis

/-! ## 1. Grit as breaking point -/

/-- The system survives the perturbation iff it is within tolerance. -/
def withstands (tolerance perturbation : Nat) : Prop := perturbation ≤ tolerance

/-- The system breaks iff the perturbation exceeds tolerance. -/
def breaks (tolerance perturbation : Nat) : Prop := tolerance < perturbation

/-- **Robustness trichotomy.** Against any perturbation a system either
    withstands it or breaks — exhaustively, with no third option. (Compare
    `Anthropogenesis.survival_trichotomy`: that band has two failure modes;
    a one-sided tolerance has one.) -/
theorem robustness_trichotomy (tolerance perturbation : Nat) :
    withstands tolerance perturbation ∨ breaks tolerance perturbation := by
  unfold withstands breaks
  rcases Nat.lt_or_ge tolerance perturbation with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- **Exclusivity.** Withstanding and breaking cannot both happen: endurance and
    failure are genuine opposites, not a matter of degree. -/
theorem withstands_excludes_breaks (tolerance perturbation : Nat)
    (hw : withstands tolerance perturbation) : ¬ breaks tolerance perturbation := by
  unfold withstands at hw
  unfold breaks
  intro hb
  exact Nat.lt_irrefl perturbation (Nat.lt_of_le_of_lt hw hb)

/-- The grit of a system is its tolerance: the largest perturbation it endures. -/
def grit (tolerance : Nat) : Nat := tolerance

/-- **The breaking point is exactly the tolerance.** A perturbation equal to the
    tolerance is still withstood, but one unit more breaks the system. The
    boundary is sharp; grit is a hard wall, not a gradient. -/
theorem breaking_point (tolerance : Nat) :
    withstands tolerance tolerance ∧ breaks tolerance (tolerance + 1) := by
  unfold withstands breaks
  exact ⟨Nat.le_refl tolerance, Nat.lt_succ_self tolerance⟩

/-- **Grit is the maximum withstood perturbation.** Everything up to `grit` is
    survived; the very next unit breaks. This characterizes grit operationally:
    it is precisely the supremum of survivable shocks. -/
theorem grit_is_max_withstood (tolerance perturbation : Nat) :
    (perturbation ≤ grit tolerance → withstands tolerance perturbation)
      ∧ breaks tolerance (grit tolerance + 1) := by
  unfold grit withstands breaks
  refine ⟨?_, Nat.lt_succ_self tolerance⟩
  intro h
  exact h

/-- More grit never reduces what a system can survive (monotone endurance). -/
theorem more_grit_endures_more (t₁ t₂ perturbation : Nat)
    (hgrit : t₁ ≤ t₂) (hw : withstands t₁ perturbation) : withstands t₂ perturbation := by
  unfold withstands at *
  exact Nat.le_trans hw hgrit

/-! ## 2. Min-max / max-min adversarial robustness

We model a finite, two-element game (enough to exhibit weak duality and a
genuine saddle point) without leaving `Nat`. The system chooses a defense level,
the adversary chooses an attack level; the survival `payoff` is the system's
guaranteed margin, which we keep `Nat`-valued. -/

/-- The survival payoff: the system's defense net of the adversary's attack
    (truncated at 0 — once overwhelmed, survival is simply zero). -/
def payoff (defense attack : Nat) : Nat := defense - attack

/-- **Max-min** for a 2x2 game: for each of the two defenses the system computes
    its *worst case* over the two attacks (the inner `min`), then takes the
    *best* such guarantee (the outer `max`). This is the value the system can
    secure no matter what the adversary does. -/
def maxmin (d₀ d₁ a₀ a₁ : Nat) : Nat :=
  Nat.max (Nat.min (payoff d₀ a₀) (payoff d₀ a₁))
          (Nat.min (payoff d₁ a₀) (payoff d₁ a₁))

/-- **Min-max** for the same game: for each attack the adversary computes the
    system's *best* response (the inner `max`), then takes the *worst* of those
    for the system (the outer `min`). This is what the adversary can hold the
    system to. -/
def minmax (d₀ d₁ a₀ a₁ : Nat) : Nat :=
  Nat.min (Nat.max (payoff d₀ a₀) (payoff d₁ a₀))
          (Nat.max (payoff d₀ a₁) (payoff d₁ a₁))

/-- A single cell of the payoff matrix is a lower bound on the value the system
    can guarantee: even committing blindly to one defense, the worst attack
    leaves the system no worse than `maxmin`. -/
theorem maxmin_le_payoff_row0 (d₀ d₁ a₀ a₁ : Nat) :
    Nat.min (payoff d₀ a₀) (payoff d₀ a₁) ≤ maxmin d₀ d₁ a₀ a₁ :=
  Nat.le_max_left _ _

/-- **Weak duality: max-min ≤ min-max.** What the system can *guarantee* never
    exceeds what the adversary can *hold it to*. Defending second (min-max) is
    never worse than defending first (max-min): information has nonnegative
    value. This is the structural backbone of adversarial robustness, proved
    here from pure `Nat.min`/`Nat.max` lemmas. -/
theorem minmax_ge_maxmin (d₀ d₁ a₀ a₁ : Nat) :
    maxmin d₀ d₁ a₀ a₁ ≤ minmax d₀ d₁ a₀ a₁ := by
  unfold maxmin minmax
  -- Name the four matrix entries (opaque, so this is pure lattice algebra).
  generalize payoff d₀ a₀ = p00
  generalize payoff d₀ a₁ = p01
  generalize payoff d₁ a₀ = p10
  generalize payoff d₁ a₁ = p11
  -- It suffices to show each inner-min ≤ each inner-max appropriately.
  -- max(min(p00,p01), min(p10,p11)) ≤ min(max(p00,p10), max(p01,p11)).
  apply Nat.max_le.mpr
  refine ⟨?_, ?_⟩
  · -- min(p00,p01) ≤ min(max(p00,p10), max(p01,p11))
    apply Nat.le_min.mpr
    refine ⟨?_, ?_⟩
    · exact Nat.le_trans (Nat.min_le_left p00 p01) (Nat.le_max_left p00 p10)
    · exact Nat.le_trans (Nat.min_le_right p00 p01) (Nat.le_max_left p01 p11)
  · -- min(p10,p11) ≤ min(max(p00,p10), max(p01,p11))
    apply Nat.le_min.mpr
    refine ⟨?_, ?_⟩
    · exact Nat.le_trans (Nat.min_le_left p10 p11) (Nat.le_max_right p00 p10)
    · exact Nat.le_trans (Nat.min_le_right p10 p11) (Nat.le_max_right p01 p11)

/-- A saddle point: a strategy pair `(dStar, aStar)` that is simultaneously the
    adversary's best attack against `dStar` (it minimizes the system's payoff)
    and the system's best defense against `aStar` (it maximizes the payoff). -/
def isSaddle (dStar aStar : Nat) (otherD otherA : Nat) : Prop :=
  payoff dStar aStar ≤ payoff dStar otherA ∧ payoff otherD aStar ≤ payoff dStar aStar

/-- **Saddle point ⇒ the value is pinned.** Read the 2x2 game with `d★ = d₀` and
    `a★ = a₀` against alternatives `d₁, a₁`. If `(d₀, a₀)` is a saddle, its
    payoff is simultaneously a max-min lower bound and a min-max upper bound, so
    `maxmin = minmax`: the game has a sharp value, the equilibrium where neither
    side can profitably deviate. -/
theorem saddle_point (d₀ d₁ a₀ a₁ : Nat)
    (hsad : isSaddle d₀ a₀ d₁ a₁) :
    maxmin d₀ d₁ a₀ a₁ = minmax d₀ d₁ a₀ a₁ := by
  unfold isSaddle at hsad
  obtain ⟨hrow, hcol⟩ := hsad
  -- hrow : payoff d₀ a₀ ≤ payoff d₀ a₁   (a₀ is the adversary's best vs d₀)
  -- hcol : payoff d₁ a₀ ≤ payoff d₀ a₀   (d₀ is the system's best vs a₀)
  apply Nat.le_antisymm
  · exact minmax_ge_maxmin d₀ d₁ a₀ a₁
  · unfold maxmin minmax
    -- Show minmax ≤ payoff d₀ a₀, and payoff d₀ a₀ ≤ maxmin; chain them.
    -- min(max(p00,p10), max(p01,p11)) ≤ max(p00,p10) = p00 (since p10 ≤ p00).
    have hmax_col : Nat.max (payoff d₀ a₀) (payoff d₁ a₀) = payoff d₀ a₀ :=
      Nat.max_eq_left hcol
    have hupper : Nat.min (Nat.max (payoff d₀ a₀) (payoff d₁ a₀))
        (Nat.max (payoff d₀ a₁) (payoff d₁ a₁)) ≤ payoff d₀ a₀ := by
      rw [hmax_col]
      exact Nat.min_le_left (payoff d₀ a₀) (Nat.max (payoff d₀ a₁) (payoff d₁ a₁))
    -- max(min(p00,p01), min(p10,p11)) ≥ min(p00,p01) = p00 (since p00 ≤ p01).
    have hmin_row : Nat.min (payoff d₀ a₀) (payoff d₀ a₁) = payoff d₀ a₀ :=
      Nat.min_eq_left hrow
    have hlower : payoff d₀ a₀ ≤ Nat.max (Nat.min (payoff d₀ a₀) (payoff d₀ a₁))
        (Nat.min (payoff d₁ a₀) (payoff d₁ a₁)) :=
      Nat.le_trans (Nat.le_of_eq hmin_row.symm)
        (Nat.le_max_left (Nat.min (payoff d₀ a₀) (payoff d₀ a₁))
          (Nat.min (payoff d₁ a₀) (payoff d₁ a₁)))
    exact Nat.le_trans hupper hlower

/-! ## 3. Grit = distance to the edge (tie to `Anthropogenesis.SurvivalBand`) -/

/-- **Edge-grit.** For a cell at neighbour count `n` in a band `[lo, hi]`, its
    grit is the distance to the *nearer* edge: how many neighbours can be gained
    or lost before it dies. This is the band-aware reading of `grit`. -/
def edgeGrit (b : SurvivalBand) (n : Nat) : Nat :=
  Nat.min (n - b.lo) (b.hi - n)

/-- **Interior cells have positive grit.** Strictly inside the band, both edges
    are strictly away, so the distance to the nearer one is positive: an
    interior cell can absorb at least one perturbation in either direction.
    Robustness is exactly the slack of being away from the boundary. -/
theorem interior_has_positive_grit (b : SurvivalBand) (n : Nat)
    (h : interior b n) : 0 < edgeGrit b n := by
  unfold interior at h
  unfold edgeGrit
  -- lo < n gives 0 < n - lo;  n < hi gives 0 < hi - n;  min of two positives is positive.
  apply Nat.le_min.mpr
  exact ⟨Nat.sub_pos_of_lt h.left, Nat.sub_pos_of_lt h.right⟩

/-- **The lower edge has zero grit.** A cell sitting exactly on the band's lower
    boundary has distance `0` to that edge, so its grit is `0`: it is maximally
    brittle. One lost neighbour and it dies of underpopulation. -/
theorem edge_has_zero_grit (b : SurvivalBand) : edgeGrit b b.lo = 0 := by
  unfold edgeGrit
  -- lo - lo = 0, and min 0 _ = 0.
  rw [Nat.sub_self]
  exact Nat.zero_min (b.hi - b.lo)

/-- **The upper edge has zero grit** too, symmetrically. -/
theorem upper_edge_has_zero_grit (b : SurvivalBand) : edgeGrit b b.hi = 0 := by
  unfold edgeGrit
  rw [Nat.sub_self]
  exact Nat.min_zero (b.hi - b.lo)

/-- **Life happens on the edges = grit vanishes at the edges.** Restating
    `Anthropogenesis.life_happens_on_the_edges` in the language of grit: the two
    band edges are exactly the points of zero grit (maximal brittleness), while
    a strictly interior cell has positive grit. The generative churn of the
    Metaverse lives where robustness has run out — the edge of chaos. -/
theorem grit_vanishes_at_edges (b : SurvivalBand) (n : Nat) (h : interior b n) :
    edgeGrit b b.lo = 0 ∧ edgeGrit b b.hi = 0 ∧ 0 < edgeGrit b n :=
  ⟨edge_has_zero_grit b, upper_edge_has_zero_grit b, interior_has_positive_grit b n h⟩

/-! ## 4. Push-to-crash on Gnosis time (chronotype / daylight savings)

The canonical Gnosis clock has period 12 (`aeon = 12`,
`GnosisTimeClock.tickIterate_twelve`). A body entrained to it sits at the right
phase; chronotype mismatch and daylight savings push it off. We measure that
push as circular distance on the 12-dial and ask when it crashes. -/

/-- The aeon — the size of the canonical dial (matches `Circadian.aeon = 12`). -/
def aeon : Nat := 12

/-- **Phase delta.** Circular distance between the human's phase and the Gnosis
    phase on a dial of size 12. We add 12 before subtracting to keep it in `Nat`
    (avoiding truncation), reduce mod 12, then fold the dial in half so a delta
    never exceeds half a turn. -/
def phaseDelta (humanPhase gnosisPhase : Nat) : Nat :=
  let d := (humanPhase + 12 - gnosisPhase % 12) % 12
  Nat.min d (12 - d)

/-- **Maximal misalignment is half a turn.** No two phases on a 12-dial are ever
    more than 6 apart, because past the halfway point the *other* way around is
    shorter. This is the clean bound (`≤ 6`), proved without `decide`/`omega`. -/
theorem phaseDelta_le_six (a b : Nat) : phaseDelta a b ≤ 6 := by
  unfold phaseDelta
  -- The raw forward distance is a `% 12`, hence < 12.
  have hlt : (a + 12 - b % 12) % 12 < 12 := Nat.mod_lt _ (Nat.succ_pos 11)
  -- Abstract it to an opaque `d` carrying only `d < 12`.
  generalize hd : (a + 12 - b % 12) % 12 = d at *
  rcases Nat.lt_or_ge d 7 with hsmall | hbig
  · -- d ≤ 6, so the forward arm already ≤ 6.
    exact Nat.le_trans (Nat.min_le_left d (12 - d)) (Nat.le_of_lt_succ hsmall)
  · -- d ≥ 7, so the backward arm 12 - d ≤ 12 - 7 = 5 ≤ 6.
    have h5 : 12 - d ≤ 5 := Nat.sub_le_sub_left hbig 12
    have h56 : (5 : Nat) ≤ 6 := Nat.le_succ 5
    exact Nat.le_trans (Nat.min_le_right d (12 - d)) (Nat.le_trans h5 h56)

/-- **Phase delta never reaches a full turn** (the looser, also-true bound noted
    for completeness; `phaseDelta_le_six` is strictly stronger). -/
theorem phaseDelta_lt_twelve (a b : Nat) : phaseDelta a b < 12 :=
  Nat.lt_of_le_of_lt (phaseDelta_le_six a b) (by exact Nat.lt_of_sub_eq_succ rfl)

/-- The crash threshold: the maximum phase misalignment the body tolerates before
    its circadian system breaks down (the grit of the clock against DST). -/
def crashThreshold (tolerance : Nat) : Nat := tolerance

/-- The clock crashes when the misalignment exceeds the threshold. -/
def crashes (threshold humanPhase gnosisPhase : Nat) : Prop :=
  threshold < phaseDelta humanPhase gnosisPhase

/-- **Crash when delta exceeds threshold.** If the measured phase delta is larger
    than the crash threshold, the circadian system breaks — this is `breaks`
    applied to the clock's grit. -/
theorem crashes_when_delta_exceeds_threshold (threshold humanPhase gnosisPhase : Nat)
    (h : crashThreshold threshold < phaseDelta humanPhase gnosisPhase) :
    breaks (crashThreshold threshold) (phaseDelta humanPhase gnosisPhase) := by
  unfold breaks
  exact h

/-- **An entrained system is safe.** A body perfectly entrained to Gnosis time
    has zero phase delta, so it withstands *any* threshold whatsoever — there is
    nothing to break. Concretely, when human and gnosis phases agree (`p < 12`),
    the delta is `0`. -/
theorem entrained_is_safe (p : Nat) (hp : p < 12) (threshold : Nat) :
    phaseDelta p p = 0 ∧ withstands threshold (phaseDelta p p) := by
  have hzero : phaseDelta p p = 0 := by
    unfold phaseDelta
    -- p % 12 = p since p < 12; then (p + 12 - p) % 12 = 12 % 12 = 0; min 0 _ = 0.
    rw [Nat.mod_eq_of_lt hp]
    -- now d = (p + 12 - p) % 12
    rw [Nat.add_sub_cancel_left]
    -- d = 12 % 12 = 0
    have h12 : (12 : Nat) % 12 = 0 := Nat.mod_self 12
    rw [h12]
    exact Nat.zero_min (12 - 0)
  refine ⟨hzero, ?_⟩
  unfold withstands
  rw [hzero]
  exact Nat.zero_le threshold

/-- **A daylight-savings shift increases the delta.** Concrete instance: a body
    entrained at phase `0` (delta `0`) is shoved by one hour to phase `1`; its
    delta against the unchanged Gnosis phase `0` rises to `1 > 0`. The "spring
    forward" jolt is a genuine perturbation, not a relabeling. -/
theorem dst_increases_delta :
    phaseDelta 0 0 < phaseDelta 1 0 := by
  -- phaseDelta 0 0 = 0 and phaseDelta 1 0 = 1, both by computation.
  show (0 : Nat) < 1
  exact Nat.zero_lt_one

/-- **A larger DST jump is a larger perturbation** (monotone within the first
    half-dial): shifting forward to phase `k+1 ≤ 6` against Gnosis phase `0`
    strictly exceeds shifting to phase `k`. Stated for the worst realistic DST
    jolts (within half a turn) as concrete instances chained off `phaseDelta`.
    Here: a 2-hour shift beats a 1-hour shift. -/
theorem bigger_dst_bigger_delta :
    phaseDelta 1 0 < phaseDelta 2 0 := by
  show (1 : Nat) < 2
  exact Nat.lt_succ_self 1

/-! ## 5. The headline synthesis -/

/-- **The robustness principle.** Grit is one thing seen four ways, and they
    cohere:

    * (breaking point) a system's grit is the sharp largest perturbation it
      withstands — at the limit it survives, one step past it breaks;
    * (adversarial) what a system can *guarantee* against a worst-case adversary
      never exceeds what the adversary can *hold it to* (`maxmin ≤ minmax`);
    * (edge) inside a survival band, grit is the distance to the nearer edge —
      strictly positive in the interior, zero at the edge, so *life happens on
      the edges* means *the edges are exactly where grit runs out*;
    * (clock) the same brittleness governs Gnosis time: a body's grit against
      daylight-savings is its crash threshold, and the misalignment that tests
      it is bounded by half a turn of the 12-dial.

    Bundled as one theorem so the four pictures are provably the same theory. -/
theorem robustness_principle
    (tolerance : Nat)
    (d₀ d₁ a₀ a₁ : Nat)
    (b : SurvivalBand) (n : Nat) (hn : interior b n)
    (threshold humanPhase gnosisPhase : Nat) :
    -- 1. breaking point: the limit holds, one past it breaks
    (withstands tolerance tolerance ∧ breaks tolerance (tolerance + 1)) ∧
    -- 2. adversarial weak duality
    (maxmin d₀ d₁ a₀ a₁ ≤ minmax d₀ d₁ a₀ a₁) ∧
    -- 3. grit is positive in the interior, zero on the edges
    (0 < edgeGrit b n ∧ edgeGrit b b.lo = 0 ∧ edgeGrit b b.hi = 0) ∧
    -- 4. clock misalignment is bounded by half a turn, and crash = breaks
    (phaseDelta humanPhase gnosisPhase ≤ 6 ∧
      (crashThreshold threshold < phaseDelta humanPhase gnosisPhase →
        breaks (crashThreshold threshold) (phaseDelta humanPhase gnosisPhase))) := by
  refine ⟨breaking_point tolerance, minmax_ge_maxmin d₀ d₁ a₀ a₁, ?_, ?_⟩
  · exact ⟨interior_has_positive_grit b n hn, edge_has_zero_grit b,
      upper_edge_has_zero_grit b⟩
  · refine ⟨phaseDelta_le_six humanPhase gnosisPhase, ?_⟩
    intro h
    exact crashes_when_delta_exceeds_threshold threshold humanPhase gnosisPhase h

end Gnosis.Body.Robustness
