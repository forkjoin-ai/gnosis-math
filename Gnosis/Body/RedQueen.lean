import Init

/-!
# The Red Queen — Adversarial Co-Evolution and Predator–Prey Oscillation

"Now, here, you see, it takes all the running you can do, to keep in the same
place." The Metaverse (the 3D Game-of-Life evolutionary world in `aeon-corpus`)
runs predators against prey. Each adaptation by one side erodes the advantage of
the other; the arms race never settles into a static optimum. The dynamical
signature of this is **oscillation**: predator and prey populations rise and
fall in antiphase, a period-2 cycle that no fixed point can absorb.

`Gnosis/Evolution.lean` already exhibits a period-2 oscillation of *forces*
(`evolution_period_two : p.flip.flip = p`) — selection vs mutation. This module
exhibits a period-2 oscillation of *states* (a real 2-cycle, not just an
involution on a configuration), and adds the three pillars that make it the Red
Queen rather than a mere clock:

1. **A genuine period-2 orbit** (`has_period_two_orbit`): an explicit state with
   `step s₀ ≠ s₀` but `step (step s₀) = s₀` — oscillation provably exists — plus
   `period_exactly_two`: the cycle never settles, `step (step (step s₀)) = step s₀`.
2. **Adversarial co-evolution is zero-sum** (`coevolution_is_zero_sum`): prey and
   predator fitness are antiparallel; their sum is conserved. One's gain is the
   other's loss — neither can rest (the Red Queen).
3. **Maxmin robustness / weak duality** (`maxmin_le_minmax`): what the prey can
   guarantee never exceeds what the predator can hold it to.
4. **Grit as the push-to-extinction point** (`prey_survives_iff_within_grit`,
   `predator_wins_beyond_grit`, `over_push_is_pyrrhic`): prey survives iff
   predator pressure is within prey grit; pushing past grit drives prey to 0 —
   and the predator's food to 0 with it. The arms race has a cliff.

Finally `red_queen_principle` synthesizes: co-evolution oscillates (period 2),
is zero-sum, and its sustainable equilibrium is the maxmin value, bounded by grit.

Rustic Church: `Init` only (no Mathlib). `Nat` arithmetic, `Int` only where
signed values are genuine. No `sorry`; no `simp`/`decide`/`omega` on open goals.
-/

namespace Gnosis.Body.RedQueen

/-! ## 1. A genuine period-2 orbit (oscillation provably exists) -/

/-- The phase of the predator–prey cycle: which side is currently ascendant. A
    two-state dial — the smallest carrier of a real oscillation. -/
inductive Phase where
  | predatorHigh   -- predators numerous, prey crashing
  | preyHigh       -- prey recovered, predators starving
  deriving DecidableEq, Repr

/-- The deterministic predator–prey map. When predators are high they overconsume
    and crash the prey, flipping the system toward `preyHigh`; with abundant prey
    and few predators, predators rebound, flipping back. The map has **no fixed
    point** — every phase is sent to the other. -/
def step : Phase → Phase
  | .predatorHigh => .preyHigh
  | .preyHigh     => .predatorHigh

/-- The starting state of our explicit orbit. -/
def s₀ : Phase := Phase.predatorHigh

/-- `step` is an involution: two applications return to the start. This is the
    period-2 identity for *states* (compare `Evolution.evolution_period_two`,
    the period-2 identity for *forces*). -/
theorem step_step (p : Phase) : step (step p) = p := by
  cases p <;> rfl

/-- The two phases are genuinely distinct — there is something to oscillate
    between. -/
theorem phases_distinct : Phase.predatorHigh ≠ Phase.preyHigh := by
  intro h
  exact Phase.noConfusion h

/-- One step actually moves the state: `s₀` is not a fixed point. Together with
    `step (step s₀) = s₀` this is what makes the orbit a *real* 2-cycle rather
    than a stationary point. -/
theorem step_moves : step s₀ ≠ s₀ := by
  intro h
  -- step s₀ = preyHigh, so h : preyHigh = predatorHigh
  exact phases_distinct h.symm

/-- **A period-2 orbit exists.** There is a state that moves under one step
    (`step s₀ ≠ s₀`) yet returns under two (`step (step s₀) = s₀`): a genuine
    2-cycle. This is the formal answer to "can predator–prey oscillation exist?"
    — yes, provably. -/
theorem has_period_two_orbit : step s₀ ≠ s₀ ∧ step (step s₀) = s₀ :=
  ⟨step_moves, step_step s₀⟩

/-- **Period exactly two: the cycle never settles.** Three steps land where one
    step did (`step³ s₀ = step s₀`), reusing the period-2 identity. The orbit
    cannot decay into a fixed point — it keeps running to stay in place. -/
theorem period_exactly_two : step (step (step s₀)) = step s₀ :=
  step_step (step s₀)

/-! ## 2. Adversarial co-evolution is zero-sum (the Red Queen) -/

/-- Total stake in the arms race: the fixed pool of advantage the two sides
    contest (signed, since advantages can swing either way). -/
def totalStake : Int := 100

/-- **Prey fitness** rises with prey defense and falls with predator pressure. -/
def preyFitness (defense pressure : Int) : Int :=
  defense - pressure

/-- **Predator fitness** is the mirror image: it claims whatever of the fixed
    stake the prey does not. It rises with predator pressure and falls with prey
    defense — exactly opposite to `preyFitness`. -/
def predatorFitness (defense pressure : Int) : Int :=
  totalStake - (defense - pressure)

/-- **Co-evolution is zero-sum.** Prey and predator fitness always sum to the
    fixed total stake: every unit the prey gains in defense is a unit the
    predator loses, and vice versa. Neither side can improve except at the
    other's expense — the Red Queen condition that forbids rest. -/
theorem coevolution_is_zero_sum (defense pressure : Int) :
    preyFitness defense pressure + predatorFitness defense pressure = totalStake := by
  unfold preyFitness predatorFitness
  -- (defense - pressure) + (totalStake - (defense - pressure)) = totalStake
  -- Let x = defense - pressure. Goal: x + (totalStake - x) = totalStake.
  generalize hx : defense - pressure = x
  -- x + (totalStake - x) = totalStake  ⇐  add_comm then add_sub_cancel
  rw [Int.add_comm x (totalStake - x)]
  exact Int.sub_add_cancel totalStake x

/-- **Antiparallel coupling.** Increasing prey defense by `δ` lowers predator
    fitness by exactly `δ` — the gain of one is the loss of the other, made
    quantitative. -/
theorem prey_gain_is_predator_loss (defense pressure δ : Int) :
    predatorFitness (defense + δ) pressure
      = predatorFitness defense pressure - δ := by
  unfold predatorFitness
  -- totalStake - ((defense+δ) - pressure) = (totalStake - (defense-pressure)) - δ
  -- Inner rearrangement: (defense+δ) - pressure = (defense-pressure) + δ.
  have hinner : defense + δ - pressure = defense - pressure + δ := by
    rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg]
    exact Int.add_right_comm defense δ (-pressure)
  rw [hinner, Int.sub_sub totalStake (defense - pressure) δ]

/-! ## 3. Maxmin robustness — weak duality for the 2×2 arms-race game -/

/-- The prey's survival payoff against a predator: defense net of pressure,
    truncated at 0 (once overwhelmed, survival is simply none). `Nat` here: a
    payoff floored at zero. -/
def gamePayoff (defense pressure : Nat) : Nat := defense - pressure

/-- **Max-min** for the 2×2 game: for each of two prey defenses, take the worst
    case over the predator's two pressures (inner `min`), then the best such
    guarantee (outer `max`). What the prey can secure regardless of the predator. -/
def maxmin (d₀ d₁ a₀ a₁ : Nat) : Nat :=
  Nat.max (Nat.min (gamePayoff d₀ a₀) (gamePayoff d₀ a₁))
          (Nat.min (gamePayoff d₁ a₀) (gamePayoff d₁ a₁))

/-- **Min-max** for the same game: for each predator pressure take the prey's
    best response (inner `max`), then the worst of those for the prey (outer
    `min`). What the predator can hold the prey to. -/
def minmax (d₀ d₁ a₀ a₁ : Nat) : Nat :=
  Nat.min (Nat.max (gamePayoff d₀ a₀) (gamePayoff d₁ a₀))
          (Nat.max (gamePayoff d₀ a₁) (gamePayoff d₁ a₁))

/-- **Weak duality: max-min ≤ min-max.** What the prey can *guarantee* never
    exceeds what the predator can *hold it to*. The structural backbone of
    adversarial robustness, proved from pure `Nat.min`/`Nat.max` lemmas. -/
theorem maxmin_le_minmax (d₀ d₁ a₀ a₁ : Nat) :
    maxmin d₀ d₁ a₀ a₁ ≤ minmax d₀ d₁ a₀ a₁ := by
  unfold maxmin minmax
  -- Name the four matrix entries; the rest is pure lattice algebra.
  generalize gamePayoff d₀ a₀ = p00
  generalize gamePayoff d₀ a₁ = p01
  generalize gamePayoff d₁ a₀ = p10
  generalize gamePayoff d₁ a₁ = p11
  apply Nat.max_le.mpr
  refine ⟨?_, ?_⟩
  · apply Nat.le_min.mpr
    refine ⟨?_, ?_⟩
    · exact Nat.le_trans (Nat.min_le_left p00 p01) (Nat.le_max_left p00 p10)
    · exact Nat.le_trans (Nat.min_le_right p00 p01) (Nat.le_max_left p01 p11)
  · apply Nat.le_min.mpr
    refine ⟨?_, ?_⟩
    · exact Nat.le_trans (Nat.min_le_left p10 p11) (Nat.le_max_right p00 p10)
    · exact Nat.le_trans (Nat.min_le_right p10 p11) (Nat.le_max_right p01 p11)

/-! ## 4. Grit as the push-to-extinction point -/

/-- The prey's grit: the maximal predator pressure it can absorb before
    extinction. -/
def preyGrit : Nat → Nat := fun g => g

/-- Prey survives predator pressure `p` iff `p` is within its grit. -/
def survives (grit p : Nat) : Prop := p ≤ grit

/-- **Prey survives iff within grit.** Survival is exactly the within-grit
    condition — a definitional but load-bearing characterization that the next
    theorems negate. -/
theorem prey_survives_iff_within_grit (grit p : Nat) :
    survives grit p ↔ p ≤ grit := Iff.rfl

/-- **The predator wins beyond grit.** If predator pressure strictly exceeds prey
    grit, the prey does not survive — the extinction cliff. -/
theorem predator_wins_beyond_grit (grit p : Nat) (h : grit < p) :
    ¬ survives grit p := by
  unfold survives
  intro hle
  -- h : grit < p and hle : p ≤ grit ⟹ grit < grit, contradiction
  exact Nat.lt_irrefl grit (Nat.lt_of_lt_of_le h hle)

/-- The surviving prey population under pressure `p`: the grit margin if within
    grit, else 0 (extinction). Truncated `Nat.sub` gives extinction for free
    once pressure passes grit. -/
def preyPopulation (grit p : Nat) : Nat := grit - p

/-- Beyond grit, the prey population is exactly 0 — extinction. -/
theorem prey_extinct_beyond_grit (grit p : Nat) (h : grit < p) :
    preyPopulation grit p = 0 := by
  unfold preyPopulation
  exact Nat.sub_eq_zero_of_le (Nat.le_of_lt h)

/-- The predator's food supply is the surviving prey population. No prey, no
    food. -/
def predatorFood (grit p : Nat) : Nat := preyPopulation grit p

/-- **Over-pushing is pyrrhic.** If the predator pushes pressure past prey grit,
    the prey hits 0 — and so the predator's own food supply hits 0. The arms race
    cannot be "won" by unbounded escalation: maximal predation is self-defeating,
    the predator starves on the corpses. This is why pressure must stay within
    grit, and why the equilibrium oscillates rather than running to the extreme. -/
theorem over_push_is_pyrrhic (grit p : Nat) (h : grit < p) :
    predatorFood grit p = 0 := by
  unfold predatorFood
  exact prey_extinct_beyond_grit grit p h

/-- Conversely, within grit the predator's food is positive whenever there is any
    grit margin — the sustainable regime where both sides persist. -/
theorem sustainable_within_grit (grit p : Nat) (h : p < grit) :
    0 < predatorFood grit p := by
  unfold predatorFood preyPopulation
  exact Nat.zero_lt_sub_of_lt h

/-! ## 5. The Red Queen principle (synthesis) -/

/-- **The Red Queen principle.** Adversarial co-evolution exhibits, all at once:

    1. **Oscillation** — a genuine period-2 orbit exists (`step s₀ ≠ s₀`,
       `step (step s₀) = s₀`) and never settles (`step³ s₀ = step s₀`);
    2. **Zero-sum coupling** — prey and predator fitness sum to the fixed stake,
       so neither can rest without costing the other (the Red Queen);
    3. **Bounded sustainable equilibrium** — the prey's guaranteed value
       (`maxmin`) never exceeds what the predator can enforce (`minmax`), and the
       whole regime is bounded by grit: push pressure past grit and the
       predator's own food collapses to 0 (`over_push_is_pyrrhic`).

    Running to stay in place: oscillating, zero-sum, and capped by grit. -/
theorem red_queen_principle
    (defense pressure : Int) (d₀ d₁ a₀ a₁ grit p : Nat) (hp : grit < p) :
    -- 1. Oscillation: a real 2-cycle that never settles.
    (step s₀ ≠ s₀ ∧ step (step s₀) = s₀ ∧ step (step (step s₀)) = step s₀) ∧
    -- 2. Zero-sum co-evolution.
    (preyFitness defense pressure + predatorFitness defense pressure = totalStake) ∧
    -- 3a. Maxmin robustness (weak duality).
    (maxmin d₀ d₁ a₀ a₁ ≤ minmax d₀ d₁ a₀ a₁) ∧
    -- 3b. Grit is the cliff: over-pushing starves the predator.
    (predatorFood grit p = 0) := by
  refine ⟨⟨step_moves, step_step s₀, period_exactly_two⟩, ?_, ?_, ?_⟩
  · exact coevolution_is_zero_sum defense pressure
  · exact maxmin_le_minmax d₀ d₁ a₀ a₁
  · exact over_push_is_pyrrhic grit p hp

end Gnosis.Body.RedQueen
