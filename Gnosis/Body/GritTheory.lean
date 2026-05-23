import Init
import Gnosis.Body.Anthropogenesis
import Gnosis.Body.Robustness
import Gnosis.Body.SapolskyStress
import Gnosis.Body.RedQueen
import Gnosis.Body.SelfDefense
import Gnosis.Body.WarMakesPeace
import Gnosis.Body.AmnesiaGritFrontier
import Gnosis.Body.DiversityIsOptimal
import Gnosis.Body.Neurodiversity
import Gnosis.Body.DepressionAsCollapsedCycle
import Gnosis.Body.Vampire

/-!
# Grit Theory — the Capstone Synthesis

**The through-line of the whole arc, in one sentence:** a living system survives
at the productive edge between too-little and too-much; anxiety is the signal
that keeps it there; **life had to be**.

Every module in the grit-theory arc is a different camera trained on that same
sentence. This capstone imports them all and bundles their headline results into
a single proved conjunction (`grit_theory_synthesis`), so the through-line is not
a slogan but a checked theorem whose proof *depends on* each module's real work.

The cameras, and the headline each contributes:

* **`Anthropogenesis`** — *life had to be* (`life_had_to_be`): in any world with
  positive carrying capacity a viable population exists and, under selection,
  strictly beats extinction. Plus *stress produces culture*
  (`stress_produces_culture`), *comfort is cultural death*
  (`comfort_is_cultural_death`), and *life happens on the edges*
  (`life_happens_on_the_edges`): the band's edges survive but sit one
  perturbation from death — the productive edge made literal.
* **`Robustness`** — grit is the maximum withstood perturbation
  (`grit_is_max_withstood`) and adversarial weak duality `maxmin ≤ minmax`
  (`minmax_ge_maxmin`): what a system can guarantee never exceeds what the
  adversary can hold it to.
* **`SapolskyStress`** — the inverted-U dose-response (`inverted_u`), acute
  withstands but chronic breaks (`acute_withstands_chronic_breaks`), and the
  clinamen swerve as the sole freedom (`swerve_is_the_only_freedom`): *the dose
  makes the poison*.
* **`RedQueen`** — a real period-2 orbit exists (`has_period_two_orbit`) and
  over-pushing is pyrrhic (`over_push_is_pyrrhic`): the arms race oscillates and
  cannot be won by unbounded escalation.
* **`SelfDefense`** — *adversaries improve you* (`adversaries_improve`): the
  enemy outside makes you grittier.
* **`WarMakesPeace`** — *war makes peace* (`war_makes_peace`): a graver threat
  grows the peacemaking set — deterrence.
* **`AmnesiaGritFrontier`** — amnesia is idempotent (`amnesia_is_idempotent`)
  and grit/amnesia trade on a genuine Pareto frontier
  (`amnesia_grit_is_a_frontier`): robustness lives at the interior edge between
  settled memory and open exploration.
* **`DiversityIsOptimal`** — diversity is the maxmin-robust strategy under
  uncertainty (`diversity_is_maxmin_optimal`).
* **`Neurodiversity`** — comparative advantage preserves diversity
  (`comparative_advantage_preserves_diversity`): no maintained neurotype is
  dominated; none is to be othered.
* **`DepressionAsCollapsedCycle`** — drive revives amplitude
  (`drive_revives_amplitude`): the collapsed cycle is escapable.
* **`Vampire`** — total drain is pyrrhic (`total_drain_is_pyrrhic`): the
  parasite that kills the host starves.

Read together: each system lives at a sharp edge (grit, the band, the inverted-U
peak, the Pareto frontier, the regeneration wall, the crash threshold); too
little forfeits the good (comfort is cultural death, pure amnesia banks nothing,
the flat fixed point); too much breaks the system (chronic load, over-push,
total drain, the brittle monoculture); anxiety / stress is the signal that keeps
the system at the productive edge (stress produces culture, the inverted-U,
drive revives the cycle); and the whole thing was not chosen but forced, because
non-life scores zero — **life had to be**.

## Style

`import Init` plus the eleven Init-clean sibling Body modules. No Mathlib,
`Nat`/`Int` only, no `sorry`, no `simp`/`decide`/`omega` on open goals. The
proofs are pure composition: `⟨…⟩`, `And.intro`, and direct references to the
imported theorems by their fully-qualified names. Several modules export
colliding `maxmin`/`minmax`/`payoff`; this module does **not** blanket-`open`
anything — every reference is fully qualified — so there is no ambiguity.
-/

namespace Gnosis.Body.GritTheory

/-! ## Capstone re-exports

Each `capstone_*` theorem restates one module's headline and proves it by direct
reference to the real theorem in that module. They take the same parameters /
hypotheses the source theorem takes, instantiated with concrete witnesses where a
clean witness exists. These are the load-bearing dependencies of the grand
synthesis below. -/

/-- **Life had to be** (`Anthropogenesis.life_had_to_be`). In any world with
    positive dark-matter capacity a viable, non-empty population exists, and under
    selection on world fitness it strictly beats extinction. The sweet spot is not
    chosen; it is forced, because non-life scores zero. -/
theorem capstone_life_had_to_be (dark : Gnosis.Body.Anthropogenesis.DarkCapacity)
    (h : 0 < dark.capacity) :
    (∃ visible, 0 < visible ∧ visible ≤ dark.capacity) ∧
    (∀ sustained, 0 < sustained →
      Gnosis.Body.Anthropogenesis.select Gnosis.Body.Anthropogenesis.extinctFitness
          (Gnosis.Body.Anthropogenesis.sustainingFitness sustained)
        = Gnosis.Body.Anthropogenesis.sustainingFitness sustained) :=
  Gnosis.Body.Anthropogenesis.life_had_to_be dark h

/-- **Stress produces culture** (`Anthropogenesis.stress_produces_culture`):
    a stressed population converts its stress into shared culture. -/
theorem capstone_stress_produces_culture (stress : Nat) (h : 0 < stress) :
    0 < Gnosis.Body.Anthropogenesis.stressToCulture stress :=
  Gnosis.Body.Anthropogenesis.stress_produces_culture stress h

/-- **Comfort is cultural death** (`Anthropogenesis.comfort_is_cultural_death`):
    with no stress, no culture is generated. -/
theorem capstone_comfort_is_cultural_death :
    Gnosis.Body.Anthropogenesis.stressToCulture 0 = 0 :=
  Gnosis.Body.Anthropogenesis.comfort_is_cultural_death

/-- **Life happens on the edges** (`Anthropogenesis.life_happens_on_the_edges`):
    the band's two edges survive yet sit one perturbation from death — the
    productive edge between isolation and overcrowding. -/
theorem capstone_life_happens_on_the_edges
    (b : Gnosis.Body.Anthropogenesis.SurvivalBand)
    (hw : b.lo ≤ b.hi) (hlo : 0 < b.lo) :
    (Gnosis.Body.Anthropogenesis.survives b b.lo ∧
      Gnosis.Body.Anthropogenesis.diesUnderpopulation b (b.lo - 1)) ∧
    (Gnosis.Body.Anthropogenesis.survives b b.hi ∧
      Gnosis.Body.Anthropogenesis.diesOvercrowding b (b.hi + 1)) :=
  Gnosis.Body.Anthropogenesis.life_happens_on_the_edges b hw hlo

/-- **Grit is the maximum withstood perturbation**
    (`Robustness.grit_is_max_withstood`): everything up to grit is survived; the
    very next unit breaks. -/
theorem capstone_grit_is_max_withstood (tolerance perturbation : Nat) :
    (perturbation ≤ Gnosis.Body.Robustness.grit tolerance →
      Gnosis.Body.Robustness.withstands tolerance perturbation)
      ∧ Gnosis.Body.Robustness.breaks tolerance
          (Gnosis.Body.Robustness.grit tolerance + 1) :=
  Gnosis.Body.Robustness.grit_is_max_withstood tolerance perturbation

/-- **Adversarial weak duality** (`Robustness.minmax_ge_maxmin`): what a system
    can guarantee never exceeds what the adversary can hold it to. -/
theorem capstone_minmax_ge_maxmin (d₀ d₁ a₀ a₁ : Nat) :
    Gnosis.Body.Robustness.maxmin d₀ d₁ a₀ a₁
      ≤ Gnosis.Body.Robustness.minmax d₀ d₁ a₀ a₁ :=
  Gnosis.Body.Robustness.minmax_ge_maxmin d₀ d₁ a₀ a₁

/-- **The inverted-U** (`SapolskyStress.inverted_u`): there is a peak below which
    stress strictly helps and above which it strictly hurts, with both extremes
    zero — the dose makes the poison. -/
theorem capstone_inverted_u (capacity : Nat) :
    ∃ p : Nat,
      p = capacity / 2 ∧
      (∀ s, 2 * s + 2 ≤ capacity →
        Gnosis.Body.SapolskyStress.performance s capacity
          < Gnosis.Body.SapolskyStress.performance (s + 1) capacity) ∧
      (∀ s, capacity ≤ 2 * s → s + 1 ≤ capacity →
        Gnosis.Body.SapolskyStress.performance (s + 1) capacity
          < Gnosis.Body.SapolskyStress.performance s capacity) ∧
      (Gnosis.Body.SapolskyStress.performance 0 capacity = 0 ∧
        Gnosis.Body.SapolskyStress.performance capacity capacity = 0) :=
  Gnosis.Body.SapolskyStress.inverted_u capacity

/-- **Acute withstands, chronic breaks**
    (`SapolskyStress.acute_withstands_chronic_breaks`): the same nonzero stressor
    that the body withstands at rest will, sustained long enough, break it. -/
theorem capstone_acute_withstands_chronic_breaks (perTick tolerance : Nat)
    (hp : 0 < perTick) :
    Gnosis.Body.Robustness.withstands tolerance
        (Gnosis.Body.SapolskyStress.allostaticLoad perTick 0) ∧
    Gnosis.Body.Robustness.breaks tolerance
        (Gnosis.Body.SapolskyStress.allostaticLoad perTick (tolerance + 1)) :=
  Gnosis.Body.SapolskyStress.acute_withstands_chronic_breaks perTick tolerance hp

/-- **The swerve is the only freedom**
    (`SapolskyStress.swerve_is_the_only_freedom`): behavior is determined; the
    clinamen `+1` is the sole departure. -/
theorem capstone_swerve_is_the_only_freedom (state : Nat) :
    Gnosis.Body.SapolskyStress.swerve state
      ≠ Gnosis.Body.SapolskyStress.behavior state :=
  Gnosis.Body.SapolskyStress.swerve_is_the_only_freedom state

/-- **A period-2 orbit exists** (`RedQueen.has_period_two_orbit`): a real
    oscillation that moves under one step and returns under two. -/
theorem capstone_has_period_two_orbit :
    Gnosis.Body.RedQueen.step Gnosis.Body.RedQueen.s₀ ≠ Gnosis.Body.RedQueen.s₀ ∧
    Gnosis.Body.RedQueen.step (Gnosis.Body.RedQueen.step Gnosis.Body.RedQueen.s₀)
      = Gnosis.Body.RedQueen.s₀ :=
  Gnosis.Body.RedQueen.has_period_two_orbit

/-- **Over-push is pyrrhic** (`RedQueen.over_push_is_pyrrhic`): pushing predator
    pressure past prey grit starves the predator on the corpses. -/
theorem capstone_over_push_is_pyrrhic (grit p : Nat) (h : grit < p) :
    Gnosis.Body.RedQueen.predatorFood grit p = 0 :=
  Gnosis.Body.RedQueen.over_push_is_pyrrhic grit p h

/-- **Adversaries improve you** (`SelfDefense.adversaries_improve`): a defender
    trained against attacks dodges at least everything the untrained one did. -/
theorem capstone_adversaries_improve (r n w : Nat)
    (hd : Gnosis.Body.SelfDefense.dodges r w) :
    Gnosis.Body.SelfDefense.dodges (Gnosis.Body.SelfDefense.trainedReaction r n) w :=
  Gnosis.Body.SelfDefense.adversaries_improve r n w hd

/-- **War makes peace** (`WarMakesPeace.war_makes_peace`): under a graver threat,
    any deal that held the peace before still holds — the acceptable set grows. -/
theorem capstone_war_makes_peace (deal base warCost v1 v2 : Nat) (h : v1 ≤ v2)
    (hpeace : Gnosis.Body.WarMakesPeace.peacemaking deal base v1 warCost) :
    Gnosis.Body.WarMakesPeace.peacemaking deal base v2 warCost :=
  Gnosis.Body.WarMakesPeace.war_makes_peace deal base warCost v1 v2 h hpeace

/-- **Amnesia is idempotent** (`AmnesiaGritFrontier.amnesia_is_idempotent`):
    forgetting twice is forgetting once — the reset to the void is an idempotent. -/
theorem capstone_amnesia_is_idempotent (m : Nat) :
    Gnosis.Body.AmnesiaGritFrontier.amnesia
        (Gnosis.Body.AmnesiaGritFrontier.amnesia m)
      = Gnosis.Body.AmnesiaGritFrontier.amnesia m :=
  Gnosis.Body.AmnesiaGritFrontier.amnesia_is_idempotent m

/-- **Amnesia/grit is a frontier** (`AmnesiaGritFrontier.amnesia_grit_is_a_frontier`):
    along the retention axis, accumulation cannot rise without adaptability
    strictly falling — a genuine Pareto frontier, not a free lunch. -/
theorem capstone_amnesia_grit_is_a_frontier (m r1 r2 scale : Nat)
    (hlt : r1 < r2) (hle : r2 ≤ scale) :
    Gnosis.Body.AmnesiaGritFrontier.accumulationValue
        (Gnosis.Body.AmnesiaGritFrontier.retain m r1 scale)
      ≤ Gnosis.Body.AmnesiaGritFrontier.accumulationValue
          (Gnosis.Body.AmnesiaGritFrontier.retain m r2 scale) ∧
    Gnosis.Body.AmnesiaGritFrontier.adaptability r2 scale
      < Gnosis.Body.AmnesiaGritFrontier.adaptability r1 scale :=
  Gnosis.Body.AmnesiaGritFrontier.amnesia_grit_is_a_frontier m r1 r2 scale hlt hle

/-- **Diversity is maxmin-optimal** (`DiversityIsOptimal.diversity_is_maxmin_optimal`):
    under uncertainty the diverse strategy's worst case strictly beats the
    monoculture's, while under certainty the specialist can win — a frontier. -/
theorem capstone_diversity_is_maxmin_optimal
    (payoff : Gnosis.Body.DiversityIsOptimal.Strategy →
      Gnosis.Body.DiversityIsOptimal.Env → Nat)
    (hexposed : payoff Gnosis.Body.DiversityIsOptimal.Strategy.monoculture
        Gnosis.Body.DiversityIsOptimal.Env.shifted = 0)
    (hm : 0 < payoff Gnosis.Body.DiversityIsOptimal.Strategy.diverse
        Gnosis.Body.DiversityIsOptimal.Env.matched)
    (hs : 0 < payoff Gnosis.Body.DiversityIsOptimal.Strategy.diverse
        Gnosis.Body.DiversityIsOptimal.Env.shifted)
    (hn : 0 < payoff Gnosis.Body.DiversityIsOptimal.Strategy.diverse
        Gnosis.Body.DiversityIsOptimal.Env.novel)
    (hcertain : payoff Gnosis.Body.DiversityIsOptimal.Strategy.diverse
          Gnosis.Body.DiversityIsOptimal.Env.matched
        < payoff Gnosis.Body.DiversityIsOptimal.Strategy.monoculture
          Gnosis.Body.DiversityIsOptimal.Env.matched) :
    Gnosis.Body.DiversityIsOptimal.worstCase payoff
        Gnosis.Body.DiversityIsOptimal.Strategy.monoculture = 0 ∧
    0 < Gnosis.Body.DiversityIsOptimal.worstCase payoff
        Gnosis.Body.DiversityIsOptimal.Strategy.diverse ∧
    Gnosis.Body.DiversityIsOptimal.worstCase payoff
        Gnosis.Body.DiversityIsOptimal.Strategy.monoculture
      < Gnosis.Body.DiversityIsOptimal.worstCase payoff
        Gnosis.Body.DiversityIsOptimal.Strategy.diverse ∧
    payoff Gnosis.Body.DiversityIsOptimal.Strategy.diverse
        Gnosis.Body.DiversityIsOptimal.Env.matched
      < payoff Gnosis.Body.DiversityIsOptimal.Strategy.monoculture
        Gnosis.Body.DiversityIsOptimal.Env.matched :=
  Gnosis.Body.DiversityIsOptimal.diversity_is_maxmin_optimal payoff hexposed hm hs hn hcertain

/-- **Comparative advantage preserves diversity**
    (`Neurodiversity.comparative_advantage_preserves_diversity`): if every
    neurotype beats every other somewhere, none is dominated — the spread is
    stable, none to be othered. -/
theorem capstone_comparative_advantage_preserves_diversity
    (fitness : Gnosis.Body.Neurodiversity.NeuroType →
      Gnosis.Body.Neurodiversity.Niche → Nat)
    (hadv : ∀ t t', t ≠ t' → Gnosis.Body.Neurodiversity.hasAdvantage fitness t t') :
    ∀ t t', t ≠ t' → ¬ Gnosis.Body.Neurodiversity.dominated fitness t t' :=
  Gnosis.Body.Neurodiversity.comparative_advantage_preserves_diversity fitness hadv

/-- **Drive revives amplitude** (`DepressionAsCollapsedCycle.drive_revives_amplitude`):
    any positive restoring drive strictly increases the amplitude of the
    oscillation — the collapsed cycle is escapable. -/
theorem capstone_drive_revives_amplitude {amplitude drive : Nat}
    (hDrive : 0 < drive) :
    amplitude < Gnosis.Body.DepressionAsCollapsedCycle.driveStep amplitude drive :=
  Gnosis.Body.DepressionAsCollapsedCycle.drive_revives_amplitude hDrive

/-- **Total drain is pyrrhic** (`Vampire.total_drain_is_pyrrhic`): a vampire load
    that empties the commons leaves nothing to feed on — the parasite that kills
    the host starves. -/
theorem capstone_total_drain_is_pyrrhic (regen n drain : Nat)
    (h : Gnosis.Body.Vampire.collapsing regen n drain) :
    Gnosis.Body.Vampire.vampireFood regen n drain = 0 :=
  Gnosis.Body.Vampire.total_drain_is_pyrrhic regen n drain h

/-! ## The grand synthesis

One theorem bundling all eleven modules' headlines into a single proved
conjunction. The hypotheses are exactly those the source theorems require —
gathered once at the top — and the proof is pure composition: each conjunct is a
direct reference to the corresponding `capstone_*` re-export above (and hence to
the real module theorem it cites). It genuinely typechecks against the real
signatures, so the compiled artifact demonstrably depends on every module in the
arc. -/

/-- **GRIT THEORY — THE SYNTHESIS.** The through-line of the whole arc, proved as
    one conjunction over all eleven grit-theory modules:

    *A living system survives at the productive edge between too-little and
    too-much; anxiety is the signal that keeps it there; life had to be.*

    Each conjunct is a module's headline, cited by its real qualified name:

    1. `Anthropogenesis.life_had_to_be` — life is forced, not chosen;
    2. `Anthropogenesis.stress_produces_culture` — anxiety builds culture;
    3. `Anthropogenesis.comfort_is_cultural_death` — too little forfeits the good;
    4. `Anthropogenesis.life_happens_on_the_edges` — survival sits at the edge;
    5. `Robustness.grit_is_max_withstood` — grit is the sharp breaking point;
    6. `Robustness.minmax_ge_maxmin` — adversarial weak duality;
    7. `SapolskyStress.inverted_u` — the dose makes the poison;
    8. `SapolskyStress.acute_withstands_chronic_breaks` — too much breaks;
    9. `SapolskyStress.swerve_is_the_only_freedom` — the clinamen is the sole freedom;
    10. `RedQueen.has_period_two_orbit` — the cycle oscillates;
    11. `RedQueen.over_push_is_pyrrhic` — over-escalation is self-defeating;
    12. `SelfDefense.adversaries_improve` — the enemy makes you grittier;
    13. `WarMakesPeace.war_makes_peace` — the threat manufactures peace;
    14. `AmnesiaGritFrontier.amnesia_is_idempotent` — forgetting is an idempotent reset;
    15. `AmnesiaGritFrontier.amnesia_grit_is_a_frontier` — robustness at the interior edge;
    16. `DiversityIsOptimal.diversity_is_maxmin_optimal` — diversity is robust-optimal;
    17. `Neurodiversity.comparative_advantage_preserves_diversity` — none dominated;
    18. `DepressionAsCollapsedCycle.drive_revives_amplitude` — the collapse is escapable;
    19. `Vampire.total_drain_is_pyrrhic` — the parasite that kills the host starves.

    Proof: pure composition — `⟨…⟩` over the `capstone_*` re-exports. -/
theorem grit_theory_synthesis
    -- Anthropogenesis: world, band
    (dark : Gnosis.Body.Anthropogenesis.DarkCapacity) (hdark : 0 < dark.capacity)
    (stress : Nat) (hstress : 0 < stress)
    (b : Gnosis.Body.Anthropogenesis.SurvivalBand) (hw : b.lo ≤ b.hi) (hlo : 0 < b.lo)
    -- Robustness
    (tolerance perturbation : Nat)
    (d₀ d₁ a₀ a₁ : Nat)
    -- SapolskyStress
    (capacity : Nat)
    (perTick : Nat) (hperTick : 0 < perTick)
    (state : Nat)
    -- RedQueen
    (grit p : Nat) (hpush : grit < p)
    -- SelfDefense
    (r n w : Nat) (hdodge : Gnosis.Body.SelfDefense.dodges r w)
    -- WarMakesPeace
    (deal base warCost v1 v2 : Nat) (hv : v1 ≤ v2)
    (hpeace : Gnosis.Body.WarMakesPeace.peacemaking deal base v1 warCost)
    -- AmnesiaGritFrontier
    (m r1 r2 scale : Nat) (hr12 : r1 < r2) (hr2 : r2 ≤ scale)
    -- DiversityIsOptimal
    (payoff : Gnosis.Body.DiversityIsOptimal.Strategy →
      Gnosis.Body.DiversityIsOptimal.Env → Nat)
    (hexposed : payoff Gnosis.Body.DiversityIsOptimal.Strategy.monoculture
        Gnosis.Body.DiversityIsOptimal.Env.shifted = 0)
    (hdm : 0 < payoff Gnosis.Body.DiversityIsOptimal.Strategy.diverse
        Gnosis.Body.DiversityIsOptimal.Env.matched)
    (hds : 0 < payoff Gnosis.Body.DiversityIsOptimal.Strategy.diverse
        Gnosis.Body.DiversityIsOptimal.Env.shifted)
    (hdn : 0 < payoff Gnosis.Body.DiversityIsOptimal.Strategy.diverse
        Gnosis.Body.DiversityIsOptimal.Env.novel)
    (hcertain : payoff Gnosis.Body.DiversityIsOptimal.Strategy.diverse
          Gnosis.Body.DiversityIsOptimal.Env.matched
        < payoff Gnosis.Body.DiversityIsOptimal.Strategy.monoculture
          Gnosis.Body.DiversityIsOptimal.Env.matched)
    -- Neurodiversity
    (fitness : Gnosis.Body.Neurodiversity.NeuroType →
      Gnosis.Body.Neurodiversity.Niche → Nat)
    (hadv : ∀ t t', t ≠ t' → Gnosis.Body.Neurodiversity.hasAdvantage fitness t t')
    -- DepressionAsCollapsedCycle
    (amplitude drive : Nat) (hDrive : 0 < drive)
    -- Vampire
    (vRegen vN vDrain : Nat)
    (hCollapse : Gnosis.Body.Vampire.collapsing vRegen vN vDrain) :
    -- 1. Anthropogenesis: life had to be.
    ((∃ visible, 0 < visible ∧ visible ≤ dark.capacity) ∧
      (∀ sustained, 0 < sustained →
        Gnosis.Body.Anthropogenesis.select Gnosis.Body.Anthropogenesis.extinctFitness
            (Gnosis.Body.Anthropogenesis.sustainingFitness sustained)
          = Gnosis.Body.Anthropogenesis.sustainingFitness sustained)) ∧
    -- 2. Anthropogenesis: stress produces culture.
    (0 < Gnosis.Body.Anthropogenesis.stressToCulture stress) ∧
    -- 3. Anthropogenesis: comfort is cultural death.
    (Gnosis.Body.Anthropogenesis.stressToCulture 0 = 0) ∧
    -- 4. Anthropogenesis: life happens on the edges.
    ((Gnosis.Body.Anthropogenesis.survives b b.lo ∧
        Gnosis.Body.Anthropogenesis.diesUnderpopulation b (b.lo - 1)) ∧
      (Gnosis.Body.Anthropogenesis.survives b b.hi ∧
        Gnosis.Body.Anthropogenesis.diesOvercrowding b (b.hi + 1))) ∧
    -- 5. Robustness: grit is the maximum withstood perturbation.
    ((perturbation ≤ Gnosis.Body.Robustness.grit tolerance →
        Gnosis.Body.Robustness.withstands tolerance perturbation)
      ∧ Gnosis.Body.Robustness.breaks tolerance
          (Gnosis.Body.Robustness.grit tolerance + 1)) ∧
    -- 6. Robustness: adversarial weak duality.
    (Gnosis.Body.Robustness.maxmin d₀ d₁ a₀ a₁
      ≤ Gnosis.Body.Robustness.minmax d₀ d₁ a₀ a₁) ∧
    -- 7. SapolskyStress: the inverted-U.
    (∃ pk : Nat, pk = capacity / 2 ∧
      (∀ s, 2 * s + 2 ≤ capacity →
        Gnosis.Body.SapolskyStress.performance s capacity
          < Gnosis.Body.SapolskyStress.performance (s + 1) capacity) ∧
      (∀ s, capacity ≤ 2 * s → s + 1 ≤ capacity →
        Gnosis.Body.SapolskyStress.performance (s + 1) capacity
          < Gnosis.Body.SapolskyStress.performance s capacity) ∧
      (Gnosis.Body.SapolskyStress.performance 0 capacity = 0 ∧
        Gnosis.Body.SapolskyStress.performance capacity capacity = 0)) ∧
    -- 8. SapolskyStress: acute withstands, chronic breaks.
    (Gnosis.Body.Robustness.withstands tolerance
        (Gnosis.Body.SapolskyStress.allostaticLoad perTick 0) ∧
      Gnosis.Body.Robustness.breaks tolerance
        (Gnosis.Body.SapolskyStress.allostaticLoad perTick (tolerance + 1))) ∧
    -- 9. SapolskyStress: the swerve is the only freedom.
    (Gnosis.Body.SapolskyStress.swerve state
      ≠ Gnosis.Body.SapolskyStress.behavior state) ∧
    -- 10. RedQueen: a period-2 orbit exists.
    (Gnosis.Body.RedQueen.step Gnosis.Body.RedQueen.s₀ ≠ Gnosis.Body.RedQueen.s₀ ∧
      Gnosis.Body.RedQueen.step (Gnosis.Body.RedQueen.step Gnosis.Body.RedQueen.s₀)
        = Gnosis.Body.RedQueen.s₀) ∧
    -- 11. RedQueen: over-push is pyrrhic.
    (Gnosis.Body.RedQueen.predatorFood grit p = 0) ∧
    -- 12. SelfDefense: adversaries improve you.
    (Gnosis.Body.SelfDefense.dodges (Gnosis.Body.SelfDefense.trainedReaction r n) w) ∧
    -- 13. WarMakesPeace: war makes peace.
    (Gnosis.Body.WarMakesPeace.peacemaking deal base v2 warCost) ∧
    -- 14. AmnesiaGritFrontier: amnesia is idempotent.
    (Gnosis.Body.AmnesiaGritFrontier.amnesia
        (Gnosis.Body.AmnesiaGritFrontier.amnesia m)
      = Gnosis.Body.AmnesiaGritFrontier.amnesia m) ∧
    -- 15. AmnesiaGritFrontier: grit/amnesia is a Pareto frontier.
    (Gnosis.Body.AmnesiaGritFrontier.accumulationValue
        (Gnosis.Body.AmnesiaGritFrontier.retain m r1 scale)
      ≤ Gnosis.Body.AmnesiaGritFrontier.accumulationValue
          (Gnosis.Body.AmnesiaGritFrontier.retain m r2 scale) ∧
      Gnosis.Body.AmnesiaGritFrontier.adaptability r2 scale
        < Gnosis.Body.AmnesiaGritFrontier.adaptability r1 scale) ∧
    -- 16. DiversityIsOptimal: diversity is maxmin-optimal.
    (Gnosis.Body.DiversityIsOptimal.worstCase payoff
          Gnosis.Body.DiversityIsOptimal.Strategy.monoculture = 0 ∧
      0 < Gnosis.Body.DiversityIsOptimal.worstCase payoff
          Gnosis.Body.DiversityIsOptimal.Strategy.diverse ∧
      Gnosis.Body.DiversityIsOptimal.worstCase payoff
          Gnosis.Body.DiversityIsOptimal.Strategy.monoculture
        < Gnosis.Body.DiversityIsOptimal.worstCase payoff
          Gnosis.Body.DiversityIsOptimal.Strategy.diverse ∧
      payoff Gnosis.Body.DiversityIsOptimal.Strategy.diverse
          Gnosis.Body.DiversityIsOptimal.Env.matched
        < payoff Gnosis.Body.DiversityIsOptimal.Strategy.monoculture
          Gnosis.Body.DiversityIsOptimal.Env.matched) ∧
    -- 17. Neurodiversity: comparative advantage preserves diversity.
    (∀ t t', t ≠ t' → ¬ Gnosis.Body.Neurodiversity.dominated fitness t t') ∧
    -- 18. DepressionAsCollapsedCycle: drive revives amplitude.
    (amplitude < Gnosis.Body.DepressionAsCollapsedCycle.driveStep amplitude drive) ∧
    -- 19. Vampire: total drain is pyrrhic.
    (Gnosis.Body.Vampire.vampireFood vRegen vN vDrain = 0) :=
  ⟨capstone_life_had_to_be dark hdark,
   capstone_stress_produces_culture stress hstress,
   capstone_comfort_is_cultural_death,
   capstone_life_happens_on_the_edges b hw hlo,
   capstone_grit_is_max_withstood tolerance perturbation,
   capstone_minmax_ge_maxmin d₀ d₁ a₀ a₁,
   capstone_inverted_u capacity,
   capstone_acute_withstands_chronic_breaks perTick tolerance hperTick,
   capstone_swerve_is_the_only_freedom state,
   capstone_has_period_two_orbit,
   capstone_over_push_is_pyrrhic grit p hpush,
   capstone_adversaries_improve r n w hdodge,
   capstone_war_makes_peace deal base warCost v1 v2 hv hpeace,
   capstone_amnesia_is_idempotent m,
   capstone_amnesia_grit_is_a_frontier m r1 r2 scale hr12 hr2,
   capstone_diversity_is_maxmin_optimal payoff hexposed hdm hds hdn hcertain,
   capstone_comparative_advantage_preserves_diversity fitness hadv,
   capstone_drive_revives_amplitude hDrive,
   capstone_total_drain_is_pyrrhic vRegen vN vDrain hCollapse⟩

end Gnosis.Body.GritTheory
