import Init

/-!
# Neurodiversity — Neurotypes as Maintained Evolutionary Strategies

The DSM frames certain neurotypes — autism, depression/rumination, and others —
as pathologies: deviations from a single "healthy" norm, to be corrected toward
that norm. The neurodiversity reading (Sapolsky, and the wider neurodiversity
movement) is different and, this module argues, more precise: these neurotypes
are stable strategies, each maintained in the population by selection because
each carries a comparative advantage in some niche. A trait that is costly in one
environment and decisive in another is not a defect; it is an adaptation whose
value is conditional on the niche. Selection does not eliminate such a trait — it
keeps it on the books, because the population that loses it loses the niche.

The argument here is deliberately *structural*, not numeric. We do not pin a
fitness matrix to literal numbers and grind out literal inequalities. Instead we
take the fitness function as an abstract parameter and prove relationships that
hold for *any* fitness assignment satisfying the comparative-advantage
hypothesis. Three relationships carry the weight:

* `dominated fitness t t'`  — `t` is never better than `t'` in any niche
  (the only condition under which selection could discard `t`).
* `hasAdvantage fitness t t'` — `t` strictly beats `t'` in at least one niche.
* `leadsIn fitness t n`      — `t` is fittest in niche `n`.

The chain of results: comparative advantage rules out domination
(`advantage_implies_not_dominated`), so a population in which every type beats
every other type somewhere has no dominated type
(`comparative_advantage_preserves_diversity`) — selection cannot prune any of
them, the diversity is stable. Meanwhile, if every niche has a leader, the
all-types population always contains its environment's fittest member
(`diversity_covers_every_niche`), where a monoculture would be unfit outside its
one niche. The corollary `pathology_is_a_strategy` names the point on a single
type, and `neurodiversity_principle` composes stability with robustness: every
neurotype is maintained, and the resulting population is robust across
environments. None is dominated; none is to be othered.

The autistic *systemizer* neurotype has comparative advantage in deep pattern and
formal-structure work — which is precisely the niche this Lean development itself
occupies. We state that plainly: a strategy with a niche, not a deficit.

(`Gnosis/Evolution.lean` — `Init`-clean — already shows the dual failure modes
with concrete witnesses: `monoculture_dies_on_change` and `diversity_can_survive`.
Those are literal `Bool` facts about a fixed scenario; this module gives the
abstract structural backbone behind them. We reference rather than import them,
to keep the parametrization clean.)

Rustic Church: `import Init` only (no Mathlib). `Nat` arithmetic only — no Float,
no Real. No `sorry`; no `simp`/`decide`/`omega` on open goals. Proofs run on named
core lemmas (`Nat.lt_irrefl`, `Nat.lt_of_lt_of_le`, `Nat.le_trans`, `Nat.le_refl`,
`Nat.le_of_lt`, `Nat.le_max_left`/`right`, `Nat.max_le`).
-/

namespace Gnosis.Body.Neurodiversity

/-! ## 1. The carriers: neurotypes and niches

We keep both as small inductives with `DecidableEq`, naming the four neurotypes
and the four niches in the discussion. Nothing in the theorems depends on the
particular constructors; the fitness function stays abstract throughout. -/

/-- The neurotypes under consideration. Each is a strategy, not a grade on a
    single scale:

    * `typical`    — the modal strategy, balanced across niches;
    * `systemizer` — the autistic pattern-and-formal-structure strategy, strong
      in technical/deep-structure niches (the niche this development occupies);
    * `ruminator`  — the depressive/analytic strategy, strong at sustained
      threat-appraisal and error-detection where vigilance pays;
    * `divergent`  — the exploratory strategy, strong in novel/unstable niches
      where the established playbook does not apply. -/
inductive NeuroType where
  | typical
  | systemizer
  | ruminator
  | divergent
  deriving DecidableEq, Repr

/-- The environmental niches a population can face. Which one is in force is set
    by the environment, not chosen by the organism — hence the value of holding
    a strategy for each:

    * `stable`    — settled conditions, the established playbook works;
    * `novel`     — new/unstable conditions, no established playbook;
    * `technical` — deep pattern / formal-structure problems;
    * `threat`    — danger present, vigilance and error-detection decisive. -/
inductive Niche where
  | stable
  | novel
  | technical
  | threat
  deriving DecidableEq, Repr

/-! ## 2. Abstract fitness relations

`fitness t n` is the fitness of neurotype `t` in niche `n`. We never fix its
values; every theorem takes `fitness` as a parameter, so the results are claims
about the *shape* of comparative advantage, true for any concrete assignment. -/

/-- `t` is **dominated by** `t'`: `t` is never strictly better than `t'` in any
    niche (`fitness t n ≤ fitness t' n` everywhere). This is the only condition
    under which selection could safely discard `t` — if `t'` matches or beats it
    in every environment, `t` carries no niche of its own. Stated as the property
    we will show *fails* for every maintained neurotype. -/
def dominated (fitness : NeuroType → Niche → Nat) (t t' : NeuroType) : Prop :=
  ∀ n, fitness t n ≤ fitness t' n

/-- `t` **leads in** niche `n`: no type is fitter than `t` there
    (`fitness t' n ≤ fitness t n` for all `t'`). The niche's specialist. -/
def leadsIn (fitness : NeuroType → Niche → Nat) (t : NeuroType) (n : Niche) : Prop :=
  ∀ t', fitness t' n ≤ fitness t n

/-- `t` **has comparative advantage over** `t'`: there is some niche where `t`
    strictly beats `t'` (`fitness t' n < fitness t n`). A type with comparative
    advantage over another has a corner of the world it does better — the
    formal content of "not a defect, a strategy with a niche". -/
def hasAdvantage (fitness : NeuroType → Niche → Nat) (t t' : NeuroType) : Prop :=
  ∃ n, fitness t' n < fitness t n

/-! ## 3. Comparative advantage rules out domination -/

/-- **Comparative advantage implies not dominated.** If `t` strictly beats `t'`
    in some niche, then `t` is not dominated by `t'`: at that niche `n` we have
    `fitness t' n < fitness t n`, which contradicts domination's requirement
    `fitness t n ≤ fitness t' n`. A single niche of advantage is enough to keep a
    type off the chopping block. -/
theorem advantage_implies_not_dominated
    (fitness : NeuroType → Niche → Nat) (t t' : NeuroType)
    (h : hasAdvantage fitness t t') : ¬ dominated fitness t t' := by
  intro hdom
  rcases h with ⟨n, hadv⟩
  -- hadv : fitness t' n < fitness t n
  -- hdom n : fitness t n ≤ fitness t' n
  -- chain to fitness t' n < fitness t' n, impossible
  exact Nat.lt_irrefl (fitness t' n) (Nat.lt_of_lt_of_le hadv (hdom n))

/-- **A niche leader is not dominated by anyone strictly worse there.** If `t`
    leads in niche `n` and some type `t'` is strictly worse than `t` at `n`
    (`fitness t' n < fitness t n`), then `t` is not dominated by `t'`: leading
    plus a strict gap is itself a comparative advantage. (The leadership
    hypothesis is recorded for context; the strict gap is what closes the
    contradiction, via `advantage_implies_not_dominated`.) -/
theorem leads_implies_not_dominated_by_any
    (fitness : NeuroType → Niche → Nat) (t t' : NeuroType) (n : Niche)
    (_hlead : leadsIn fitness t n) (hgap : fitness t' n < fitness t n) :
    ¬ dominated fitness t t' :=
  advantage_implies_not_dominated fitness t t' ⟨n, hgap⟩

/-! ## 4. The headline: comparative advantage maintains the whole spread -/

/-- **Comparative advantage preserves diversity.** Suppose every neurotype has a
    comparative advantage over every *other* neurotype — each type beats each
    other type in at least one niche. Then no type is dominated by any other.
    Selection prunes only dominated types, so under this hypothesis it can prune
    none of them: the full spread of neurotypes is stable. Each so-called
    "pathology", carrying its own niche of advantage, is a maintained strategy,
    not a deviation awaiting correction. -/
theorem comparative_advantage_preserves_diversity
    (fitness : NeuroType → Niche → Nat)
    (hadv : ∀ t t', t ≠ t' → hasAdvantage fitness t t') :
    ∀ t t', t ≠ t' → ¬ dominated fitness t t' := by
  intro t t' hne
  exact advantage_implies_not_dominated fitness t t' (hadv t t' hne)

/-! ## 5. Diversity covers every niche (robustness across environments)

A monoculture holds one strategy and is fit only in that strategy's niche; a
diverse population holds a specialist for each niche, so whichever niche the
environment selects, the population still fields its fittest member. We make this
exact: the all-types population's best fitness in a niche equals that niche's
leader's fitness. -/

/-- The **best fitness present in the all-types population** for niche `n`: the
    maximum of every neurotype's fitness there. A diverse population, holding all
    four strategies, realizes this maximum in every niche. -/
def popBest (fitness : NeuroType → Niche → Nat) (n : Niche) : Nat :=
  Nat.max (Nat.max (fitness NeuroType.typical n) (fitness NeuroType.systemizer n))
          (Nat.max (fitness NeuroType.ruminator n) (fitness NeuroType.divergent n))

/-- Every neurotype's fitness in a niche is at most the population's best there —
    `popBest` really is an upper bound over the whole population. -/
theorem le_popBest
    (fitness : NeuroType → Niche → Nat) (t : NeuroType) (n : Niche) :
    fitness t n ≤ popBest fitness n := by
  unfold popBest
  cases t with
  | typical =>
    exact Nat.le_trans
      (Nat.le_max_left (fitness NeuroType.typical n) (fitness NeuroType.systemizer n))
      (Nat.le_max_left _ _)
  | systemizer =>
    exact Nat.le_trans
      (Nat.le_max_right (fitness NeuroType.typical n) (fitness NeuroType.systemizer n))
      (Nat.le_max_left _ _)
  | ruminator =>
    exact Nat.le_trans
      (Nat.le_max_left (fitness NeuroType.ruminator n) (fitness NeuroType.divergent n))
      (Nat.le_max_right _ _)
  | divergent =>
    exact Nat.le_trans
      (Nat.le_max_right (fitness NeuroType.ruminator n) (fitness NeuroType.divergent n))
      (Nat.le_max_right _ _)

/-- **The all-types population realizes the niche leader's fitness.** If `t` leads
    in niche `n`, then the population's best fitness there equals `t`'s fitness:
    the diverse population, by containing the specialist `t`, performs in niche
    `n` exactly as well as the best possible single type. (`popBest ≤ fitness t n`
    because `t` leads and so dominates the max; `fitness t n ≤ popBest` because
    `t` is in the population.) -/
theorem popBest_eq_leader
    (fitness : NeuroType → Niche → Nat) (t : NeuroType) (n : Niche)
    (hlead : leadsIn fitness t n) :
    popBest fitness n = fitness t n := by
  apply Nat.le_antisymm
  · -- popBest ≤ fitness t n : every entry of the max is ≤ fitness t n, as t leads
    unfold popBest
    apply Nat.max_le.mpr
    refine ⟨?_, ?_⟩
    · exact Nat.max_le.mpr
        ⟨hlead NeuroType.typical, hlead NeuroType.systemizer⟩
    · exact Nat.max_le.mpr
        ⟨hlead NeuroType.ruminator, hlead NeuroType.divergent⟩
  · -- fitness t n ≤ popBest : t is a member of the population
    exact le_popBest fitness t n

/-- **Diversity covers every niche.** Assume each niche has some leading type.
    Then for every niche the all-types population's best fitness is achieved by a
    member who is fittest in that niche — so the diverse population is robust to
    whichever niche the environment imposes. A monoculture has one such member and
    one only; outside its niche it has no leader to field. Stated as: for every
    niche there is a member type whose fitness equals the population's best and
    who leads the niche. -/
theorem diversity_covers_every_niche
    (fitness : NeuroType → Niche → Nat)
    (hcover : ∀ n, ∃ t, leadsIn fitness t n) :
    ∀ n, ∃ t, leadsIn fitness t n ∧ popBest fitness n = fitness t n := by
  intro n
  rcases hcover n with ⟨t, hlead⟩
  exact ⟨t, hlead, popBest_eq_leader fitness t n hlead⟩

/-! ## 6. Naming the point -/

/-- **A "pathology" is a strategy.** Take a neurotype `t` that the DSM classes as
    a disorder. If it has comparative advantage in some niche over a type `t'`
    held up as the norm, then `t` is not dominated by that norm — there is an
    environment in which `t` is the better strategy. Selection therefore has no
    grounds to discard it. What is called a disorder, read by its niche, is a
    maintained strategy, not a defect to be othered into the norm. -/
theorem pathology_is_a_strategy
    (fitness : NeuroType → Niche → Nat) (t norm : NeuroType)
    (h : hasAdvantage fitness t norm) : ¬ dominated fitness t norm :=
  advantage_implies_not_dominated fitness t norm h

/-- The systemizer reading made concrete: granted that the systemizer beats the
    typical strategy in the `technical` niche (deep pattern / formal-structure
    work — the niche of this very development), the systemizer is not dominated by
    the typical norm. A niche of advantage, stated plainly. -/
theorem systemizer_not_dominated_by_typical
    (fitness : NeuroType → Niche → Nat)
    (h : fitness NeuroType.typical Niche.technical
          < fitness NeuroType.systemizer Niche.technical) :
    ¬ dominated fitness NeuroType.systemizer NeuroType.typical :=
  pathology_is_a_strategy fitness NeuroType.systemizer NeuroType.typical
    ⟨Niche.technical, h⟩

/-! ## 7. The neurodiversity principle (synthesis) -/

/-- **The neurodiversity principle.** Under two hypotheses about the fitness
    landscape —

    1. **comparative advantage everywhere**: every neurotype beats every other in
       some niche (`∀ t t', t ≠ t' → hasAdvantage fitness t t'`); and
    2. **every niche has a leader**: each niche is led by some type
       (`∀ n, ∃ t, leadsIn fitness t n`) —

    two things hold together:

    * **Stability**: no neurotype is dominated by any other, so selection cannot
      prune any of them — the full spread is maintained.
    * **Robustness**: for every niche the all-types population fields a member who
      is fittest there (its best fitness equals the niche leader's), so the
      diverse population holds up whichever niche the environment selects.

    Comparative advantage keeps every neurotype on the books; the resulting
    diversity keeps the population fit across environments. None dominated; none
    to be othered. -/
theorem neurodiversity_principle
    (fitness : NeuroType → Niche → Nat)
    (hadv : ∀ t t', t ≠ t' → hasAdvantage fitness t t')
    (hcover : ∀ n, ∃ t, leadsIn fitness t n) :
    (∀ t t', t ≠ t' → ¬ dominated fitness t t') ∧
    (∀ n, ∃ t, leadsIn fitness t n ∧ popBest fitness n = fitness t n) :=
  ⟨comparative_advantage_preserves_diversity fitness hadv,
   diversity_covers_every_niche fitness hcover⟩

end Gnosis.Body.Neurodiversity
