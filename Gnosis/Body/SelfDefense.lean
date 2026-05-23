import Init
import Gnosis.Body.Robustness
import Gnosis.Body.RedQueen

/-!
# Self-Defense — Ki, Dodgeball, and the Adversary Who Makes You Grittier

The Metaverse (the 3D Game-of-Life evolutionary world in `aeon-corpus`) pits
bodies against attacks. This module bridges the **adversary / sin / Ki** strand
of the theory to the **robustness / grit** strand, around a single concrete
self-defense model: **DODGEBALL**.

An incoming attack carries a *telegraph*: a `window` of warning ticks before it
lands. A defender has a *reaction*: the ticks it needs to observe-and-act. **Ki**
is exactly this — observing inside the window. Lower reaction = sharper Ki. The
two notions of `Gnosis.Body.Robustness` (`withstands`/`breaks`) reappear as
`dodges`/`hit`, so dodging *is* withstanding, on the defender's own dial.

The module is organized around six pictures, then a synthesis:

1. **Ki as observational defense.** `dodges r w := r ≤ w`, `hit r w := w < r`.
   Exhaustive and exclusive (`dodge_trichotomy`, `dodge_excludes_hit`); sharper
   Ki dodges more (`faster_ki_dodges_more`).
2. **Dodge grit.** The smallest still-dodgeable window is `reaction` itself
   (`dodges_iff_window_ge_reaction`, `dodgeGrit_eq_reaction`); sharpening Ki
   *strictly* lowers that minimum (`sharper_ki_lowers_grit`). Dodging is
   `Robustness.withstands` on the reaction dial (`dodges_is_withstands`).
3. **Adversaries improve** (the contrarian core). `trainedReaction r n := r - n`.
   Training never worsens Ki (`training_never_worsens_ki`); a trained defender
   dodges everything an untrained one did (`adversaries_improve`) and *strictly*
   lowers the minimum dodgeable window when `0 < n ≤ r`
   (`training_strictly_improves_grit`). Mirrors
   `AdversarialRobustness.robust_training`.
4. **Sin as the internal adversary.** A self-inflicted `sinPenalty` added to
   reaction — hubris stops the agent observing. An attack the un-sinning agent
   would have dodged now lands (`sin_lowers_defense`). The internal adversary is
   the costliest.
5. **Dodgeball as adversarial interaction.** A 2×2 throw/defend game; reuse
   `Robustness.maxmin`/`minmax`. Weak duality (`dodgeball_weak_duality`) and a
   concrete saddle (`dodgeball_saddle`).
6. `self_defense_principle` composes them all.

Rustic Church: `Init` only (plus the two sibling Body modules). `Nat` arithmetic,
proofs from core `Nat` lemmas. No `sorry`; no `simp`/`decide`/`omega` on open
goals.
-/

namespace Gnosis.Body.SelfDefense

-- Both sibling modules export `maxmin`/`minmax`/`payoff`/`isSaddle`/`saddle_point`.
-- We build the dodgeball game on `Robustness`'s versions and qualify those names
-- as `Robustness.…` (these resolve under the enclosing `Gnosis.Body`); `RedQueen`
-- is referenced conceptually (its `Phase` 2-cycle, `over_push_is_pyrrhic`) in the
-- prose. `open`ing both would make the shared names ambiguous, so we qualify
-- explicitly rather than opening either.

/-! ## 1. Ki as observational defense

An attack telegraphs for `window` ticks; the defender needs `reaction` ticks to
observe-and-act. The defender dodges iff it can act inside the window. This is
`Robustness.withstands`/`breaks` read on the *reaction* dial: the defender
"withstands" an attack whose warning window is at least its reaction time. Ki is
the discipline of keeping `reaction` small — of observing fast enough. -/

/-- The defender dodges iff its reaction fits inside the attack's telegraph
    window. Lower `reaction` (sharper Ki) dodges more. -/
def dodges (reaction window : Nat) : Prop := reaction ≤ window

/-- The defender is hit iff the window is too short for its reaction — the attack
    lands before observe-and-act completes. -/
def hit (reaction window : Nat) : Prop := window < reaction

/-- **Dodge trichotomy.** Against any telegraphed attack the defender either
    dodges it or is hit — exhaustively, no third option (mirrors
    `Robustness.robustness_trichotomy`). -/
theorem dodge_trichotomy (reaction window : Nat) :
    dodges reaction window ∨ hit reaction window := by
  unfold dodges hit
  rcases Nat.lt_or_ge window reaction with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- **Exclusivity.** Dodging and being hit cannot both happen: a clean evasion
    and a clean strike are genuine opposites (mirrors
    `Robustness.withstands_excludes_breaks`). -/
theorem dodge_excludes_hit (reaction window : Nat)
    (hd : dodges reaction window) : ¬ hit reaction window := by
  unfold dodges at hd
  unfold hit
  intro hh
  exact Nat.lt_irrefl window (Nat.lt_of_lt_of_le hh hd)

/-- **Sharper Ki dodges more.** If `r₁ ≤ r₂` (defender 1 has the faster, sharper
    Ki) and the slower defender already dodges an attack of window `w`, then the
    sharper one dodges it too. Ki = observe within the window: less time needed
    is never worse. -/
theorem faster_ki_dodges_more (r₁ r₂ w : Nat)
    (hki : r₁ ≤ r₂) (hd : dodges r₂ w) : dodges r₁ w := by
  unfold dodges at *
  exact Nat.le_trans hki hd

/-- **A wider telegraph is easier to dodge.** Fixing the defender, a longer
    warning window can only help: if a defender dodges a `w₁`-telegraphed attack
    and `w₁ ≤ w₂`, it dodges the `w₂`-telegraphed one. -/
theorem wider_telegraph_dodges (r w₁ w₂ : Nat)
    (hw : w₁ ≤ w₂) (hd : dodges r w₁) : dodges r w₂ := by
  unfold dodges at *
  exact Nat.le_trans hd hw

/-! ## 2. Dodge grit

Grit, in `Robustness`, is the hardest perturbation survived. For a dodger the
"hardest attack" is the *shortest* telegraph: the smaller the window, the faster
(harder) the throw. The smallest window a defender can still dodge is exactly its
`reaction` — so grit (the hardest dodgeable attack) is pinned to reaction. -/

/-- **Dodging is `Robustness.withstands` on the reaction dial.** With the
    defender's `reaction` as its tolerance and the telegraph `window` as the
    perturbation it must absorb, `dodges` and `withstands` are the same
    proposition. The self-defense model is literally the robustness model. -/
theorem dodges_is_withstands (reaction window : Nat) :
    dodges reaction window ↔ Robustness.withstands window reaction := by
  unfold dodges Robustness.withstands
  exact Iff.rfl

/-- The dodge grit of a defender: the smallest telegraph window it can still
    dodge — which we now prove is exactly its reaction time. (Smaller window =
    faster throw = harder attack, so this is the hardest attack survived.) -/
def dodgeGrit (reaction : Nat) : Nat := reaction

/-- **Dodgeable exactly when the window reaches the reaction.** The defender
    dodges an attack iff its telegraph window is at least the reaction time —
    definitional, but the load-bearing characterization the rest negates and
    sharpens. -/
theorem dodges_iff_window_ge_reaction (reaction window : Nat) :
    dodges reaction window ↔ reaction ≤ window := Iff.rfl

/-- **Grit is pinned to reaction.** The smallest dodgeable window equals the
    reaction: the defender dodges right at `window = dodgeGrit reaction` but a
    one-tick-faster throw (`window = reaction - 1`, i.e. one below grit when
    `0 < reaction`) gets through. The boundary is sharp. -/
theorem dodgeGrit_eq_reaction (reaction : Nat) :
    dodges reaction (dodgeGrit reaction)
      ∧ (0 < reaction → hit reaction (reaction - 1)) := by
  unfold dodgeGrit dodges hit
  refine ⟨Nat.le_refl reaction, ?_⟩
  intro hpos
  -- reaction - 1 < reaction when 0 < reaction
  exact Nat.sub_lt hpos Nat.zero_lt_one

/-- **Sharper Ki strictly lowers the minimum dodgeable window.** If `r₁ < r₂`
    then `dodgeGrit r₁ < dodgeGrit r₂`: a faster reaction can dodge a strictly
    faster throw (a strictly smaller window) than a slower one. Improving Ki
    pushes the grit floor down — strictly. -/
theorem sharper_ki_lowers_grit (r₁ r₂ : Nat) (h : r₁ < r₂) :
    dodgeGrit r₁ < dodgeGrit r₂ := by
  unfold dodgeGrit
  exact h

/-! ## 3. Adversaries improve (the contrarian core)

Here is the headline of the whole module: **the enemy makes you grittier.** Each
round of training against attacks sharpens Ki — lowers reaction — flooring at 0
(`Nat` truncated subtraction does this for free). A defender trained against
adversaries dodges *at least* everything the untrained one did, and after even a
single effective round it dodges a strictly faster throw. This mirrors
`AdversarialRobustness.robust_training`: adversarial training raises the
robustness radius. Here it lowers the reaction (which is the same thing on the
dodge dial — a smaller reaction is a wider effective robustness margin). -/

/-- Ki after `rounds` of adversarial training: reaction sharpens by one tick per
    round, floored at 0. Practice against attacks makes observe-and-act faster. -/
def trainedReaction (reaction rounds : Nat) : Nat := reaction - rounds

/-- **Training never worsens Ki.** However many rounds, the trained reaction is
    never larger than the untrained one (truncated `Nat.sub` only ever shrinks).
    The adversary cannot make you slower; at worst it does nothing. -/
theorem training_never_worsens_ki (r n : Nat) : trainedReaction r n ≤ r := by
  unfold trainedReaction
  exact Nat.sub_le r n

/-- **Adversaries improve you.** Any attack the untrained defender dodges, the
    *trained* defender dodges too: training only widens the dodgeable set. This is
    the dodge-dial mirror of `AdversarialRobustness.robust_training` — adversarial
    practice raises robustness. The enemy makes you grittier. -/
theorem adversaries_improve (r n w : Nat) (hd : dodges r w) :
    dodges (trainedReaction r n) w := by
  -- trainedReaction r n ≤ r, and sharper Ki dodges everything the slower did.
  exact faster_ki_dodges_more (trainedReaction r n) r w (training_never_worsens_ki r n) hd

/-- **Effective training strictly sharpens Ki.** With at least one round and not
    yet floored (`0 < n ≤ r`), the trained reaction is strictly below the
    untrained one. (`r - n < r` exactly when `0 < n` and `0 < r`.) -/
theorem training_strictly_sharpens (r n : Nat) (hn : 0 < n) (hnr : n ≤ r) :
    trainedReaction r n < r := by
  unfold trainedReaction
  -- 0 < r since 0 < n ≤ r
  have hr : 0 < r := Nat.lt_of_lt_of_le hn hnr
  exact Nat.sub_lt hr hn

/-- **Training strictly improves grit.** Mirrors
    `AdversarialRobustness.robust_training` quantitatively: with `0 < n ≤ r`, the
    trained defender's minimum dodgeable window is *strictly* smaller than the
    untrained one's — it can dodge a strictly faster throw. The robustness radius
    (here, the reciprocal notion: a smaller grit floor) genuinely rises with
    adversarial training, not merely "does not fall." -/
theorem training_strictly_improves_grit (r n : Nat) (hn : 0 < n) (hnr : n ≤ r) :
    dodgeGrit (trainedReaction r n) < dodgeGrit r :=
  sharper_ki_lowers_grit (trainedReaction r n) r (training_strictly_sharpens r n hn hnr)

/-- **The robust-training mirror, stated as a dodge.** After effective training
    the defender dodges an attack one tick faster than its old grit floor — an
    attack the *untrained* defender was hit by. Concretely: the untrained
    defender is hit by `window = r - 1` (when `0 < r`), but a defender trained
    one effective round dodges it. The new robustness strictly contains the old.
    (Compare `robust_training`: `godWeight R_robust > godWeight R_normal`.) -/
theorem robust_training_dodges_more (r n : Nat) (hn : 0 < n) (hnr : n ≤ r) :
    hit r (r - 1) ∧ dodges (trainedReaction r n) (r - 1) := by
  have hr : 0 < r := Nat.lt_of_lt_of_le hn hnr
  refine ⟨?_, ?_⟩
  · -- untrained defender is hit by window r-1
    exact (dodgeGrit_eq_reaction r).right hr
  · -- trained defender dodges window r-1:  trainedReaction r n ≤ r - 1
    unfold dodges trainedReaction
    -- r - n ≤ r - 1  since 1 ≤ n
    exact Nat.sub_le_sub_left hn r

/-! ## 4. Sin as the internal adversary

`TwoTypesOfSin` models sin as an Agent claiming the God-position — the creature
who thinks itself the Monad and so stops *observing*, since a god has nothing to
watch for. We model that hubris as a self-inflicted reaction penalty added to the
defender's own reaction. The internal adversary is the costliest: it degrades Ki
directly, turning an attack the un-sinning agent would have dodged into a hit. We
keep `sinPenalty` local (a `Nat`) to stay `Init`-clean, in the spirit of
`TwoTypesOfSin.animalMagnetism`. -/

/-- The self-inflicted Ki penalty of sin: hubris (the agent who thinks himself
    God stops watching) added to reaction time. The internal adversary slows the
    defender from the inside. -/
def sinReaction (reaction sinPenalty : Nat) : Nat := reaction + sinPenalty

/-- **Sin never sharpens Ki.** The sinning reaction is never below the clean one
    — hubris can only slow you (it adds, never subtracts). The exact dual of
    `training_never_worsens_ki`: the external adversary may help, the internal
    one never does. -/
theorem sin_never_sharpens_ki (reaction sinPenalty : Nat) :
    reaction ≤ sinReaction reaction sinPenalty := by
  unfold sinReaction
  exact Nat.le_add_right reaction sinPenalty

/-- **Sin lowers defense.** Take an attack telegraphed *exactly* at `reaction` —
    one the un-sinning agent dodges precisely (`dodges reaction reaction`, the
    grit boundary). Any positive `sinPenalty` makes the sinning agent miss it:
    `¬ dodges (reaction + sinPenalty) reaction`. The creature who claims the
    God-position stops observing inside the window and takes the hit it would
    otherwise have evaded. The internal adversary is the costliest — unlike the
    external one, it strictly degrades grit. -/
theorem sin_lowers_defense (reaction sinPenalty : Nat) (hs : 0 < sinPenalty) :
    ¬ dodges (sinReaction reaction sinPenalty) reaction := by
  unfold dodges sinReaction
  intro hle
  -- hle : reaction + sinPenalty ≤ reaction, with 0 < sinPenalty — impossible.
  -- reaction < reaction + sinPenalty  (since 0 < sinPenalty)
  have hlt : reaction < reaction + sinPenalty := Nat.lt_add_of_pos_right hs
  exact Nat.lt_irrefl reaction (Nat.lt_of_lt_of_le hlt hle)

/-- **The very same attack is dodged without sin.** The grit-boundary attack
    (`window = reaction`) is dodged precisely when the agent is not sinning,
    making the loss in `sin_lowers_defense` real: sin converts a dodge into a hit
    on an otherwise-survivable attack. -/
theorem clean_agent_dodges_boundary (reaction : Nat) :
    dodges reaction reaction := by
  unfold dodges
  exact Nat.le_refl reaction

/-- **Sin is hit where training is dodge.** Pinning the contrast: on the
    grit-boundary attack, the trained (external-adversary) defender still dodges
    (training never worsens Ki), while the sinning (internal-adversary) defender
    is hit. The enemy outside makes you grittier; the enemy inside makes you
    brittle. -/
theorem internal_adversary_costlier (reaction sinPenalty n : Nat)
    (hs : 0 < sinPenalty) :
    dodges (trainedReaction reaction n) reaction
      ∧ ¬ dodges (sinReaction reaction sinPenalty) reaction :=
  ⟨adversaries_improve reaction n reaction (clean_agent_dodges_boundary reaction),
   sin_lowers_defense reaction sinPenalty hs⟩

/-! ## 5. Dodgeball as adversarial interaction + minmax

A dodgeball round is a 2×2 game. The thrower picks an attack: a *small* window is
a fast throw, a *large* window a slow one. The defender picks a reaction. The
payoff to the defender is the dodge *margin* `window - reaction` (truncated at 0
— a hit scores nothing), exactly `Robustness.payoff`. We reuse
`Robustness.maxmin`/`minmax` directly: think of the "defense" axis as the
telegraph window the defender forces (a wide window helps it) and the "attack"
axis as the thrower's reaction-cost imposition. Weak duality and a concrete
saddle follow from the robustness lemmas — the dodgeball game has a value, and at
the saddle neither thrower nor defender can profitably deviate.

We also tie to `RedQueen.over_push_is_pyrrhic` conceptually: a thrower who throws
*infinitely* fast (window 0) guarantees a hit but, like over-pushing prey past
grit, leaves no game — the analogue of starving on the corpses is a degenerate
round with margin 0 for everyone. -/

/-- The dodge margin (defender payoff) of a dodgeball cell: how many ticks of
    telegraph remain after the defender reacts, floored at 0. This is exactly
    `Robustness.payoff` — the dodgeball game is the robustness game. -/
def dodgeMargin (window reaction : Nat) : Nat := Robustness.payoff window reaction

/-- The dodge margin coincides with `Robustness.payoff`. -/
theorem dodgeMargin_is_payoff (window reaction : Nat) :
    dodgeMargin window reaction = Robustness.payoff window reaction := rfl

/-- **A positive dodge margin means a dodge.** If the defender clears the throw
    with ticks to spare (`reaction < window`), it dodges. Margin measures the
    quality of the dodge. -/
theorem positive_margin_dodges (window reaction : Nat) (h : reaction < window) :
    0 < dodgeMargin window reaction ∧ dodges reaction window := by
  unfold dodgeMargin Robustness.payoff dodges
  exact ⟨Nat.zero_lt_sub_of_lt h, Nat.le_of_lt h⟩

/-- **A hit scores zero margin.** If the throw beats the reaction
    (`window < reaction`, a hit), the margin is exactly 0 — the dodgeball reading
    of "once overwhelmed, survival is none." -/
theorem hit_has_zero_margin (window reaction : Nat) (h : hit reaction window) :
    dodgeMargin window reaction = 0 := by
  unfold dodgeMargin Robustness.payoff hit at *
  exact Nat.sub_eq_zero_of_le (Nat.le_of_lt h)

/-- **Dodgeball weak duality.** Over the 2×2 round (defender's two window-forcing
    choices `d₀,d₁` against the thrower's two reaction-cost choices `a₀,a₁`), what
    the defender can *guarantee* never exceeds what the thrower can *hold it to* —
    `maxmin ≤ minmax`. Reuses `Robustness.minmax_ge_maxmin` directly; the
    dodgeball game inherits the structural backbone of adversarial robustness. -/
theorem dodgeball_weak_duality (d₀ d₁ a₀ a₁ : Nat) :
    Robustness.maxmin d₀ d₁ a₀ a₁ ≤ Robustness.minmax d₀ d₁ a₀ a₁ :=
  Robustness.minmax_ge_maxmin d₀ d₁ a₀ a₁

/-- A concrete dodgeball matrix and its saddle, oriented so the saddle cell is
    the `(d₀, a₀)` slot `Robustness.saddle_point` expects. Defender choices
    `d₀ = 5, d₁ = 3` (windows it can force); thrower choices `a₀ = 4, a₁ = 2`
    (reaction costs it imposes). Payoffs `payoff d a = d - a`:

         a₀=4  a₁=2
    d₀=5   1     3      (row min 1)   ← maxmin = max(1,0) = 1
    d₁=3   0     1      (row min 0)
    col    1     3
    max                               ← minmax = min(1,3) = 1

    The cell `(d₀, a₀) = (5, 4)` has payoff 1; it is the worst the thrower can do
    against `d₀` (its payoff ≤ the `a₁` payoff 3) and the best the defender can do
    against `a₀` (its payoff ≥ the `d₁` payoff 0). That is a saddle, so by
    `Robustness.saddle_point` the game value is pinned: `maxmin = minmax = 1`. -/
theorem dodgeball_saddle :
    Robustness.maxmin 5 3 4 2 = Robustness.minmax 5 3 4 2 := by
  -- (d★, a★) = (d₀ = 5, a₀ = 4) is a genuine saddle of this matrix.
  have hsad : Robustness.isSaddle 5 4 3 2 := by
    unfold Robustness.isSaddle Robustness.payoff
    -- need:  payoff 5 4 ≤ payoff 5 2   and   payoff 3 4 ≤ payoff 5 4
    --        i.e.  5 - 4 ≤ 5 - 2  (1 ≤ 3)   and   3 - 4 ≤ 5 - 4  (0 ≤ 1)
    refine ⟨?_, ?_⟩
    · -- 1 ≤ 3
      exact Nat.le_of_lt (Nat.lt_of_sub_eq_succ rfl)
    · -- 0 ≤ 1
      exact Nat.zero_le (5 - 4)
  -- The saddle pins the value via the reused robustness lemma.
  exact Robustness.saddle_point 5 3 4 2 hsad

/-- **Over-fast throwing is pyrrhic** (the `RedQueen.over_push_is_pyrrhic`
    analogue). A thrower who throws infinitely fast — window 0 — guarantees a hit
    against any positive reaction, but the dodge margin everyone walks away with
    is 0: no game, no skill expressed, the degenerate round. Like the predator
    that over-pushes prey past grit and starves on the corpses, maximal attack
    speed yields a hollow "win." Sustainable dodgeball, like sustainable
    predation, lives strictly inside the margin. -/
theorem over_fast_throw_is_pyrrhic (reaction : Nat) (h : 0 < reaction) :
    hit reaction 0 ∧ dodgeMargin 0 reaction = 0 := by
  refine ⟨?_, ?_⟩
  · unfold hit
    exact h
  · unfold dodgeMargin Robustness.payoff
    exact Nat.zero_sub reaction

/-! ## 6. The headline synthesis -/

/-- **The self-defense principle.** The adversary/sin/Ki theory and the
    robustness/grit theory are one theory, seen through dodgeball:

    1. **Ki within the window** — the defender dodges iff its reaction fits the
       telegraph; dodging *is* `Robustness.withstands` on the reaction dial
       (`dodges_is_withstands`), and the two outcomes are exhaustive and
       exclusive.
    2. **Adversaries improve you** — a defender trained against attacks dodges at
       least everything the untrained one did (`adversaries_improve`) and, after
       an effective round, dodges a *strictly* faster throw the untrained one was
       hit by. Robustness rises with adversarial training (the
       `AdversarialRobustness.robust_training` mirror). The enemy makes you
       grittier.
    3. **Sin lowers defense** — the internal adversary (the creature claiming the
       God-position and so ceasing to observe) adds a positive reaction penalty
       and converts the grit-boundary dodge into a hit (`sin_lowers_defense`).
       The costliest adversary is the one inside.
    4. **The interaction has a value** — the dodgeball game's weak duality
       `maxmin ≤ minmax` holds always, so what the defender can guarantee is its
       maxmin floor.

    Bundled so the four are provably the same theory. -/
theorem self_defense_principle
    (reaction window n sinPenalty : Nat)
    (hs : 0 < sinPenalty)
    (d₀ d₁ a₀ a₁ : Nat) :
    -- 1. Ki within the window: dodging = withstanding, and the outcome is total.
    ((dodges reaction window ↔ Robustness.withstands window reaction)
      ∧ (dodges reaction window ∨ hit reaction window)) ∧
    -- 2. Adversaries improve you: trained dodges everything untrained did.
    (dodges reaction window → dodges (trainedReaction reaction n) window) ∧
    -- 3. Sin (internal adversary) lowers defense on an otherwise-dodged attack.
    (dodges reaction reaction
      ∧ ¬ dodges (sinReaction reaction sinPenalty) reaction) ∧
    -- 4. The dodgeball interaction's value: the defender's maxmin floor holds.
    (Robustness.maxmin d₀ d₁ a₀ a₁ ≤ Robustness.minmax d₀ d₁ a₀ a₁) := by
  refine ⟨⟨dodges_is_withstands reaction window, dodge_trichotomy reaction window⟩,
          ?_, ?_, dodgeball_weak_duality d₀ d₁ a₀ a₁⟩
  · intro hd
    exact adversaries_improve reaction n window hd
  · exact ⟨clean_agent_dodges_boundary reaction, sin_lowers_defense reaction sinPenalty hs⟩

end Gnosis.Body.SelfDefense
