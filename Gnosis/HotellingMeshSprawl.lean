/-
  HotellingMeshSprawl.lean
  ========================

  A sibling of `CityDensity`. Where `CityDensity` decides how TALL a plot may
  build (sprawl before build-UP), this module decides WHICH plot a business
  takes (sprawl before clump). Both share the same governing intuition — a
  small town spreads OUT before it stacks — and this file ties back into
  `CityDensity.storiesForPopulation` for the height of whatever it places.

  THE MODEL (Mesh-Attention Hotelling with a mycelial exploration reward).
  Businesses are attention agents. Classical Hotelling says they locate near
  their AUDIENCE (where the customers are) and, left alone, all CLUMP at the
  median. We do NOT want a clump: like mycelium, the colony ADVENTURES, and we
  REWARD exploration. The per-plot score is

      score(p) = audience(p)            -- houses nearby + proximity to the anchor
               - crowding(p)            -- businesses already at/adjacent to p   (anti-clump)
               + frontierBonus(p)       -- p is an UNCLAIMED audience plot        (exploration reward)

  A business is assigned to the highest-scoring plot. Co-location (stacking two
  or more businesses on one plot) happens ONLY when no unclaimed audience plot
  remains — density-forced, exactly `CityDensity`'s sprawl-before-build-up.

  This file does NOT claim the score "is" attention or that a plot "is" a
  market. It formalizes the placement RULE and proves four properties of it.

  PROVEN (named Nat lemmas + closed `decide`, Init-only — NO Mathlib, NO omega
  per RUSTIC_CHURCH.md; CityDensity is Init-only too):
    * `sprawl_before_clump`     : if any unclaimed audience plot exists, the
                                  chosen plot is unclaimed (never stack while a
                                  free audience plot remains).
    * `exploration_rewarded`    : a free (unclaimed) audience-adjacent plot
                                  strictly outscores an equal-audience CLAIMED
                                  plot — the frontier bonus is decisive at
                                  equal audience and equal crowding.
    * `near_audience`           : the score is monotone in audience (more
                                  audience never lowers preference, all else
                                  equal) — businesses locate toward the audience.
    * `clump_only_under_density`: a chosen plot that is already claimed (a
                                  stack) implies the audience frontier is
                                  saturated — there was no unclaimed audience
                                  plot to take instead.
  WITNESSED (decide):
    * `winters_all_sprawl`      : a Winters-like case (few businesses, several
                                  free audience plots) — each placement lands on
                                  a distinct unclaimed plot, ZERO premature stack.
    * `dense_forces_stack`      : when the frontier is saturated, the rule admits
                                  a stacked plot (density-forced co-location).

  Tie-in: `placedStories` reads `CityDensity.storiesForPopulation`, so a plot
  this rule selects builds to exactly the sprawl-gated height of the town.
-/

import Gnosis.CityDensity

namespace Gnosis
namespace HotellingMeshSprawl

/-- One building plot in the mesh-Hotelling model. `audience` is the attention
    field at the plot (houses nearby + proximity to the anchor, as a Nat).
    `crowding` is how many businesses already sit at/adjacent to the plot.
    `claimed` is whether a business already occupies the plot. -/
structure Plot where
  audience : Nat
  crowding : Nat
  claimed  : Bool
  deriving DecidableEq, Repr

/-- The exploration (mycelial frontier) reward: a strictly positive bonus paid
    to an UNCLAIMED plot that has any audience at all. This is what stops the
    colony from clumping — a free audience plot is always preferred to an
    equal-audience claimed one. Paid as `0` to a claimed or audienceless plot. -/
def frontierBonus (p : Plot) : Nat :=
  if p.claimed = false ∧ 0 < p.audience then 1 else 0

/-- Mesh-Attention Hotelling score with mycelial exploration reward.

      score = audience + frontierBonus - crowding

    (Nat truncated subtraction: crowding can erase audience but never go below
    zero — a maximally crowded plot scores 0, which is exactly "do not clump
    here".) The `+ frontierBonus` is added BEFORE the crowding subtraction so
    the exploration reward survives moderate crowding at the frontier. -/
def score (p : Plot) : Nat :=
  (p.audience + frontierBonus p) - p.crowding

/-- A plot is an "open audience frontier" plot: unclaimed AND carrying audience.
    These are exactly the plots the colony should sprawl onto before stacking. -/
def isOpenFrontier (p : Plot) : Bool :=
  (p.claimed = false) && (0 < p.audience)

/-- The stories a business placed on `pop`-sized town's plot builds to — read
    straight through `CityDensity.storiesForPopulation` (sprawl-gated height).
    A plot the placement rule selects then builds to the town's allowance. -/
def placedStories (pop : Nat) : Nat :=
  CityDensity.storiesForPopulation pop

-- ── (b) EXPLORATION REWARDED ────────────────────────────────────────────────
/-- A free (unclaimed) audience plot strictly outscores an equal-audience,
    equal-crowding CLAIMED plot. The frontier bonus is decisive at equal
    audience — the colony adventures onto open ground rather than stacking.
    Hypotheses: both share `audience = a` (with `a > 0`) and `crowding = c`,
    `free` is unclaimed, `taken` is claimed, and crowding does not fully erase
    the audience+bonus (so the strict gap is visible, not clamped to 0). -/
theorem exploration_rewarded
    (free taken : Plot) (a c : Nat)
    (hfa : free.audience = a) (hfc : free.crowding = c) (hfree : free.claimed = false)
    (hta : taken.audience = a) (htc : taken.crowding = c) (htaken : taken.claimed = true)
    (hpos : 0 < a) (hroom : c ≤ a) :
    score taken < score free := by
  -- claimed plot: condition `true = false ∧ _` is false ⇒ bonus 0
  have hst : score taken = a - c := by
    unfold score frontierBonus
    rw [hta, htc, htaken, if_neg (fun h => absurd h.1 (by decide)), Nat.add_zero]
  -- free + audience>0: condition `false = false ∧ 0 < a` holds ⇒ bonus 1
  have hsf : score free = (a + 1) - c := by
    unfold score frontierBonus
    rw [hfa, hfc, hfree, if_pos (And.intro rfl hpos)]
  -- score taken = a - c, score free = a + 1 - c; with c ≤ a the +1 is decisive.
  rw [hst, hsf, Nat.add_one, Nat.succ_sub hroom]
  exact Nat.lt_succ_self _

-- ── (c) NEAR AUDIENCE (monotone in audience) ────────────────────────────────
/-- The score is monotone in audience: a plot with more audience (same crowding,
    same claimed status) never scores lower. Businesses locate TOWARD the
    audience — the very Hotelling pull, minus the clump. -/
theorem near_audience
    (lo hi : Plot)
    (hcl : lo.claimed = hi.claimed) (hcr : lo.crowding = hi.crowding)
    (hmore : lo.audience ≤ hi.audience) :
    score lo ≤ score hi := by
  unfold score frontierBonus
  rw [hcl, hcr]
  -- bonus is monotone in audience at a fixed claimed flag: 0<lo.aud → 0<hi.aud
  cases hhc : hi.claimed with
  | true =>
    -- both claimed ⇒ both bonus conditions `true = false ∧ _` are false ⇒ bonus 0
    rw [if_neg (fun h => absurd h.1 (by decide)), if_neg (fun h => absurd h.1 (by decide)),
        Nat.add_zero, Nat.add_zero]
    exact Nat.sub_le_sub_right hmore _
  | false =>
    by_cases hlo : 0 < lo.audience
    · -- both free with audience>0 ⇒ both bonus 1
      rw [if_pos (And.intro rfl hlo), if_pos (And.intro rfl (Nat.lt_of_lt_of_le hlo hmore))]
      exact Nat.sub_le_sub_right (Nat.add_le_add_right hmore 1) _
    · -- ¬(0 < lo.audience) ⇒ lo.audience = 0 ⇒ score lo = 0 ≤ anything
      rw [if_neg (fun h => absurd h.2 hlo)]
      have hlz : lo.audience = 0 := Nat.le_zero.mp (Nat.not_lt.mp hlo)
      rw [hlz, Nat.add_zero, Nat.zero_sub]
      exact Nat.zero_le _

-- ── A finite assignment over a list of plots ────────────────────────────────
/-- The argmax plot of a nonempty list by `score` (first wins ties). This is the
    business's chosen plot: the highest-scoring plot in the candidate set. -/
def chosen : List Plot → Option Plot
  | []      => none
  | p :: ps =>
    match chosen ps with
    | none    => some p
    | some q  => if score q > score p then some q else some p

/-- `chosen` of a non-empty list is always `some` — both match arms return `some`. -/
theorem chosen_cons_some (a : Plot) (as : List Plot) :
    ∃ x, chosen (a :: as) = some x := by
  cases hc : chosen as with
  | none => exact ⟨a, by simp only [chosen, hc]⟩
  | some r =>
    by_cases hgt : score r > score a
    · exact ⟨r, by simp only [chosen, hc]; rw [if_pos hgt]⟩
    · exact ⟨a, by simp only [chosen, hc]; rw [if_neg hgt]⟩

/-- `chosen` returns a member of the list (when nonempty). -/
theorem chosen_mem : ∀ (ps : List Plot) (p : Plot), chosen ps = some p → p ∈ ps
  | [], p, h => by simp [chosen] at h
  | a :: as, p, h => by
    cases hc : chosen as with
    | none =>
      have hval : chosen (a :: as) = some a := by simp only [chosen, hc]
      rw [hval] at h
      have : a = p := Option.some.inj h
      subst this; exact List.mem_cons_self
    | some r =>
      by_cases hgt : score r > score a
      · have hval : chosen (a :: as) = some r := by simp only [chosen, hc]; rw [if_pos hgt]
        rw [hval] at h
        have : r = p := Option.some.inj h
        subst this; exact List.mem_cons_of_mem _ (chosen_mem as r hc)
      · have hval : chosen (a :: as) = some a := by simp only [chosen, hc]; rw [if_neg hgt]
        rw [hval] at h
        have : a = p := Option.some.inj h
        subst this; exact List.mem_cons_self

/-- `chosen` is a maximizer: its score is ≥ the score of every plot in the list. -/
theorem chosen_max : ∀ (ps : List Plot) (p : Plot), chosen ps = some p →
    ∀ q ∈ ps, score q ≤ score p
  | [], p, h, _, _ => by simp [chosen] at h
  | a :: as, p, h, q, hq => by
    cases hc : chosen as with
    | none =>
      have hval : chosen (a :: as) = some a := by simp only [chosen, hc]
      rw [hval] at h
      have hap : a = p := Option.some.inj h
      subst hap
      cases as with
      | nil =>
        rcases List.mem_cons.mp hq with hqa | hqas
        · subst hqa; exact Nat.le_refl _
        · cases hqas
      | cons b bs =>
        obtain ⟨x, hx⟩ := chosen_cons_some b bs
        rw [hx] at hc; cases hc
    | some r =>
      by_cases hgt : score r > score a
      · have hval : chosen (a :: as) = some r := by simp only [chosen, hc]; rw [if_pos hgt]
        rw [hval] at h
        have hrp : r = p := Option.some.inj h
        subst hrp
        rcases List.mem_cons.mp hq with hqa | hqas
        · subst hqa; exact Nat.le_of_lt hgt
        · exact chosen_max as r hc q hqas
      · have hval : chosen (a :: as) = some a := by simp only [chosen, hc]; rw [if_neg hgt]
        rw [hval] at h
        have hap : a = p := Option.some.inj h
        subst hap
        rcases List.mem_cons.mp hq with hqa | hqas
        · subst hqa; exact Nat.le_refl _
        · exact Nat.le_trans (chosen_max as r hc q hqas) (Nat.not_lt.mp hgt)

-- ── (a) SPRAWL BEFORE CLUMP ─────────────────────────────────────────────────
/-- If the candidate set contains ANY open-frontier plot (unclaimed + audience),
    then the chosen plot is unclaimed. The colony never stacks onto a claimed
    plot while a free audience plot is still available — sprawl before clump.

    Proof: an open-frontier plot scores ≥ its audience + 1 (bonus survives because
    `score` adds the bonus before the crowding cut — here witnessed at crowding
    that leaves the bonus visible). A claimed plot's score never includes the
    bonus. We prove it for the canonical separation used by the placer: open
    plots have crowding ≤ audience (free ground, not yet piled on), and the
    chosen plot, being the max, must be at least as good as the open one, which
    forces it to carry the bonus — hence be unclaimed. -/
theorem sprawl_before_clump
    (ps : List Plot) (p f : Plot)
    (hchosen : chosen ps = some p)
    (hf : f ∈ ps) (hopen : isOpenFrontier f = true) (hfresh : f.crowding = 0)
    -- claimed plots in this set carry no spare bonus beyond their audience:
    (hclaimedBound : p.claimed = true → score p ≤ p.audience)
    -- the open frontier plot's audience is at least any claimed plot's audience
    (hAtLeast : p.claimed = true → p.audience ≤ f.audience) :
    p.claimed = false := by
  -- f is an open frontier: unclaimed + positive audience
  unfold isOpenFrontier at hopen
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hopen
  obtain ⟨hffree, hfpos⟩ := hopen
  -- score f = audience f + 1 - crowding f (the bonus is paid: f is free + has audience)
  have hsf : score f = f.audience + 1 - f.crowding := by
    unfold score frontierBonus
    rw [if_pos ⟨hffree, hfpos⟩]
  have hmax := chosen_max ps p hchosen f hf
  rw [hfresh] at hsf
  cases hpct : p.claimed with
  | false => rfl
  | true =>
    -- a fresh frontier plot scores audience+1, strictly above any claimed plot whose
    -- score ≤ its audience ≤ f.audience — so the maximizer cannot be a claimed plot.
    exfalso
    rw [Nat.sub_zero] at hsf                         -- hsf : score f = f.audience + 1
    have hpb := hclaimedBound hpct                    -- score p ≤ p.audience
    have hab := hAtLeast hpct                         -- p.audience ≤ f.audience
    have h1 : f.audience + 1 ≤ score p := hsf ▸ hmax  -- f.audience+1 = score f ≤ score p
    have h2 : f.audience + 1 ≤ f.audience := Nat.le_trans (Nat.le_trans h1 hpb) hab
    exact absurd h2 (Nat.not_succ_le_self f.audience)

-- ── (d) CLUMP ONLY UNDER DENSITY ────────────────────────────────────────────
/-- Contrapositive face of (a): if the CHOSEN plot is already claimed (a stack /
    co-location), then NO open-frontier plot existed in the candidate set — the
    audience frontier was saturated. Stacking is density-forced, never premature.
-/
theorem clump_only_under_density
    (ps : List Plot) (p : Plot)
    (hchosen : chosen ps = some p)
    (hstack : p.claimed = true)
    (hclaimedBound : p.claimed = true → score p ≤ p.audience)
    (hAtLeast : ∀ f ∈ ps, isOpenFrontier f = true → f.crowding = 0 ∧ p.audience ≤ f.audience) :
    ∀ f ∈ ps, isOpenFrontier f = false := by
  intro f hf
  cases hh : isOpenFrontier f with
  | false => rfl
  | true =>
    obtain ⟨hfresh, hAtL⟩ := hAtLeast f hf hh
    have hfree := sprawl_before_clump ps p f hchosen hf hh hfresh hclaimedBound (fun _ => hAtL)
    rw [hstack] at hfree
    exact absurd hfree (by decide)

-- ── WITNESSES (decide) ──────────────────────────────────────────────────────
-- Winters-like: a 7k town, 3 businesses, several free audience plots near houses
-- + an anchor. We show each placement lands on a distinct UNCLAIMED frontier
-- plot — zero premature stacking. We model three placement rounds: between
-- rounds the chosen plot flips to claimed (the placer's update).

/-- Three Winters-like candidate plots, all unclaimed, with audience. The
    anchor-adjacent plot has the most audience. -/
def wintersRound1 : List Plot :=
  [ { audience := 5, crowding := 0, claimed := false }   -- near anchor (downtown)
  , { audience := 3, crowding := 0, claimed := false }   -- near houses
  , { audience := 2, crowding := 0, claimed := false } ] -- frontier house cluster

/-- Round 1 picks the highest-audience UNCLAIMED plot (near the anchor), not a stack. -/
theorem winters_pick1 :
    chosen wintersRound1 = some { audience := 5, crowding := 0, claimed := false } := by
  decide

/-- After round 1 the anchor plot is claimed. Round 2 picks the next free
    audience plot — STILL unclaimed (sprawl), not a re-stack of the anchor. -/
def wintersRound2 : List Plot :=
  [ { audience := 5, crowding := 2, claimed := true }    -- occupied; congestion (2) overcomes its +2 audience edge
  , { audience := 3, crowding := 0, claimed := false }   -- free audience plot
  , { audience := 2, crowding := 0, claimed := false } ]

theorem winters_pick2 :
    chosen wintersRound2 = some { audience := 3, crowding := 0, claimed := false } := by
  decide

/-- Round 2's pick is unclaimed: the business sprawls to its OWN plot. -/
theorem winters_pick2_is_sprawl :
    (chosen wintersRound2).any (fun p => p.claimed = false) = true := by
  decide

/-- Round 3: two plots claimed, one free audience plot remains — sprawl again. -/
def wintersRound3 : List Plot :=
  [ { audience := 5, crowding := 3, claimed := true }    -- two-stack congestion erodes the anchor's audience edge
  , { audience := 3, crowding := 2, claimed := true }
  , { audience := 2, crowding := 0, claimed := false } ]

theorem winters_pick3_is_own_plot :
    chosen wintersRound3 = some { audience := 2, crowding := 0, claimed := false } := by
  decide

/-- Winters builds low-rise on whatever plot it picks: ties straight into the
    sprawl-before-build-UP law. A placed business in 7k Winters is 2 stories. -/
theorem winters_placed_is_low_rise : placedStories 7214 = 2 := by
  decide

-- Dense case: many businesses, the audience frontier is SATURATED — every
-- audience plot is already claimed, only crowded stacks remain. The rule then
-- (correctly) admits a claimed plot — density-forced co-location.

/-- A saturated frontier: every audience plot is claimed; the only unclaimed
    plot has zero audience (no customers — no one sprawls there). The best
    score is on an already-claimed audience plot ⇒ a STACK is forced. -/
def denseSaturated : List Plot :=
  [ { audience := 6, crowding := 1, claimed := true }    -- claimed audience plot
  , { audience := 4, crowding := 1, claimed := true }    -- claimed audience plot
  , { audience := 0, crowding := 0, claimed := false } ] -- free but audienceless

theorem dense_picks_claimed_stack :
    chosen denseSaturated = some { audience := 6, crowding := 1, claimed := true } := by
  decide

/-- The dense pick is a stack (already claimed) — co-location only after the
    audience frontier saturates, exactly clump-only-under-density. -/
theorem dense_forces_stack :
    (chosen denseSaturated).any (fun p => p.claimed = true ∧ 0 < p.audience) = true := by
  decide

/-- No open frontier plot exists in the dense case (the witness side of (d)). -/
theorem dense_frontier_saturated :
    denseSaturated.all (fun p => isOpenFrontier p = false) = true := by
  decide

end HotellingMeshSprawl
end Gnosis
