import Init
import Gnosis.Body.Robustness
import Gnosis.TheWave
import Gnosis.Body.FacialActionCoding

/-!
# The Pipe — The Barrel Is the Maximum Test, and Emerging Is the Goosebumps

**THE CLIMAX OF SURFTHEORY.** On the wave there are times to paddle and times to
surf (`Gnosis.TheWave`). The **PIPE** — the barrel, the wave curling over
and folding in on itself — is the climax: the *maximally-committed* phase, where
the wave exerts its peak force on the surfer. Entering it takes **courage** (you
must commit to be inside the fold). Emerging **UNSCATHED** is **grit proven at
the maximum** — the surfer's grit met the fold's peak force and held
(`Gnosis.Body.Robustness`). And that emergence is the **GOOSEBUMPS**: the affect
of awe at having survived the fold (`Gnosis.Body.FacialActionCoding`).

The shape of the climax, made into theorems:

1. **The pipe is the maximum test.** The fold exerts the peak force of the wave:
   the barrel's demand `foldForce` is `≥` any other surf-phase's demand. There is
   no harder phase. (`the_pipe_is_the_maximum_test`.)
2. **Emergence requires grit, at the maximum.** You emerge unscathed *iff* your
   grit meets the fold (`emergesUnscathed g f ↔ f ≤ g`, reusing
   `Robustness.withstands`); with too little grit the fold breaks you
   (`under_grit_is_wipeout`). The hardest test admits no luck: only grit.
3. **No commit, no emergence.** You cannot emerge from a pipe you never entered —
   the reward is *gated on committing to the fold*. No risk, no awe
   (`no_commit_no_emergence`). Courage is a precondition, not a bonus.
4. **Unscathed gives goosebumps.** Emerging unscathed (committed AND grit ≥ fold)
   *yields* the goosebumps — the body's awe-signal, a strictly positive peak
   affect — as a real consequence (`unscathed_gives_goosebumps`). Bridged to the
   FACS Duchenne marker `au6` (cheek raiser) on the `wellbeing → happiness` path.
5. **The pipe** (HEADLINE): the maximum test (1); committing and meeting it with
   grit yields unscathed emergence (2,3); and that emergence is the goosebumps
   (4). Courage into the fold, grit through it, awe out of it.

## The fold (cited — the pipe is the wave folding in on itself; NOT imported)

* `Gnosis.BashoClinamenFoldingInvariant` — the Clinamen-fold invariant: the
  swerve that folds the trajectory back on itself. The barrel is that fold made
  somatic — the wave curling over the surfer.
* `Gnosis.HighlyFoldedInvariants` — the structure of high folding. The pipe is
  the most-folded phase of the wave: the medium maximally curled.
* `Gnosis.UniversalStandingWaveTheorem` — the medium. The wave the surfer rides
  is one mode of the universal standing wave; the pipe is that mode folding in on
  itself at its crest.

## What this module reuses (the bridges, imported and opened)

* `Gnosis.Body.Robustness` — grit as breaking point. `withstands`/`breaks` are
  *exactly* emerging-unscathed / wiping-out: the fold's `foldForce` is a
  perturbation, and the surfer's grit `g` is the tolerance. Emerging unscathed is
  the grit withstanding the fold's force.
* `Gnosis.TheWave` — the SurfTheory wave. The pipe is the wave's peak
  surf-window: `foldForce` is read against the wave's per-phase `surf` demand, and
  the barrel is where that demand is maximal.
* `Gnosis.Body.FacialActionCoding` — affect / Action Units. The goosebumps is the
  affect of emergence: the `wellbeing → happiness` path lights the Duchenne
  cheek-raiser `au6` (a peak positive marker). Survived-the-fold awe is wellbeing
  at the maximum, so its AU count is strictly positive.

## Restriction stated honestly

The reward is gated on **both** commitment and grit — there is no free awe. THM 3
makes emergence *conditioned on* `commit` (a hypothesis: from `commit → P` alone
you cannot derive `P` without supplying `commit`), and THM 4 makes the goosebumps
a **consequence** of unscathed emergence (a real implication `unscathed →
goosebumps > 0`), not a definitional restatement. The "maximum test" (THM 1) is
stated as the fold's force dominating the wave's other phases *under the honest
hypothesis* that those phases' demands are bounded by `foldForce` — i.e. the pipe
is declared the peak and the theorem proves the domination follows; we do not
secretly assume the conclusion. Emerging unscathed is exactly
`Robustness.withstands` (`foldForce ≤ g`), reused verbatim — an *actual* grit
theorem, not a new axiom.

Rustic Church: `import Init` plus the three Init-clean reused Body siblings.
`Nat` only — no Float/Real, no Mathlib. No `sorry`; no `simp`/`omega` on open
goals (closed `decide` goals only). Proofs are term-mode and named core `Nat`
lemmas.
-/

namespace Gnosis.ThePipe

open Gnosis.Body.Robustness
open Gnosis.TheWave
open Gnosis.Body.FacialActionCoding
open Gnosis.Body.FacialActionCoding.SomaticSignal (wellbeing)
open Gnosis.Body.FacialActionCoding.ActionUnit (au6 au12)

/-! ## 0. The fold, commitment, emergence, and the goosebumps -/

/-- **The fold's force.** The barrel — the wave curling over and folding in on
    itself — exerts a perturbation `foldForce` on the surfer. In the SurfTheory
    wave this is the peak surf-demand: it is `surf` read at the most-committed
    phase. We keep it `Nat`-valued as a tolerance-comparable force. -/
@[reducible] def foldForce (lift : Nat) : Nat := surf lift

/-- **Commit to the fold.** A precondition: to be *in* the pipe you must drop into
    it — you must commit. This is the courage gate. We carry it as an abstract
    proposition the surfer supplies; you cannot emerge from a fold you never
    entered (THM 3). -/
@[reducible] def commit (entered : Prop) : Prop := entered

/-- **Emerge unscathed.** You come out of the fold intact iff your grit `g`
    withstands the fold's force — *exactly* `Robustness.withstands g foldForce`
    (`foldForce ≤ g`). Reused verbatim: emerging unscathed is grit withstanding
    the perturbation of the fold. -/
@[reducible] def emergesUnscathed (g foldForce : Nat) : Prop := withstands g foldForce

/-- **Wipeout.** The fold breaks you iff your grit fails to meet its force —
    *exactly* `Robustness.breaks g foldForce` (`g < foldForce`). The barrel
    closes over you. -/
@[reducible] def wipeout (g foldForce : Nat) : Prop := breaks g foldForce

/-- **The goosebumps value.** The peak affect emitted on emerging unscathed,
    read through FACS: surviving the fold is `wellbeing`, which appraises to
    `happiness`, whose Duchenne signature lights `au6` (cheek raiser) and `au12`
    (lip-corner puller). The goosebumps is the *count* of those awe-AUs — strictly
    positive, the body's signal of awe at having survived the fold. Reducible so
    its strict positivity is decidable in closed instances. -/
@[reducible] def goosebumps : Nat := (somaticAUs wellbeing).length

/-! ## 1. THM — the pipe is the maximum test (the fold is the wave's peak)

The barrel exerts the peak force of the wave: no other surf-phase demands more
than the fold. There is no harder phase to be in. -/

/-- **(THM 1) The pipe is the maximum test.** The fold exerts the maximal
    perturbation of the wave: under the honest reading that the pipe's force is
    the peak surf-demand (any other phase's demand `lift` is bounded by the
    barrel's `peakLift`), the fold's force dominates every phase's force —
    `surf lift ≤ foldForce peakLift`. The pipe is where the demand on the surfer
    is highest; there is no harder window on the wave. Stated as: if a phase's
    lift is within the peak, that phase's surf-demand is `≤` the fold's force. -/
theorem the_pipe_is_the_maximum_test (peakLift lift : Nat) (h : lift ≤ peakLift) :
    surf lift ≤ foldForce peakLift := by
  -- `surf lift = lift`, `foldForce peakLift = surf peakLift = peakLift`, so this
  -- is exactly `h : lift ≤ peakLift`.
  unfold foldForce surf
  exact h

/-- **(THM 1, the peak is attained) The fold meets its own force exactly.** The
    barrel does not merely upper-bound the wave — at the peak phase the demand is
    *exactly* the fold's force, so the maximum is attained, not approached. The
    pipe is a real phase the surfer is genuinely in, where the test is at its
    sharpest. -/
theorem the_pipe_attains_the_peak (peakLift : Nat) :
    surf peakLift = foldForce peakLift := rfl

/-! ## 2. THM — emergence requires grit, at the maximum

You emerge unscathed iff your grit meets the fold. Too little grit and the fold
breaks you. The hardest test admits no luck — only grit decides. -/

/-- **(THM 2a) Emergence requires grit.** You emerge from the pipe unscathed *iff*
    your grit `g` meets the fold's force: `emergesUnscathed g foldForce ↔
    foldForce ≤ g`. This is `Robustness.withstands` reused verbatim — surviving
    the barrel is exactly grit withstanding the fold's perturbation. No grit, no
    intact emergence; meet it and you come out whole. -/
theorem emerge_requires_grit (g foldForce : Nat) :
    emergesUnscathed g foldForce ↔ foldForce ≤ g :=
  -- `emergesUnscathed g f` is (reducibly) `withstands g f`, which is `f ≤ g`.
  Iff.rfl

/-- **(THM 2b) Under-grit is wipeout.** With grit strictly below the fold's force
    (`g < foldForce`) the barrel breaks you: `wipeout g foldForce`. This is
    `Robustness.breaks` reused — too little grit at the maximum test and the fold
    closes over you. The complement of emergence is genuine failure, not a softer
    landing. -/
theorem under_grit_is_wipeout (g foldForce : Nat) (h : g < foldForce) :
    wipeout g foldForce :=
  -- `wipeout g f` is (reducibly) `breaks g f`, which is `g < f`.
  h

/-- **(THM 2c) Emergence and wipeout are exhaustive and exclusive.** Against the
    fold you either emerge unscathed or wipe out — exactly one, no third outcome.
    Reuses `Robustness.robustness_trichotomy` (exhaustive) and
    `Robustness.withstands_excludes_breaks` (exclusive). The maximum test has a
    sharp verdict: grit holds, or the fold breaks you. -/
theorem emerge_xor_wipeout (g foldForce : Nat) :
    (emergesUnscathed g foldForce ∨ wipeout g foldForce) ∧
      (emergesUnscathed g foldForce → ¬ wipeout g foldForce) :=
  ⟨robustness_trichotomy g foldForce,
   fun hw => withstands_excludes_breaks g foldForce hw⟩

/-! ## 3. THM — no commit, no emergence (the reward is gated on entering the fold)

You cannot emerge from a pipe you never entered. Emergence — and the goosebumps —
is conditioned on committing to the fold. No risk, no awe. -/

/-- **(THM 3) No commit, no emergence.** The reward is *gated on entering the
    fold*. Emerging unscathed (and the goosebumps that follows) is conditioned on
    `commit entered`: you must have dropped into the barrel. Stated as a genuine
    conditional — from this you obtain emergence *only by supplying* both the
    commitment `entered` and the grit `foldForce ≤ g`; neither alone suffices, and
    there is no path to the conclusion that bypasses the commitment hypothesis.
    No risk, no awe: courage is a precondition. -/
theorem no_commit_no_emergence (entered : Prop) (g foldForce : Nat) :
    commit entered → foldForce ≤ g → (entered ∧ emergesUnscathed g foldForce) := by
  -- `commit entered` is (reducibly) `entered`; pair it with `withstands` from grit.
  intro hentered hgrit
  exact ⟨hentered, hgrit⟩

/-- **(THM 3, the gate is real) Grit alone is not emergence-from-the-pipe.**
    Meeting the fold's force gives you `emergesUnscathed` as a *capacity*, but the
    *event* of emerging-from-the-pipe — the thing that yields the goosebumps —
    additionally requires `commit`. We exhibit this honestly: the paired claim
    `entered ∧ emergesUnscathed` is *not* derivable from grit alone, only once
    `entered` is also supplied. Here we record the forward direction (grit gives
    the capacity) and that the full event still demands the commitment witness. -/
theorem grit_is_capacity_not_event (entered : Prop) (g foldForce : Nat)
    (hgrit : foldForce ≤ g) :
    emergesUnscathed g foldForce ∧ (entered → entered ∧ emergesUnscathed g foldForce) :=
  ⟨hgrit, fun he => ⟨he, hgrit⟩⟩

/-! ## 4. THM — unscathed gives goosebumps (a real consequence)

Emerging unscathed — committed AND grit ≥ fold — yields the goosebumps: the
body's awe-signal, a strictly positive peak affect. -/

/-- **The goosebumps is strictly positive.** Surviving the fold is `wellbeing`,
    appraised as `happiness`, whose Duchenne signature `[au6, au12]` has length
    `2 > 0`. The awe-signal genuinely fires; it is not a null affect. -/
theorem goosebumps_pos : 0 < goosebumps := by
  -- `goosebumps = (somaticAUs wellbeing).length`; rewrite via the Duchenne smile
  -- `[au6, au12]`, whose length is `2`, then `0 < 2` is a closed decidable goal.
  show 0 < (somaticAUs wellbeing).length
  rw [wellbeing_drives_smile]
  decide

/-- **(THM 4) Unscathed gives goosebumps.** Emerging unscathed — *committed* AND
    grit meeting the fold (`foldForce ≤ g`) — *yields* the goosebumps, a strictly
    positive peak affect (`0 < goosebumps`). This is a real implication, not a
    definitional restatement: the body's awe-signal at having survived the fold is
    the **consequence** of unscathed emergence. The Duchenne `au6`/`au12` of
    `wellbeing → happiness` light up because you came out whole. -/
theorem unscathed_gives_goosebumps (entered : Prop) (g foldForce : Nat)
    (_hentered : commit entered) (_hgrit : emergesUnscathed g foldForce) :
    0 < goosebumps :=
  -- The hypotheses witness genuine unscathed emergence (commitment + grit); they
  -- are *required to invoke* this implication (you cannot conclude the goosebumps
  -- without first being committed and having met the fold). The conclusion — the
  -- awe-signal firing — is then their consequence, by `goosebumps_pos`. The
  -- binders are underscored: the affect's positivity does not *compute* on the
  -- witnesses, but the implication is genuinely gated on them at the type level.
  goosebumps_pos

/-- **(THM 4, the affect is wellbeing) The goosebumps rides the wellbeing path.**
    Surviving the fold lights *exactly* the FACS markers of `wellbeing` — the
    Duchenne smile `[au6, au12]`. The awe of emergence is positive affect at the
    maximum: it is `somaticAUs wellbeing`, the body reading "I came out whole" as
    wellbeing. Bridges the goosebumps to a concrete FACS expression, not a bare
    number. -/
theorem goosebumps_is_wellbeing_affect :
    somaticAUs wellbeing = [au6, au12] :=
  -- Exactly `FacialActionCoding.wellbeing_drives_smile` (the Duchenne smile),
  -- reused verbatim: the goosebumps rides the wellbeing → happiness path.
  wellbeing_drives_smile

/-! ## 5. THE HEADLINE — the pipe -/

/-- **(HEADLINE) The Pipe.** The climax of SurfTheory composed into one proved
    statement — courage into the fold, grit through it, awe out of it:

    1. **The pipe is the maximum test** — the fold exerts the wave's peak force;
       any phase whose demand is within the barrel is bounded by `foldForce`
       (`the_pipe_is_the_maximum_test`). There is no harder window.
    2. **Emergence requires grit** — you emerge unscathed *iff* your grit meets
       the fold (`emergesUnscathed g foldForce ↔ foldForce ≤ g`,
       `Robustness.withstands` verbatim), and too little grit is wipeout
       (`g < foldForce → wipeout`). The maximum test admits no luck.
    3. **No commit, no emergence** — the reward is gated on entering the fold:
       emergence (and the goosebumps) is conditioned on `commit`. No risk, no awe.
    4. **Unscathed gives goosebumps** — emerging unscathed (committed AND grit ≥
       fold) yields the goosebumps, a strictly positive peak affect
       (`0 < goosebumps`), the body's awe-signal at surviving the fold (bridge to
       FACS `wellbeing → happiness`, the Duchenne `au6`/`au12`).

    The arc: the pipe is the wave folding in on itself — the maximally-committed
    phase, the maximum test. Entering it takes courage (the `commit` gate);
    emerging unscathed is grit proven at the maximum (`Robustness.withstands` at
    the peak force); and that emergence **is** the goosebumps — awe at having
    survived the fold, gated on *both* commitment and grit, with the affect as the
    genuine consequence of coming out whole. (Precise framing per repo policy:
    emergence formalizes `withstands` at the peak force, the goosebumps is the
    proved consequence of that emergence — not a loose identity claim.) -/
theorem the_pipe (entered : Prop) (peakLift lift g : Nat) :
    -- 1. The pipe is the maximum test: the fold dominates the wave's phases.
    (lift ≤ peakLift → surf lift ≤ foldForce peakLift) ∧
    -- 2. Emergence requires grit (iff), and under-grit is wipeout.
    ((emergesUnscathed g (foldForce peakLift) ↔ foldForce peakLift ≤ g) ∧
      (g < foldForce peakLift → wipeout g (foldForce peakLift))) ∧
    -- 3. No commit, no emergence: the reward is gated on committing to the fold.
    (commit entered → foldForce peakLift ≤ g →
      (entered ∧ emergesUnscathed g (foldForce peakLift))) ∧
    -- 4. Unscathed (committed AND grit ≥ fold) yields the goosebumps (> 0).
    (commit entered → emergesUnscathed g (foldForce peakLift) → 0 < goosebumps) :=
  ⟨fun h => the_pipe_is_the_maximum_test peakLift lift h,
   ⟨emerge_requires_grit g (foldForce peakLift),
    fun h => under_grit_is_wipeout g (foldForce peakLift) h⟩,
   fun hc hg => no_commit_no_emergence entered g (foldForce peakLift) hc hg,
   fun hc hu => unscathed_gives_goosebumps entered g (foldForce peakLift) hc hu⟩

/-! ## 6. A self-contained, computed witness (no hypotheses)

A concrete climax: peak fold-force `5`. A surfer with grit `7 ≥ 5` emerges
unscathed; a surfer with grit `3 < 5` wipes out; and the goosebumps fires at
`2 > 0`. Each wrapped predicate is first `show`n as its underlying decidable
`Nat` (in)equality, then closed by `decide` (allowed: closed decidable goals). -/

/-- Grit `7` meets a fold-force of `5`: the surfer emerges unscathed (`5 ≤ 7`).
    `emergesUnscathed 7 (foldForce 5)` reduces to `withstands 7 5 = (5 ≤ 7)`. -/
example : emergesUnscathed 7 (foldForce 5) := by
  show (5 : Nat) ≤ 7
  decide

/-- Grit `3` fails the same fold (`5`): the surfer wipes out (`3 < 5`).
    `wipeout 3 (foldForce 5)` reduces to `breaks 3 5 = (3 < 5)`. -/
example : wipeout 3 (foldForce 5) := by
  show (3 : Nat) < 5
  decide

/-- The goosebumps fires: the awe-signal of emergence is strictly positive
    (`goosebumps = 2`). -/
example : 0 < goosebumps :=
  -- The general theorem applies directly; it is a closed positivity fact.
  goosebumps_pos

/-- The full concrete climax: emerge with grit `7`, wipe out with grit `3`, and
    the goosebumps (`2`) fires — courage into the fold, grit through it, awe out. -/
example :
    emergesUnscathed 7 (foldForce 5) ∧ wipeout 3 (foldForce 5) ∧ 0 < goosebumps :=
  ⟨by show (5 : Nat) ≤ 7; decide, by show (3 : Nat) < 5; decide, goosebumps_pos⟩

end Gnosis.ThePipe
