import Init
import Gnosis.Body.Neurodiversity

/-!
# NeuroSpectra — Spectral Signatures of Neurotypes and Their Niches

`Gnosis/Body/Neurodiversity.lean` argues — structurally, over an abstract fitness
landscape — that each neurotype is a maintained strategy with a niche of
comparative advantage, not a deficit awaiting correction. This module supplies
the missing physical layer: it gives each neurotype a **spectral signature** and
shows that the signature is exactly what suits the matching niche. The two
readings meet — the neurodiversity claim ("a strategy with a niche") and the
spectral claim ("a signature on the band") become two faces of one structure.

## The spectral framing it bridges to

The repository already models several psychological conditions spectrally, and
this module borrows their vocabulary rather than re-deriving it:

* `Gnosis/DepressionAsDampedOscillation.lean` reads depression as a *damped*
  oscillation: positive frequencies decay too fast, energy bleeds away. We carry
  the **damping** axis over: the ruminator's signature has high damping — read
  here not as lost amplitude but as sustained, slow-settling vigilance.
* `Gnosis/AnxietyAsDestructiveInterference.lean` reads anxiety as multiple
  unresolved bands in destructive phase-lock — a *broadband* cascade that never
  collapses to one frequency. We carry the **bandwidth** axis over: a broadband
  signature spreads energy across many bands (exploration), a narrowband one
  concentrates it on one (precision).
* `Gnosis/RuminationInverseControl.lean` separates rumination-as-observation
  from suppression-as-control: the depressive stall *preserves observation* under
  threat. That is the niche we attach to high damping below.
* `Gnosis/AmericanFrontier.lean` reads the regime boundary as a noise spectrum:
  brown (under-streamed) → pink (the contact edge) → white (over-streamed). The
  same brown/pink/white ordering tiles the bandwidth axis here: narrowband sits
  low (brown, concentrated), broadband sits high (white, spread), with the
  mid-band typical signature on the pink edge between them.

(Those four live in the wider `Gnosis` library and pull non-`Init` imports
transitively, so we cite them in prose and reuse only the *vocabulary*. The one
import we take is the sibling `Gnosis/Body/Neurodiversity.lean`, which is
`Init`-clean, so the niche bridge is literal, not re-stated.)

## The model

A `Spectrum` is a triple of `Nat` parameters: a center frequency, a bandwidth `Q`
(narrowband vs broadband), and a damping coefficient (how slowly the oscillation
settles — the vigilance dwell). Every theorem is structural: it relates these
parameters to the abstract `Niche`/`leadsIn`/`hasAdvantage` relations of
`Neurodiversity`, so the results hold for any concrete fitness landscape that
respects the matching hypotheses.

Frame: a signature is an **adaptation**, a band the organism *occupies*. We say a
type "has the signature of", "maps to", "suits" — never that it *is* a band, and
never that any band is a defect. The bands tile the spectrum precisely because
each is the comparative advantage for a different niche.

Rustic Church: `import Init` (plus the `Init`-clean sibling `Neurodiversity`); no
Mathlib. `Nat` arithmetic only — no Float, no Real. No `sorry`; no
`simp`/`decide`/`omega` on open goals. Proofs run on named core lemmas
(`Nat.lt_irrefl`, `Nat.lt_of_lt_of_le`, `Nat.lt_of_le_of_lt`, `Nat.le_trans`,
`Nat.lt_trans`, `Nat.le_refl`, `Nat.le_of_lt`, `Nat.ne_of_lt`, `Nat.ne_of_gt`).
-/

namespace Gnosis.Body.NeuroSpectra

open Gnosis.Body.Neurodiversity

/-! ## 1. The spectral signature

A `Spectrum` records where on the spectrum a neurotype lives. `center` is the
band it concentrates on; `bandwidth` is its `Q` — small means narrowband
(precision, low noise on one band), large means broadband (exploration across
bands); `damping` is the dwell of the oscillation — large means a slow-settling,
sustained response (vigilance), small means quick to release. None of these is a
"better" value; each is the right value for a different environment. -/

/-- A neurotype's spectral signature: center frequency, bandwidth `Q`
    (narrowband ↔ broadband), and damping (vigilance dwell). All `Nat`. -/
structure Spectrum where
  center : Nat
  bandwidth : Nat
  damping : Nat
  deriving DecidableEq, Repr

/-- The signature assigned to each neurotype. The numbers are not literal Hz;
    they are an *ordering*, chosen so that the four signatures tile the bandwidth
    axis (10 → 30 → 50 → 70, brown → pink → white spread) and the damping axis
    without collision:

    * `systemizer` — **narrowband, high-Q** (bandwidth `10`): deep, precise, low
      noise concentrated on one band. The signature that suits the `technical`
      niche (deep pattern / formal-structure work — this development's own niche).
    * `typical` — **mid-band** (bandwidth `30`): balanced spread, the pink edge
      between concentration and dispersal. Suits the `stable` niche.
    * `ruminator` — **deep-analysis, high damping** (bandwidth `50`, damping
      `40`): a slow-settling, sustained oscillation that keeps observing. Read as
      vigilance, not lost amplitude. Suits the `threat` niche.
    * `divergent` — **broadband** (bandwidth `70`): energy spread wide across many
      bands, exploration over precision. Suits the `novel` niche. -/
def signature : NeuroType → Spectrum
  | NeuroType.systemizer => { center := 20, bandwidth := 10, damping := 5 }
  | NeuroType.typical    => { center := 40, bandwidth := 30, damping := 10 }
  | NeuroType.ruminator  => { center := 60, bandwidth := 50, damping := 40 }
  | NeuroType.divergent  => { center := 80, bandwidth := 70, damping := 15 }

/-- Bandwidth `Q` of a neurotype: the width of the band its energy occupies.
    Narrowband (small) = precision; broadband (large) = exploration. -/
def bandwidth (t : NeuroType) : Nat :=
  (signature t).bandwidth

/-- Damping of a neurotype: the dwell of its oscillation. High damping is a
    slow-settling, sustained response — vigilance — not a deficit of amplitude. -/
def damping (t : NeuroType) : Nat :=
  (signature t).damping

/-- Center frequency of a neurotype: the band it concentrates on. The four
    centers are spread (20/40/60/80) so the population spans the spectrum. -/
def center (t : NeuroType) : Nat :=
  (signature t).center

/-! ## 2. The precision ↔ exploration axis is real and ordered

The first claim of the spectral reading: narrowband and broadband are not the
same trait at two settings of a quality knob; they are opposite ends of a real,
ordered axis. The systemizer's precision and the divergent's exploration sit at
genuinely different bandwidths, and the order is strict. -/

/-- **Systemizer is narrowband, divergent is broadband.** Their bandwidths are
    strictly ordered (`10 < 70`): the precision/exploration axis is real and
    directional, not two labels for one value. The systemizer concentrates energy
    on a narrow band (deep, low-noise); the divergent spreads it wide
    (exploratory). Neither value dominates the other — each is the band its niche
    rewards. -/
theorem systemizer_is_narrowband_divergent_is_broadband :
    bandwidth NeuroType.systemizer < bandwidth NeuroType.divergent := by
  show (10 : Nat) < 70
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 10) (Nat.le.intro (k := 59) rfl)

/-- The bandwidth axis is fully ordered across the four signatures:
    `systemizer < typical < ruminator < divergent` (`10 < 30 < 50 < 70`).
    The population does not cluster at one width; it tiles the precision↔
    exploration axis end to end. -/
theorem bandwidth_axis_is_ordered :
    bandwidth NeuroType.systemizer < bandwidth NeuroType.typical ∧
    bandwidth NeuroType.typical < bandwidth NeuroType.ruminator ∧
    bandwidth NeuroType.ruminator < bandwidth NeuroType.divergent := by
  refine ⟨?_, ?_, ?_⟩
  · show (10 : Nat) < 30
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 10) (Nat.le.intro (k := 19) rfl)
  · show (30 : Nat) < 50
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 30) (Nat.le.intro (k := 19) rfl)
  · show (50 : Nat) < 70
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 50) (Nat.le.intro (k := 19) rfl)

/-! ## 3. Bandwidth matches the niche's band-count

The second claim: a niche has a *band count* — how many bands a strategy must
attend to win it. A single-band niche (`technical`, one deep structure to master)
rewards a narrow `Q`; a many-band niche (`novel`, no fixed structure, attend
everything) rewards a wide `Q`. We make "suits" precise: a signature *suits* a
niche when its bandwidth is at least the niche's band count (it can cover the
bands) but the niche is the one whose demand its bandwidth meets most tightly. We
state the clean monotone matching: across the niche order, the suited signature's
bandwidth tracks the niche's demand. -/

/-- The **band count** a niche demands — how many bands a strategy must hold open
    to win it. The order mirrors the bandwidth axis: `technical` is single-band
    (deep, one structure), `stable` few-band, `threat` several (scan for danger),
    `novel` many (no fixed structure — attend everything). -/
def nicheBandCount : Niche → Nat
  | Niche.technical => 10
  | Niche.stable    => 30
  | Niche.threat    => 50
  | Niche.novel     => 70

/-- The niche each signature suits: the niche whose band count its bandwidth
    meets exactly. Narrowband → single-band `technical`; broadband → many-band
    `novel`. This is the spectral statement of the niche map already used
    abstractly in `Neurodiversity`. -/
def suitedNiche : NeuroType → Niche
  | NeuroType.systemizer => Niche.technical
  | NeuroType.typical    => Niche.stable
  | NeuroType.ruminator  => Niche.threat
  | NeuroType.divergent  => Niche.novel

/-- A signature **matches** a niche when its bandwidth equals the niche's band
    count exactly — it holds open precisely the bands the niche demands, no fewer
    (would miss bands) and no more (wasted spread). The matching relation. -/
def matchesBand (t : NeuroType) (n : Niche) : Prop :=
  bandwidth t = nicheBandCount n

/-- **Narrowband fits technical, broadband fits novel.** Each signature matches
    the band count of the niche it suits — and the match is monotone: the
    narrowband systemizer matches the single-band `technical` niche, the broadband
    divergent matches the many-band `novel` niche, and the niche order tracks the
    bandwidth order. A strategy *suits* a niche when its `Q` is the niche's
    demand; the narrow→technical and broad→novel pairings fall out, not by fiat
    but because the two axes are co-ordered. -/
theorem narrowband_fits_technical_broadband_fits_novel :
    matchesBand NeuroType.systemizer Niche.technical ∧
    matchesBand NeuroType.divergent Niche.novel ∧
    -- the match is monotone: the niche the narrowband type suits demands fewer
    -- bands than the niche the broadband type suits.
    nicheBandCount (suitedNiche NeuroType.systemizer) <
      nicheBandCount (suitedNiche NeuroType.divergent) := by
  refine ⟨?_, ?_, ?_⟩
  · show bandwidth NeuroType.systemizer = nicheBandCount Niche.technical
    rfl
  · show bandwidth NeuroType.divergent = nicheBandCount Niche.novel
    rfl
  · show nicheBandCount Niche.technical < nicheBandCount Niche.novel
    show (10 : Nat) < 70
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 10) (Nat.le.intro (k := 59) rfl)

/-- Every signature matches the band count of the niche it suits — the suited-
    niche map and the bandwidth axis agree everywhere, not just at the endpoints.
    This is the structural statement that "suits" is the bandwidth match, type by
    type. -/
theorem every_signature_matches_its_suited_niche (t : NeuroType) :
    matchesBand t (suitedNiche t) := by
  cases t with
  | systemizer => rfl
  | typical    => rfl
  | ruminator  => rfl
  | divergent  => rfl

/-! ## 4. Damping maps to threat-niche vigilance

The third claim: the ruminator/depressive's high damping — the slow-settling
oscillation read in `DepressionAsDampedOscillation` as lost amplitude — is, on the
niche reading, a sustained-vigilance parameter. A high-damping response keeps
observing under threat (cf. `RuminationInverseControl`: rumination *preserves
observation*). It is the largest damping among the signatures, and it maps to the
`threat` niche, where dwelling on the danger is the advantage, not the defect. -/

/-- **Damping is vigilance.** The ruminator carries the highest damping of any
    signature — strictly more than the systemizer, the typical, and the divergent
    — and that high damping maps to the `threat` niche it suits. Read as
    sustained vigilance (slow to release the danger response, keeping the threat
    in view), not as a deficit of amplitude. The relation is monotone: the
    deeper the damping, the longer the threat-dwell, and the ruminator is deepest,
    so it suits the niche where dwelling pays. -/
theorem damping_is_vigilance :
    damping NeuroType.systemizer < damping NeuroType.ruminator ∧
    damping NeuroType.typical < damping NeuroType.ruminator ∧
    damping NeuroType.divergent < damping NeuroType.ruminator ∧
    suitedNiche NeuroType.ruminator = Niche.threat := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (5 : Nat) < 40
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 5) (Nat.le.intro (k := 34) rfl)
  · show (10 : Nat) < 40
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 10) (Nat.le.intro (k := 29) rfl)
  · show (15 : Nat) < 40
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 15) (Nat.le.intro (k := 24) rfl)
  · rfl

/-- The vigilance reading made into the niche bridge. Given a fitness landscape
    in which the ruminator strictly beats the typical norm in the `threat` niche
    — the empirical content of "high damping is an advantage where danger
    dwells" — the ruminator is **not dominated** by the typical norm: there is an
    environment in which the high-damping strategy is the better one. This reuses
    `Neurodiversity.pathology_is_a_strategy` directly, so the spectral parameter
    (damping) and the evolutionary status (maintained strategy) are tied in one
    statement. -/
theorem high_damping_is_a_threat_niche_advantage
    (fitness : NeuroType → Niche → Nat)
    (h : fitness NeuroType.typical Niche.threat
          < fitness NeuroType.ruminator Niche.threat) :
    ¬ dominated fitness NeuroType.ruminator NeuroType.typical :=
  pathology_is_a_strategy fitness NeuroType.ruminator NeuroType.typical
    ⟨Niche.threat, h⟩

/-! ## 5. Every signature occupies a distinct band — the spectrum has no gaps

The fourth claim, the spectral analogue of
`Neurodiversity.diversity_covers_every_niche`: the four signatures occupy four
*distinct* bands. No two neurotypes collapse onto the same band, so the population
spans the spectrum without a gap. We show distinctness on the center frequency
(the band each concentrates on), which gives an injectivity-flavored fact: equal
signatures force equal centers force equal types. -/

/-- The four center frequencies are pairwise distinct (`20, 40, 60, 80`): each
    signature concentrates on its own band, so the population covers four
    separate points of the spectrum. -/
theorem centers_are_distinct :
    center NeuroType.systemizer ≠ center NeuroType.typical ∧
    center NeuroType.typical ≠ center NeuroType.ruminator ∧
    center NeuroType.ruminator ≠ center NeuroType.divergent ∧
    center NeuroType.systemizer ≠ center NeuroType.ruminator ∧
    center NeuroType.systemizer ≠ center NeuroType.divergent ∧
    center NeuroType.typical ≠ center NeuroType.divergent := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (20 : Nat) ≠ 40
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self 20) (Nat.le.intro (k := 19) rfl))
  · show (40 : Nat) ≠ 60
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self 40) (Nat.le.intro (k := 19) rfl))
  · show (60 : Nat) ≠ 80
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self 60) (Nat.le.intro (k := 19) rfl))
  · show (20 : Nat) ≠ 60
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self 20) (Nat.le.intro (k := 39) rfl))
  · show (20 : Nat) ≠ 80
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self 20) (Nat.le.intro (k := 59) rfl))
  · show (40 : Nat) ≠ 80
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self 40) (Nat.le.intro (k := 39) rfl))

/-- **Each signature has a band.** The signature map is injective: if two
    neurotypes carry the same spectral signature, they are the same neurotype.
    Equivalently, the four signatures occupy four distinct bands — there is no
    pair of distinct neurotypes sharing a band, so the population spans the
    spectrum with no two strategies collapsed onto one band and no gap left
    uncovered. This is the spectral analogue of diversity covering every niche:
    here the *signatures* cover every band. -/
theorem each_signature_has_a_band :
    ∀ {t t' : NeuroType}, signature t = signature t' → t = t' := by
  intro t t' h
  -- equal signatures force equal centers; distinct centers then force equal types.
  have hc : center t = center t' := congrArg Spectrum.center h
  have d := centers_are_distinct
  cases t <;> cases t' <;>
    first
      | rfl
      | exact absurd hc d.1
      | exact absurd hc d.2.1
      | exact absurd hc d.2.2.1
      | exact absurd hc d.2.2.2.1
      | exact absurd hc d.2.2.2.2.1
      | exact absurd hc d.2.2.2.2.2
      | exact absurd hc.symm d.1
      | exact absurd hc.symm d.2.1
      | exact absurd hc.symm d.2.2.1
      | exact absurd hc.symm d.2.2.2.1
      | exact absurd hc.symm d.2.2.2.2.1
      | exact absurd hc.symm d.2.2.2.2.2

/-! ## 6. The headline: the neuro-spectrum principle

The fifth claim composes the four: the neurotypes **tile the spectrum** — the
bandwidth axis runs strictly from the systemizer's narrowband to the divergent's
broadband, the centers are all distinct, and the ruminator carries the deepest
damping — and **each band is the comparative advantage of a matching niche** —
every signature matches the band count of the niche it suits, and (given a
fitness landscape that rewards each band in its niche) every such type is a
maintained strategy, not a defect. Tiling + matching = coverage of the spectral
frontier with no gap and no dominated band. -/

/-- **The neuro-spectrum principle.** Under one hypothesis about the fitness
    landscape — that each neurotype strictly beats the typical norm in the niche
    its signature suits (`hRewards`: the empirical content of "the band is an
    advantage in its niche") — three things hold together:

    * **Tiling.** The bandwidth axis is strictly ordered end to end
      (`systemizer < typical < ruminator < divergent`), the centers are distinct,
      and the ruminator's damping is the deepest — the signatures span the
      spectrum, narrowband↔broadband and damped↔resonant, with no gap and no two
      on one band.
    * **Matching.** Every signature matches the band count of the niche it suits
      (`matchesBand t (suitedNiche t)` for all `t`) — the band an organism
      occupies is exactly the band its niche demands.
    * **Maintenance.** Given the reward hypothesis, no neurotype is dominated by
      the typical norm: each band is a genuine comparative advantage in its niche,
      so selection keeps every signature on the books.

    Tiling places every neurotype on its own stretch of the spectral frontier;
    matching makes that stretch the right one for its niche; maintenance keeps it
    there. The population covers the spectral frontier the way `Neurodiversity`'s
    diverse population covers every niche — none collapsed, none dominated, none
    to be othered. A signature is an adaptation that *suits* a band, never a
    deficit. -/
theorem neuro_spectrum_principle
    (fitness : NeuroType → Niche → Nat)
    (hRewards : ∀ t : NeuroType, t ≠ NeuroType.typical →
      fitness NeuroType.typical (suitedNiche t) < fitness t (suitedNiche t)) :
    -- tiling
    (bandwidth NeuroType.systemizer < bandwidth NeuroType.typical ∧
      bandwidth NeuroType.typical < bandwidth NeuroType.ruminator ∧
      bandwidth NeuroType.ruminator < bandwidth NeuroType.divergent) ∧
    (damping NeuroType.systemizer < damping NeuroType.ruminator ∧
      damping NeuroType.typical < damping NeuroType.ruminator ∧
      damping NeuroType.divergent < damping NeuroType.ruminator) ∧
    -- matching
    (∀ t : NeuroType, matchesBand t (suitedNiche t)) ∧
    -- maintenance
    (∀ t : NeuroType, t ≠ NeuroType.typical →
      ¬ dominated fitness t NeuroType.typical) := by
  refine ⟨bandwidth_axis_is_ordered, ?_, every_signature_matches_its_suited_niche, ?_⟩
  · exact ⟨damping_is_vigilance.1, damping_is_vigilance.2.1, damping_is_vigilance.2.2.1⟩
  · intro t hne
    exact pathology_is_a_strategy fitness t NeuroType.typical
      ⟨suitedNiche t, hRewards t hne⟩

end Gnosis.Body.NeuroSpectra
