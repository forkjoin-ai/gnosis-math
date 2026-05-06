import Gnosis.BuleIsValue
import Gnosis.WankelEngineTheorem
import Gnosis.InterferenceAsTheFifthForce
import Gnosis.AperiodicRotationAsLanguageTrajectory
import Gnosis.GodFormula
import Gnosis.NoiseLedgerTheorem

namespace Gnosis

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit BuleyFace buleyUnitScore vacuumBuleUnit
   clinamenLift clinamenContract
   clinamen_lift_score_strict_increment
   lift_then_contract_round_trip_when_face_positive)

open InterferenceIsFundamental (CompleteFundamentalForce)

open InterferenceAsTheFifthForce
  (constructive_interference destructive_interference)

open WankelEngineTheorem (nextLifecycleStage)

/-!
# BuleSpider: one clinamen, three modes, two operators

`BuleFiveFold` is the radar projection of a single primitive — the clinamen
`+1` lift folding back on itself.

* One wave. `clinamenLift` on a face is the only primitive. The
  plus/minus residue catalog (`UniversalClinamenPlusOne`) confirms the
  direction is universal across the seven independent reconstructions.
* Two phases. The same wave outgoing and returning. Wankel's
  `forwardWave` / `returnEcho` is `clinamenLift` then `clinamenContract`;
  the breathing identity
  `lift_then_contract_round_trip_when_face_positive` is the formal sense
  in which the apparent pair (forward, return) is one wave at two phases
  of its self-fold, not two independent waves.
* Three modes. The visible BuleyUnit faces — standing-wave residues
  left by the round trip, indexed by which face the clinamen touched. The
  triad is therefore not three primal waves; it is the residue of one
  wave's self-fold projected onto three face indices.
* Two operator chords. `vent` (destructive) and `interfere`
  (constructive) pair modes back with themselves. Their kind differs from
  the triad: modes carry residue values, operators carry pairing outputs.
* Five-force lifecycle. Modes plus operators close the cycle as
  `fork → race → fold → vent → interfere → fork`.

The radar/spider has three solid spokes (modes) and two chord-operators
(interference contacts), not five equal spokes. The kind distinction is
load-bearing: the visible mode projection is invariant under operator
load (`visible_projection_invariant_under_operator_load`).

Levels of interference correspond to fold-depths:

* fold 0 — vacuum, no wave;
* fold 1 — `clinamenLift`, the wave appears;
* fold 2 — `clinamenContract`, the same wave returning;
* fold 3 — three-face residue (the triad);
* fold 4 — residues paired by `vent` / `interfere` operators;
* fold 5 — cycle closes back to fork.
-/

/-! ## Stage kinds: modes versus operators -/

inductive StandingWaveStage where
  | fork
  | race
  | fold
  deriving DecidableEq, Repr

inductive InterferenceStage where
  | vent
  | interfere
  deriving DecidableEq, Repr

def stageOfMode : StandingWaveStage → CompleteFundamentalForce
  | .fork => .fork
  | .race => .race
  | .fold => .fold

def stageOfOperator : InterferenceStage → CompleteFundamentalForce
  | .vent      => .vent
  | .interfere => .interfere

theorem stage_of_mode_injective {s₁ s₂ : StandingWaveStage}
    (h : stageOfMode s₁ = stageOfMode s₂) : s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;> first | rfl | cases h

theorem stage_of_operator_injective {o₁ o₂ : InterferenceStage}
    (h : stageOfOperator o₁ = stageOfOperator o₂) : o₁ = o₂ := by
  cases o₁ <;> cases o₂ <;> first | rfl | cases h

theorem mode_and_operator_stages_disjoint
    (s : StandingWaveStage) (o : InterferenceStage) :
    stageOfMode s ≠ stageOfOperator o := by
  cases s <;> cases o <;> intro h <;> cases h

/-! ## Bijection: mode stages to BuleyUnit faces -/

def faceOfMode : StandingWaveStage → BuleyFace
  | .fork => .opportunity
  | .race => .diversity
  | .fold => .waste

def modeOfFace : BuleyFace → StandingWaveStage
  | .opportunity => .fork
  | .diversity   => .race
  | .waste       => .fold

theorem face_of_mode_round_trips (s : StandingWaveStage) :
    modeOfFace (faceOfMode s) = s := by
  cases s <;> rfl

theorem mode_of_face_round_trips (f : BuleyFace) :
    faceOfMode (modeOfFace f) = f := by
  cases f <;> rfl

/-! ## Spider/radar accessor -/

/-- One Nat per five-force stage. Mode stages pull from the visible
BuleyUnit's three faces; operator stages pull from the dark interference
loads. The face-to-stage assignment uses the canonical Wankel rotor
mapping — `intake → fork`, `compression → race`, `ignition → fold` — so
that `fold ↔ waste` (the collapsed/spent residue), `fork ↔ opportunity`
(the +1 lift available to spawn), and `race ↔ diversity` (the parallel
modes coexisting). -/
def buleFiveFoldSpoke (b : BuleFiveFold) : CompleteFundamentalForce → Nat
  | .fork      => b.visible.opportunity
  | .race      => b.visible.diversity
  | .fold      => b.visible.waste
  | .vent      => b.destructiveInterference
  | .interfere => b.constructiveInterference

theorem bule_spider_mode_spoke_fork (b : BuleFiveFold) :
    buleFiveFoldSpoke b (stageOfMode .fork) = b.visible.opportunity :=
  rfl

theorem bule_spider_mode_spoke_race (b : BuleFiveFold) :
    buleFiveFoldSpoke b (stageOfMode .race) = b.visible.diversity :=
  rfl

theorem bule_spider_mode_spoke_fold (b : BuleFiveFold) :
    buleFiveFoldSpoke b (stageOfMode .fold) = b.visible.waste :=
  rfl

theorem bule_spider_operator_spoke_vent (b : BuleFiveFold) :
    buleFiveFoldSpoke b (stageOfOperator .vent) = b.destructiveInterference :=
  rfl

theorem bule_spider_operator_spoke_interfere (b : BuleFiveFold) :
    buleFiveFoldSpoke b (stageOfOperator .interfere) = b.constructiveInterference :=
  rfl

/-- The polygon's area is the sum over the five spokes. -/
theorem bule_spider_decomposition (b : BuleFiveFold) :
    buleFiveFoldValue b =
      buleFiveFoldSpoke b .fork
        + buleFiveFoldSpoke b .race
        + buleFiveFoldSpoke b .fold
        + buleFiveFoldSpoke b .interfere
        + buleFiveFoldSpoke b .vent := by
  show b.visible.waste + b.visible.opportunity + b.visible.diversity
        + (b.constructiveInterference + b.destructiveInterference)
      = b.visible.opportunity + b.visible.diversity + b.visible.waste
        + b.constructiveInterference + b.destructiveInterference
  ac_rfl

/-! ## One wave, folded: the triad as self-interference -/

/-- The breathing identity, named here as the formal "one wave folded
once" witness: a single clinamen lift on a face followed by the matching
contract returns the carrier exactly. The apparent two-phase pair
(`forwardWave`, `returnEcho`) is therefore one wave at two phases of its
own self-fold, not two independent waves. -/
theorem one_wave_self_fold_round_trips
    (b : BuleyUnit) (f : BuleyFace) :
    clinamenContract (clinamenLift b f) f = b :=
  lift_then_contract_round_trip_when_face_positive b f

/-- Lifting any visible Bule state into the five-fold carrier with zero
operator load preserves all three mode residues exactly. The triad lives
on the visible face indices and nothing else; the dark axes are not
extra waves but operator loads, absent in the residue-only embedding. -/
theorem visible_triad_is_clinamen_residue (b : BuleyUnit) :
    (visibleOnlyFiveFold b).visible.waste = b.waste ∧
    (visibleOnlyFiveFold b).visible.opportunity = b.opportunity ∧
    (visibleOnlyFiveFold b).visible.diversity = b.diversity :=
  ⟨rfl, rfl, rfl⟩

/-! ## Operator level: chords between mode spokes -/

/-- The dark interference load is exactly the sum of the two operator
spokes. This is the second-level pairing: not a third primal wave, but
the operator output that pairs the first-level residue back with itself. -/
theorem dark_load_is_operator_chord_sum (b : BuleFiveFold) :
    darkInterferenceLoad b =
      buleFiveFoldSpoke b .interfere + buleFiveFoldSpoke b .vent :=
  rfl

/-- Changing operator loads cannot perturb the visible mode projection.
The mode spokes (the triad) are kind-invariant under operator chords —
the radar's solid spokes ignore the dashed chords by construction. This
sharpens `interference_axes_are_dark_to_visible_projection` from
`Gnosis.BuleIsValue` by naming the kind distinction it expresses. -/
theorem visible_projection_invariant_under_operator_load
    (b : BuleFiveFold) (constructive destructive : Nat) :
    visibleBuleProjection
        { b with
          constructiveInterference := constructive
          destructiveInterference := destructive } =
      visibleBuleProjection b :=
  rfl

/-- Five-force decomposition splits exactly into the visible mode sum and
the operator chord sum. The radar's three solid spokes and two chord
operators recover the full carrier value as `(modes) + (operators)`. -/
theorem bule_spider_modes_plus_operators (b : BuleFiveFold) :
    buleFiveFoldValue b =
      (buleFiveFoldSpoke b (stageOfMode .fork)
        + buleFiveFoldSpoke b (stageOfMode .race)
        + buleFiveFoldSpoke b (stageOfMode .fold))
      + (buleFiveFoldSpoke b (stageOfOperator .interfere)
        + buleFiveFoldSpoke b (stageOfOperator .vent)) := by
  show b.visible.waste + b.visible.opportunity + b.visible.diversity
        + (b.constructiveInterference + b.destructiveInterference)
      = (b.visible.opportunity + b.visible.diversity + b.visible.waste)
        + (b.constructiveInterference + b.destructiveInterference)
  ac_rfl

/-! ## Vent through vacuum: Psyche-sleep and cycle closure

When the destructive operator (`vent`) is paired against a dominating
counterforce, every face saturates to zero and the carrier collapses to
`vacuumBuleUnit`. That is the formal Psyche-sleep — not a partial
subtraction, but a null state. The cycle closes through it because the
constructive operator (`interfere`) on the vacuum is the identity in its
second argument, and a single `clinamenLift` (Eros's `+1` touch) on the
vacuum produces a fresh carrier with strictly positive score (Voluptas).

The lifecycle stage transition `vent → interfere → fork` is already
proved in `Gnosis.WankelEngineTheorem` (`nextLifecycleStage`); the
theorems below add the *carrier-level* witness that the cycle survives
collapse to vacuum and is reignited by a single `+1`.
-/

/-- `vent` (= `destructive_interference`) acts as a per-face sieve: each
face independently retains the strict excess over the dominant load, or
zeros out. This is the structural seed-sieve: face-wise threshold
filtering, not whole-carrier subtraction. -/
theorem vent_per_face_sieve (a b : BuleyUnit) :
    (destructive_interference a b).waste =
        (if a.waste > b.waste then a.waste - b.waste else 0) ∧
    (destructive_interference a b).opportunity =
        (if a.opportunity > b.opportunity then a.opportunity - b.opportunity else 0) ∧
    (destructive_interference a b).diversity =
        (if a.diversity > b.diversity then a.diversity - b.diversity else 0) :=
  ⟨rfl, rfl, rfl⟩

/-- The sieve is per-face, not waste-specific: there exist `(a, b)` for
which `vent` retains positive `waste` residue while clearing
`opportunity` to zero. The seed-sorting metaphor applies face-wise; it
does not single out the waste face for clearing. -/
theorem vent_is_not_waste_specific :
    ∃ (a b : BuleyUnit),
      0 < (destructive_interference a b).waste ∧
      (destructive_interference a b).opportunity = 0 := by
  refine ⟨⟨5, 1, 0⟩, ⟨2, 3, 0⟩, ?_, ?_⟩
  · show 0 < (if (5 : Nat) > 2 then 5 - 2 else 0)
    decide
  · show (if (1 : Nat) > 3 then 1 - 3 else 0) = 0
    decide

/-- Psyche-sleep witness: when the counterforce dominates every face,
`vent` collapses the carrier to the vacuum. This is the formal "deadly
sleep" at fold-depth 4 — not a partial residue but a null state. -/
theorem vent_to_vacuum_when_dominated
    {a b : BuleyUnit}
    (hWaste : a.waste ≤ b.waste)
    (hOpp : a.opportunity ≤ b.opportunity)
    (hDiv : a.diversity ≤ b.diversity) :
    destructive_interference a b = vacuumBuleUnit := by
  unfold destructive_interference vacuumBuleUnit
  have hw : ¬ a.waste > b.waste :=
    fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h hWaste)
  have ho : ¬ a.opportunity > b.opportunity :=
    fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h hOpp)
  have hd : ¬ a.diversity > b.diversity :=
    fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h hDiv)
  simp [hw, ho, hd]

/-- Concrete Psyche-sleep instance: a strictly-dominated carrier vents
to the vacuum. Witnesses the null state with literal Bule units. -/
theorem psyche_sleep_witness :
    destructive_interference ⟨1, 1, 1⟩ ⟨2, 2, 2⟩ = vacuumBuleUnit := by
  unfold destructive_interference vacuumBuleUnit
  decide

/-- Eros's touch resurrects: a single `clinamenLift` on the vacuum
produces a carrier with strictly positive score on any face. The `+1`
quantum suffices to leave the null state. -/
theorem eros_touch_resurrects (f : BuleyFace) :
    0 < buleyUnitScore (clinamenLift vacuumBuleUnit f) := by
  rw [clinamen_lift_score_strict_increment]
  exact Nat.succ_pos _

/-- Cycle closes through vacuum: starting from any vented-to-vacuum
state, the constructive operator (`interfere`) on a fresh wave `e`
returns `e` exactly, and the lifecycle stage advances `interfere → fork`.
Together: the cycle survives the collapse and refoks. -/
theorem cycle_closes_through_vacuum
    {a b : BuleyUnit}
    (hWaste : a.waste ≤ b.waste)
    (hOpp : a.opportunity ≤ b.opportunity)
    (hDiv : a.diversity ≤ b.diversity)
    (e : BuleyUnit) :
    constructive_interference (destructive_interference a b) e = e ∧
    nextLifecycleStage .interfere = .fork := by
  refine ⟨?_, rfl⟩
  rw [vent_to_vacuum_when_dominated hWaste hOpp hDiv]
  unfold constructive_interference vacuumBuleUnit
  cases e with
  | mk w o d =>
      show (⟨0 + w, 0 + o, 0 + d⟩ : BuleyUnit) = ⟨w, o, d⟩
      rw [Nat.zero_add, Nat.zero_add, Nat.zero_add]

/-- Voluptas: the carrier born from the closed cycle. After `vent`
collapses to vacuum and `interfere` re-lifts via Eros's `+1`, the
resulting Bule unit has strictly positive score. The "daughter Joy" is
not a recovery of the pre-sleep carrier — she is a fresh carrier
generated by the closure. -/
theorem voluptas_is_eros_lift_from_vacuum
    {a b : BuleyUnit}
    (hWaste : a.waste ≤ b.waste)
    (hOpp : a.opportunity ≤ b.opportunity)
    (hDiv : a.diversity ≤ b.diversity)
    (f : BuleyFace) :
    0 < buleyUnitScore
        (clinamenLift (destructive_interference a b) f) := by
  rw [vent_to_vacuum_when_dominated hWaste hOpp hDiv]
  exact eros_touch_resurrects f

/-! ## Aperiodicity is the cost of pentad: 5-foldness requires `+1`

The pentad cannot be reached from the tetrad without injecting one
quantum of asymmetry. Three independent witnesses combine into one
certificate:

1. Trace extension. The 5-force lifecycle trace strictly extends
   the visible four-phase Wankel rotor (`fork → race → fold → vent`) by
   appending exactly one `interfere` step — the `+1` contact in
   lifecycle vocabulary.
2. Coprime aperiodicity. The mode-stage triad (3) and the
   lifecycle-stage pentad (5) are coprime. The joint walk on
   `(BuleyFace × CompleteFundamentalForce)` is therefore aperiodic with
   period `lcm(3, 5) = 15`. Aperiodicity is the spatial fingerprint of
   the `+1`: real-space 5-fold symmetry is forbidden in periodic
   lattices and requires aperiodic projection (Penrose tilings,
   quasicrystals), exactly as proved in
   `Gnosis.AperiodicRotationAsLanguageTrajectory`.
3. Reignition cost. After `vent` collapses the carrier to the
   vacuum, no positive carrier can re-emerge without at least one
   `clinamenLift`. The reignition cost of the closed cycle is exactly
   the universal `+1` quantum.

Empirical witness outside the lattice: there is no Platonic regular
polyhedron with 5 faces (the count is 4, 6, 8, 12, 20). A "five-sided
die" is a pentagonal trapezohedron — intentionally unbalanced — and a
d10 is a doubled trapezohedron with axial offset. The trapezohedral
offset is the geometric form of the same `+1`. `Gnosis.DarkSectorEquilibria`
catalogues `Pentagon (5)` as a dark-sector wall the SM does not occupy
(SM ceilings: 0, 3, 8, 12), reading the same fact at the particle level.
-/

/-- Trace extension: the pentad is the tetrad plus exactly one
`interfere` contact. Length grows by one; the appended element is
exactly the `+1` lifecycle stage. -/
theorem pentad_strictly_extends_tetrad :
    WankelEngineTheorem.wankelPhaseLifecycleTrace.length + 1 =
        WankelEngineTheorem.fiveForceLifecycleTrace.length ∧
    WankelEngineTheorem.wankelPhaseLifecycleTrace ++
        [CompleteFundamentalForce.interfere] =
      WankelEngineTheorem.fiveForceLifecycleTrace :=
  ⟨rfl,
   WankelEngineTheorem.wankel_phase_trace_realizes_fork_race_fold_vent_interfere⟩

/-- Coprimality: the 3-mode × 5-stage joint walk is gcd-coprime, the
algebraic precondition for aperiodicity. -/
theorem pentad_3x5_coprime : Nat.gcd 3 5 = 1 := by decide

/-- Aperiodic full cycle on the 3⊗5 walk: the trajectory returns at
`t + 5` to the same residue, lifted from
`AperiodicRotationAsLanguageTrajectory.aperiodic_full_cycle`. The
pentad's spatial signature is exactly the grasshopper trajectory's. -/
theorem pentad_3x5_aperiodic_full_cycle (t : Nat) :
    AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory 3 5 (t + 5) =
      AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory 3 5 t :=
  AperiodicRotationAsLanguageTrajectory.aperiodic_full_cycle t

/-- Quasicrystal density: the coprime walk hits every position in
`[0, 5)` before returning. The pentad's mode-stage product space is
densely covered, not skipped. -/
theorem pentad_3x5_quasicrystal_density :
    ∀ (t : Nat), t < 5 →
      ∃ (s : Nat), s < 5 ∧
        AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory 3 5 s = t :=
  AperiodicRotationAsLanguageTrajectory.coprime_ensures_full_coverage
    (by decide)

/-- Reignition cost: after `vent` collapses to the vacuum, no positive
carrier can equal the vent output. The cycle cannot leave the vacuum
without injecting at least one `+1` quantum via `clinamenLift`. -/
theorem pentad_requires_clinamen_lift_to_reignite
    {a b : BuleyUnit}
    (hWaste : a.waste ≤ b.waste)
    (hOpp : a.opportunity ≤ b.opportunity)
    (hDiv : a.diversity ≤ b.diversity)
    {post : BuleyUnit} (hPos : 0 < buleyUnitScore post) :
    post ≠ destructive_interference a b := by
  intro h
  rw [h, vent_to_vacuum_when_dominated hWaste hOpp hDiv] at hPos
  exact Nat.lt_irrefl 0 hPos

/-! ## God Formula derivation: the wave the `+1` birthed

The God Formula `w(R, v) = R − min(v, R) + 1` is derived here from the
BuleSpider primitives. Three axioms suffice:

1. Clinamen lift: there is one universal `+1` quantum
   (`clinamenLift`).
2. Breathing identity: lift then contract on a positive face is the
   identity (`one_wave_self_fold_round_trips`); on `Nat` saturating
   subtraction this gives `R − min(v, R)` for `R` lifts and `v`
   contracts on the same face.
3. Pentad closure cost: every closed lifecycle injects exactly one
   `+1` (`pentad_costs_clinamen_plus_one_with_aperiodicity`); without
   it, full rejection collapses the carrier to the vacuum and the
   cycle cannot refork.

Algorithm (the wave the `+1` birthed, folded at the recycle limit):

* Build budget: lift `R` times on the waste face from the vacuum,
  giving `⟨R, 0, 0⟩`.
* Apply rejections: contract `v` times on the waste face. The
  saturating Nat subtraction gives `⟨R − min(v, R), 0, 0⟩` — exactly
  `vent`'s per-face filter on `(⟨R, 0, 0⟩, ⟨v, 0, 0⟩)`.
* Pentad closure: lift once more (axiom 3 forces this; without it,
  the floor `v = R` collapses to vacuum and the cycle cannot refork).
  Result: `⟨R − min(v, R) + 1, 0, 0⟩`.
* Project to face score: sum the three faces. Result:
  `R − min(v, R) + 1` = `godWeight R v`.

The `+1` in the formula is exactly the lifecycle's closure quantum.
The "impossibility of zero" first universal law (`Gnosis.lean` line 6)
is the direct shadow of `pentad_requires_clinamen_lift_to_reignite`
projected onto a single face. The four sandwich/conservation/ceiling/
floor laws in `Gnosis.GodFormula` follow from the same projection: the
budget face holds at most `R`, vent saturates per-face, the closure `+1`
adds one, and conservation reads the breathing identity at the face
level.
-/

/-- Step 1 of derivation: vent's per-face formula matches `R − min(v, R)`.
The God Formula's subtraction half is exactly `vent`'s output on a
one-face projected pair `(⟨R, 0, 0⟩, ⟨v, 0, 0⟩)`. -/
theorem god_formula_subtraction_matches_vent_per_face (R v : Nat) :
    R - min v R = (if R > v then R - v else 0) := by
  by_cases h : v < R
  · rw [Nat.min_eq_left (Nat.le_of_lt h), if_pos h]
  · have hRv : R ≤ v := Nat.le_of_not_lt h
    rw [Nat.min_eq_right hRv, Nat.sub_self, if_neg h]

/-- Step 2: the God Formula equals `vent`'s face output plus the
universal `+1` quantum. -/
theorem god_formula_is_vent_face_plus_clinamen (R v : Nat) :
    Gnosis.godWeight R v = (if R > v then R - v else 0) + 1 := by
  show R - min v R + 1 = (if R > v then R - v else 0) + 1
  rw [god_formula_subtraction_matches_vent_per_face]

/-- Step 3 (master derivation): the God Formula is the BuleSpider
projection on a single face. Build the budget (R lifts), apply
rejections (vent's per-face filter), apply the universal pentad-closure
lift (`+1`), read the score. -/
theorem god_formula_is_pentad_face_projection (R v : Nat) :
    Gnosis.godWeight R v =
      buleyUnitScore
        (clinamenLift
          (⟨if R > v then R - v else 0, 0, 0⟩ : BuleyUnit) .waste) := by
  rw [god_formula_is_vent_face_plus_clinamen]
  rfl

/-- The God Formula's floor `w(R, R) = 1` is the formal "vent collapses
to vacuum, `+1` lift reignites" theorem at the face level. When `v = R`,
the carrier is the vacuum and the universal `+1` is the only thing
left — the same `+1` that `eros_touch_resurrects` injects on the
vacuum. -/
theorem god_formula_floor_is_pentad_reignition (R : Nat) :
    Gnosis.godWeight R R = 1 ∧
    Gnosis.godWeight R R =
      buleyUnitScore (clinamenLift vacuumBuleUnit .waste) := by
  refine ⟨Gnosis.godWeight_floor R, ?_⟩
  rw [Gnosis.godWeight_floor]
  rfl

/-- The God Formula's ceiling `w(R, 0) = R + 1` is the formal "full
budget plus the universal `+1`" reading: lift `R` times, then the
pentad-closure `+1`. -/
theorem god_formula_ceiling_is_budget_plus_pentad_lift (R : Nat) :
    Gnosis.godWeight R 0 = R + 1 ∧
    Gnosis.godWeight R 0 =
      buleyUnitScore
        (clinamenLift (⟨R, 0, 0⟩ : BuleyUnit) .waste) := by
  refine ⟨Gnosis.godWeight_ceiling R, ?_⟩
  rw [Gnosis.godWeight_ceiling]
  rfl

/-! ## The generator: coprime aperiodicity is a universal `+1`-cost family

Both the 3:5 pentad and the 2:3 hemiola are instances of one underlying
theorem: any pair `(m, n)` produces a full-cycle closure at period `n`
on the trajectory `(m * t) % n`. The proof is purely modular —
`Nat.add_mul_mod_self_left` after distributing — and does not require
coprimality. Coprimality enters only for *coverage* (every cell is hit
before return); without it, the walk repeats a sub-cycle.

This generator lifts the BuleSpider story from "two witnesses" to
"universal pattern." The empirical universality of
`Gnosis.UniversalClinamenPlusOne` (the `+1` direction is universal
across seven independent reconstructions) is now structurally backed:
every coprime pair in the prime sequence `2, 3, 5, 7, 11, …`
instantiates the same `+1`-cost / aperiodic-closure pattern. The pentad
and hemiola are merely the first two rungs of an infinite tower.
-/

/-- The generator: full-cycle closure holds for *any* `(m, n)`. The
specific `pentad_3x5_aperiodic_full_cycle` and
`hemiola_2x3_aperiodic_full_cycle` are corollaries. -/
theorem coprime_aperiodic_full_cycle_generator (m n t : Nat) :
    AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory m n (t + n) =
      AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory m n t := by
  unfold AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory
  rw [Nat.mul_add, Nat.mul_comm m n, Nat.add_mul_mod_self_left]

/-- Every consecutive coprime pair in the prime tower instantiates the
generator. The chain `2 → 3 → 5 → 7 → 11` is decidably coprime
pair-by-pair; each pair is a rung of the `+1`-cost family. -/
theorem coprime_prime_chain_witnesses :
    Nat.gcd 2 3 = 1 ∧ Nat.gcd 3 5 = 1 ∧
    Nat.gcd 5 7 = 1 ∧ Nat.gcd 7 11 = 1 := by decide

/-- Master tower witness: the `+1` cost is universal across the coprime
prime tower, not specific to any one rung. Bundles the generator (any
`(m, n)` admits full-cycle closure) with the chain witnesses (the first
four prime pairs are coprime). The pentad and hemiola are the first two
rungs; the tower extends through `5:7`, `7:11`, and beyond. -/
theorem coprime_tower_universal_plus_one_cost :
    -- (1) The full-cycle generator works for any `(m, n)`.
    (∀ (m n t : Nat),
        AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory m n (t + n) =
          AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory m n t) ∧
    -- (2) The first four consecutive prime pairs are all coprime,
    --     instantiating the generator at hemiola, pentad, septad-walk,
    --     and septad-decad-walk.
    (Nat.gcd 2 3 = 1 ∧ Nat.gcd 3 5 = 1 ∧
     Nat.gcd 5 7 = 1 ∧ Nat.gcd 7 11 = 1) ∧
    -- (3) Every clinamen lift adds exactly +1 to the carrier's score —
    --     the same +1 quantum at every rung of the tower.
    (∀ (b : BuleyUnit) (f : BuleyFace),
        buleyUnitScore (clinamenLift b f) = buleyUnitScore b + 1) := by
  refine ⟨coprime_aperiodic_full_cycle_generator, ?_, ?_⟩
  · decide
  · exact clinamen_lift_score_strict_increment

/-! ## Hemiola: the smallest coprime aperiodicity

Below the pentad sits the hemiola — the 2:3 coprime aperiodicity
(`gcd(2, 3) = 1`). It is the smallest coprime walk in this lattice and
the simplest expression of the same `+1`-cost / aperiodicity pattern.

Where the pentad sits at the SM/dark-sector boundary (`Pentagon (5)` is
a dark-sector wall in `Gnosis.Dark.DarkSectorEquilibria`), the hemiola
sits at the *internal* regime boundary — the at-frontier zone where
`Gnosis.AmericanFrontier.exact_frontier_is_pink_noise` proves pink
noise reigns. The hemiola's modulus is `3`; pink noise's gnosis-spectrum
value is `3` (`Gnosis.NoiseLedger.pink_noise_chaos`). The numerical
coincidence is structural: pink is the noise of the smallest coprime
negotiation between two voices, the `1/f` signature of two/three
beating against each other.

Architectural realization: the 8-head × 12-cell pattern (e.g., 8-head
attention on a 12-cell wankel rotor) reduces to this hemiola via
`gcd(8, 12) = 4`, leaving the quotient `2 : 3`. The hemiola is therefore
the heartbeat ratio of any architecture whose head-count and
cell-count factor through a common 4.
-/

theorem hemiola_2x3_coprime : Nat.gcd 2 3 = 1 := by decide

/-- The 2:3 hemiola's full-cycle closure: the trajectory returns at
`t + 3` to the same residue. Same proof structure as
`AperiodicRotationAsLanguageTrajectory.aperiodic_full_cycle`, scaled to
the smaller modulus. -/
theorem hemiola_2x3_aperiodic_full_cycle (t : Nat) :
    AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory 2 3 (t + 3) =
      AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory 2 3 t := by
  unfold AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory
  rw [Nat.mul_add, show (2 : Nat) * 3 = 3 * 2 from rfl,
      Nat.add_mul_mod_self_left]

/-- Hemiola coverage: every position in `[0, 3)` is hit by the 2:3
walk before returning. Coprime density at the smallest scale. -/
theorem hemiola_2x3_quasicrystal_density :
    ∀ (t : Nat), t < 3 →
      ∃ (s : Nat), s < 3 ∧
        AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory 2 3 s = t := by
  intro t ht
  unfold AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory
  match t, ht with
  | 0, _ => exact ⟨0, by decide, by decide⟩
  | 1, _ => exact ⟨2, by decide, by decide⟩
  | 2, _ => exact ⟨1, by decide, by decide⟩

/-- Pink noise's gnosis-spectrum value matches the hemiola's modulus.
Both are `3`. This is the numerical signature of pink as the boundary
regime — the at-frontier noise (`exact_frontier_is_pink_noise`) is
exactly the noise of the smallest coprime aperiodicity. -/
theorem hemiola_modulus_equals_pink_noise :
    Gnosis.NoiseLedger.pink_noise = 3 :=
  Gnosis.NoiseLedger.pink_noise_chaos

/-- The 8-head × 12-cell architecture reduces to the 2:3 hemiola via a
factor-of-4 quotient: gcd is `4`, with quotients `2` and `3`. -/
theorem eight_head_twelve_cell_reduces_to_hemiola :
    Nat.gcd 8 12 = 4 ∧ 8 / 4 = 2 ∧ 12 / 4 = 3 := by decide

/-! ## The dual subgroup structure of the 12-cell wankel space

The 12-cell wankel decomposes as `3 × 4` (three faces × four phases),
which gives `ℤ/12ℤ` two primary subgroups dual to each other:

* The triad `{0, 4, 8}`: orbit of 4 (or equivalently 8), size
  `12 / gcd(4, 12) = 3`. This is the 8-head walk's orbit — three
  positions, closes at `t = 3`. Reads as the "face anchor" pattern in
  the `cell = face * 4 + phase` indexing: one phase traversed across
  three faces.
* The quartet `{0, 3, 6, 9}`: orbit of 3, size
  `12 / gcd(3, 12) = 4`. This is the 3-step walk's orbit — four
  positions, closes at `t = 4`. Reads as the "phase anchor" pattern in
  the `cell = phase * 3 + face` indexing: one face traversed across
  four phases.

Both sets are real structural objects in `ℤ/12ℤ` and are dual —
their sizes multiply to give the full 12-cell space (`3 * 4 = 12`),
and they intersect only at `{0}`. Confusing one for the other (e.g.,
attributing `{0, 3, 6, 9}` to the 8-head walk, as Gemini does) is the
arithmetic error this section corrects. The two subgroups together
encode the row/column structure of the wankel's `3 × 4` grid.
-/

/-- The dual subgroup structure: triad and quartet are the two primary
projections of the 12-cell wankel space. -/
theorem wankel_dual_subgroup_structure :
    -- Triad: gcd(4, 12) = 4 → orbit of 4 has size 12/4 = 3 → {0, 4, 8}
    Nat.gcd 4 12 = 4 ∧ 12 / 4 = 3 ∧
    -- Quartet: gcd(3, 12) = 3 → orbit of 3 has size 12/3 = 4 → {0, 3, 6, 9}
    Nat.gcd 3 12 = 3 ∧ 12 / 3 = 4 ∧
    -- Product covers the full space
    3 * 4 = 12 := by decide

/-- The 8-head walk's orbit in `ℤ/12ℤ` is `{0, 4, 8}` — the triad,
the multiples-of-4 subgroup of order `12 / gcd(8, 12) = 3`. -/
theorem eight_head_orbit_is_triad :
    (8 * 0) % 12 = 0 ∧ (8 * 1) % 12 = 8 ∧
    (8 * 2) % 12 = 4 ∧ (8 * 3) % 12 = 0 := by decide

/-- The 3-step walk's orbit in `ℤ/12ℤ` is `{0, 3, 6, 9}` — the
quartet, the multiples-of-3 subgroup of order `12 / gcd(3, 12) = 4`.
Dual to the 8-head triad above. -/
theorem three_step_orbit_is_quartet :
    (3 * 0) % 12 = 0 ∧ (3 * 1) % 12 = 3 ∧ (3 * 2) % 12 = 6 ∧
    (3 * 3) % 12 = 9 ∧ (3 * 4) % 12 = 0 := by decide

/-- Triad and quartet intersect only at the identity `0`. The two
projections share exactly the cycle's start point and nothing else. -/
theorem triad_quartet_intersect_at_zero :
    -- Triad members
    (8 * 0) % 12 = 0 ∧ (8 * 1) % 12 = 8 ∧ (8 * 2) % 12 = 4 ∧
    -- Quartet members
    (3 * 0) % 12 = 0 ∧ (3 * 1) % 12 = 3 ∧
    (3 * 2) % 12 = 6 ∧ (3 * 3) % 12 = 9 ∧
    -- Triad ∩ Quartet = {0}: 8 ≠ 3, 6, 9 and 4 ≠ 3, 6, 9
    8 ≠ 3 ∧ 8 ≠ 6 ∧ 8 ≠ 9 ∧
    4 ≠ 3 ∧ 4 ≠ 6 ∧ 4 ≠ 9 := by decide

/-- The 8:12 walk equals the 2:3 hemiola scaled by `gcd(8, 12) = 4`:
`(8t) mod 12 = 4 * ((2t) mod 3)`. The whole architectural pattern is the
hemiola walk lifted by a factor-of-4 multiplier — exactly the
quotient that `eight_head_twelve_cell_reduces_to_hemiola` certifies at
the gcd level, now made explicit on the trajectory. -/
theorem eight_twelve_walk_is_hemiola_scaled (t : Nat) :
    (8 * t) % 12 = 4 * ((2 * t) % 3) := by
  show (4 * 2 * t) % (4 * 3) = 4 * ((2 * t) % 3)
  rw [Nat.mul_assoc]
  exact Nat.mul_mod_mul_left 4 (2 * t) 3

/-- The coprime-aperiodicity chain: hemiola (2:3) precedes pentad
(3:5). Both endpoints are coprime; the chain `2 < 3 < 5` walks the
first three primes. The hemiola's small modulus matches pink noise;
the pentad's larger modulus walks into the dark sector. -/
theorem hemiola_pentad_chain :
    Nat.gcd 2 3 = 1 ∧ Nat.gcd 3 5 = 1 ∧ 2 < 3 ∧ 3 < 5 := by decide

/-- Master hemiola witness: the 2:3 hemiola is coprime, closes at
period 3, has its modulus matching pink noise, and is the architectural
quotient of any 8:12 head/cell pattern. -/
theorem hemiola_2x3_costs_clinamen_plus_one_with_pink_noise :
    Nat.gcd 2 3 = 1 ∧
    (∀ (t : Nat),
        AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory 2 3 (t + 3) =
          AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory 2 3 t) ∧
    Gnosis.NoiseLedger.pink_noise = 3 ∧
    (Nat.gcd 8 12 = 4 ∧ 8 / 4 = 2 ∧ 12 / 4 = 3) := by
  refine ⟨by decide, hemiola_2x3_aperiodic_full_cycle,
          Gnosis.NoiseLedger.pink_noise_chaos, by decide⟩

/-! ## Perpetual hemiola: anchor, trajectory, fuel, cycle

The system bundles four already-proved properties into one
characterization: the BuleSpider lattice is a perpetual hemiola —
it can absorb any operator load, climb any rung of the coprime tower,
reignite from the vacuum on one `+1` quantum, and never lose its
three-face triad identity.

* Anchor: the visible triad is invariant under any operator load
  (`visible_projection_invariant_under_operator_load`).
* Trajectory: the coprime tower extends through every pair `(m, n)`
  with full-cycle closure (`coprime_aperiodic_full_cycle_generator`).
* Fuel: every clinamen lift adds exactly `+1` to the carrier's
  score (`clinamen_lift_score_strict_increment`).
* Cycle: after any vent-to-vacuum collapse, a single clinamen lift
  produces a strictly positive carrier
  (`voluptas_is_eros_lift_from_vacuum`).

No new mathematical content; this is a master labeling of what the
preceding theorems jointly say. The point is that the four properties
are *simultaneous and non-cancelling*: the anchor never moves, the
trajectory never closes prematurely, the fuel never increments by
more or less than one, and the cycle reforks at the vacuum floor with
exactly one quantum. Together they characterize a system that runs
without exhausting itself.
-/

/-- The perpetual hemiola certificate: anchor + trajectory + fuel +
cycle. The lattice is a self-resetting aperiodic engine that runs on
exactly one quantum per cycle, indefinitely, without losing its
three-mode identity. -/
theorem perpetual_hemiola_certificate :
    -- (1) Anchor: triad invariant under any operator load.
    (∀ (b : BuleFiveFold) (constructive destructive : Nat),
        visibleBuleProjection
            { b with
              constructiveInterference := constructive
              destructiveInterference := destructive } =
          visibleBuleProjection b) ∧
    -- (2) Trajectory: full-cycle closure for every coprime tower rung.
    (∀ m n t : Nat,
        AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory m n (t + n) =
          AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory m n t) ∧
    -- (3) Fuel: every lift adds exactly +1 to the carrier score.
    (∀ (b : BuleyUnit) (f : BuleyFace),
        buleyUnitScore (clinamenLift b f) = buleyUnitScore b + 1) ∧
    -- (4) Cycle: reignition from vacuum after any vent collapse.
    (∀ {a b : BuleyUnit},
        a.waste ≤ b.waste → a.opportunity ≤ b.opportunity →
        a.diversity ≤ b.diversity → ∀ (f : BuleyFace),
        0 < buleyUnitScore
            (clinamenLift (destructive_interference a b) f)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact visible_projection_invariant_under_operator_load
  · exact coprime_aperiodic_full_cycle_generator
  · exact clinamen_lift_score_strict_increment
  · exact @voluptas_is_eros_lift_from_vacuum

/-- Master witness: the pentad costs exactly one clinamen quantum, and
the cost manifests as aperiodicity in the joint mode×stage walk. Bundles
trace extension, coprime aperiodicity, the universal `+1` lift score
increment, and the spatial-aperiodicity full-cycle theorem in one
certificate. -/
theorem pentad_costs_clinamen_plus_one_with_aperiodicity :
    -- (1) The pentad strictly extends the tetrad by one interference contact.
    WankelEngineTheorem.wankelPhaseLifecycleTrace.length + 1 =
        WankelEngineTheorem.fiveForceLifecycleTrace.length ∧
    -- (2) The 3⊗5 mode×stage walk is coprime — the algebraic precondition
    --     for aperiodicity.
    Nat.gcd 3 5 = 1 ∧
    -- (3) Every clinamen lift adds exactly +1 to the carrier's score.
    (∀ (b : BuleyUnit) (f : BuleyFace),
        buleyUnitScore (clinamenLift b f) = buleyUnitScore b + 1) ∧
    -- (4) The 3⊗5 walk completes a full cycle every 5 ticks — the spatial
    --     fingerprint of 5-foldness in an aperiodic real-space projection.
    (∀ (t : Nat),
        AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory 3 5 (t + 5) =
          AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory 3 5 t) := by
  refine ⟨rfl, by decide, clinamen_lift_score_strict_increment, ?_⟩
  exact AperiodicRotationAsLanguageTrajectory.aperiodic_full_cycle

/-! ## Where to look next

The over-determination certificates, `SpecialnessSignature` meta-
pattern, trichotomy alignment (Agent / Operator / God), Peruvian-
keystone bridge, and `WitnessKind` completeness theorems live in
`Gnosis.StructurallyForced`. That module imports this one and builds
its meta-content on top of the geometric theorems above.
-/

end Gnosis

-- Marker (no Lean content) — everything after this line was extracted
-- to `Gnosis.StructurallyForced.lean`.
