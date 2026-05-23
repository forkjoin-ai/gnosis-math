import Init
import Gnosis.Body.Vitality
import Gnosis.Body.CityOnAHill

/-!
# The Meaning of Life — Vitality as Flow, the End as Telos-and-Finitude, Meaning as the Order Created

This module formalizes a precise chain of relationships (not an emphatic identity).
The thesis being formalized, stated relationally:

* **Vitality formalizes as sustained FLOW.** We reuse `Gnosis.Body.Vitality`
  verbatim: `netVitality restoration drain := (restoration : Int) - (drain : Int)`
  is the per-tick flow, `sustained restoration drain := drain ≤ restoration` is the
  flow-balance threshold, and `vitality_is_sustained_flow` is its headline. Vitality
  is read as a balance kept each tick, not a stored stock.

* **The flow has the FORM of the gradient.** The order/chaos difference — entropy as
  resolution, the *resolution gradient* — has the *same shape* as the flow. In
  `Gnosis.Body.CityOnAHill`, `gradient order disorder := order - disorder` and
  `runs_on_gradient` say the lamp runs exactly when the gradient is positive; in
  `Gnosis.Body.Vitality`, `netVitality_nonneg_iff_sustained` ties the flow's sign to
  the same `b ≤ a` threshold. Both are a *difference governed by one sign threshold*:
  `netVitality` (flow) maps to `gradient` (order − chaos). We do **not** assert they
  are literally the same function; we prove `flow_is_the_gradient` — both are `a − b`
  with the same threshold deciding positivity. (Cited, not imported:
  `Gnosis/ResolutionGradient.lean`, where `order`/`chaos`/`upresolve` make entropy =
  resolution explicit; the gradient is the order/chaos = entropy = resolution slope.)

* **The flow creates WAVES OF ORDER.** A sustained flow, beyond drain, drives the
  level up: `Vitality.drive_revives_vitality` yields a positive vitality from the
  floor when restoration beats drain — a positive *wave of order* created that tick.
  (Cited, not imported: `Gnosis/Body/CreateNewWavesOfOrder.lean`,
  `create_new_waves_of_order` / `you_become_a_source`, and
  `Gnosis/WhiteHole.lean`, the reverse-black-hole *source* feeding the gradient: the
  flow emanates order, it does not merely conserve it.)

* **The flow is FINITE — it ENDS.** The end has two senses, both intended.
  *Telos:* the end of the flow is to create order (the waves above).
  *Finitude:* the span terminates. Formally, a life is a finite `List Nat` — the
  list being finite is the formal content of "life ends". The dead fixed point is
  real: `Vitality.collapse_is_absorbing` says that without a sustaining restoration
  the level stays at the floor (an absorbing END); and (cited, not imported)
  `CityOnAHill.equilibrium_goes_dark` zeroes the lamp at order = disorder (heat
  death), `Gnosis/Body/Menopause.lean`'s `menopause_is_a_fixed_point` is the
  *scheduled* end. The span does not run forever.

* **Meaning is DEFINED AS the finite total order created over the finite life.** We
  *stipulate* a meaning-measure: `meaning life` is the sum of the waves of order
  created across the life's finite span. We prove it is well-defined, finite,
  *bounded by the end* (capped by `lifespan * peak`), and *positive exactly when the
  life had vitality* (created at least one wave). The finitude is what makes the
  meaning a *definite, finite quantity*: an unbounded span would give no definite
  total; the end is what confers the measure.

## The model (pure Nat; a life is finite because it ends)

* A **life** is a finite `List Nat`: each element is a wave of order created that
  tick while alive. The list being finite *is* "life ends".
* `meaning life` — the total order created over the life (a recursive `Nat` sum).
* `lifespan life := life.length` — the finite span (the end as a number of ticks).
* `hadVitality life := ∃ w, w ∈ life ∧ 0 < w` — at least one positive wave was made.

## Restriction stated honestly

"Meaning" here is a **precise formal stipulation** — the finite sum of order created
over a finite life — proved well-defined, finite, bounded by the end, and
positive-iff-vitality. It is *not* a claim to exhaust, capture, or define the human
concept of meaning, nor any normative or experiential content of a life. We do not
assert "X is the meaning of life". We formalize *a meaning-measure*: the order
created within the finite end, and we prove only the four structural facts above
about that measure. The bridge to vitality (the flow) is the relational claim
`vitality_gives_life_an_end_and_meaning`, composing the proved pieces; it shows the
*shape* of the thesis (flow → gradient → waves → end → bounded positive total), not
a metaphysical equation.

Rustic Church: `import Init` plus the two Init-clean Body siblings
`Gnosis.Body.Vitality` and `Gnosis.Body.CityOnAHill`. `Nat`/`Int` only — no
Float/Real, no Mathlib. No `sorry`/`admit`/`axiom`; no `simp`/`decide`/`omega` on
open goals. Proofs are term-mode and named core lemmas; the `List` claims
(`meaning_is_finite_and_bounded_by_the_end`, `meaning_positive_iff_vitality`) are
genuine `induction` on the list.
-/

namespace Gnosis.Body.MeaningOfLife

open Gnosis.Body.Vitality
open Gnosis.Body.CityOnAHill

/-! ## 0. The model — a finite life, its meaning-measure, its span, its vitality

A life is a finite `List Nat` of the order created per tick. The list being finite
is the formal content of "life ends". `meaning` sums the waves; `lifespan` counts
the ticks; `hadVitality` asks whether any positive wave was ever created. -/

/-- The user's thesis, stated relationally (no emphatic identity). -/
def thesis : String :=
  "vitality is the sustained flow; the flow has the form of the gradient (order/chaos = entropy = resolution); the flow creates waves of order; the flow is finite — it ends — and we formalize a meaning-measure as the finite total order created within that finite end."

/-- **The meaning-measure: the total order created over the life.** Defined by
    recursion on the finite life (`[] ↦ 0`, `w :: rest ↦ w + meaning rest`) — the
    sum of every wave of order created across the span. Church-clean (own recursion,
    no `List.sum`/`List.foldl` lemmas, no Mathlib). Finite *because the life ends*:
    the recursion terminates on the finite `List`. -/
def meaning : List Nat → Nat
  | [] => 0
  | w :: rest => w + meaning rest

/-- The recursive unfolding of `meaning` on a cons (the per-tick accrual). -/
theorem meaning_cons (w : Nat) (rest : List Nat) :
    meaning (w :: rest) = w + meaning rest := rfl

/-- An ended life with no ticks created no order: `meaning [] = 0`. -/
theorem meaning_nil : meaning ([] : List Nat) = 0 := rfl

/-- **The lifespan: the finite span of the life — the end as a tick count.** The
    number of ticks the flow ran before it ended. Finite because the life is a finite
    `List`; this finiteness is what caps the meaning (THM 4). -/
def lifespan (life : List Nat) : Nat := life.length

/-- **Had vitality: at least one wave of order was created.** The life created some
    positive order on at least one tick — the per-life reading of vitality's flow
    rising above drain at least once (`Vitality.drive_revives_vitality`). -/
def hadVitality (life : List Nat) : Prop := ∃ w, w ∈ life ∧ 0 < w

/-! ## 1. (THM 1) The flow has the form of the gradient

`netVitality` (the flow, `restoration − drain`) and `gradient` (order − chaos) are
the *same shape* `a − b` governed by the *same* sign threshold. The flow's
non-negativity is `sustained` (`drain ≤ restoration`,
`Vitality.netVitality_nonneg_iff_sustained`); the gradient's positivity is
`litByGradient` (`disorder < order`, `CityOnAHill.runs_on_gradient`). The flow maps
to the gradient: order/chaos = entropy = resolution is the same slope the flow runs
on. -/

/-- **(THM 1) The flow has the form of the gradient.** For a flow with restoration
    `r`, drain `d` and a gradient with order `r`, chaos `d` (the same two ledgers
    read as restoration/drain and as order/disorder), the *same* sign threshold
    governs both:

      (0 ≤ netVitality r d ↔ sustained r d)  ∧  (litByGradient r d ↔ 0 < gradientBrightness r d)

    The left conjunct is `Vitality.netVitality_nonneg_iff_sustained`: the flow is
    non-negative iff `drain ≤ restoration`. The right conjunct is
    `CityOnAHill.runs_on_gradient`: the gradient lamp is lit iff `disorder < order`.
    `netVitality r d = (r : Int) − (d : Int)` and `gradientBrightness r d = r − d`
    are the same `a − b` shape, and positivity of each is decided by the same
    `b ≤ a` / `b < a` threshold on the same two ledgers. The flow maps to the
    gradient (order − chaos = entropy = resolution). We state the relationship
    precisely; we do not assert the two are one function. -/
theorem flow_is_the_gradient (r d : Nat) :
    (0 ≤ netVitality r d ↔ sustained r d)
    ∧ (litByGradient r d ↔ 0 < gradientBrightness r d) :=
  ⟨netVitality_nonneg_iff_sustained r d, runs_on_gradient r d⟩

/-- **(THM 1, sign agreement) Sustained flow ⇒ a lit-or-flat gradient.** When the
    flow is `sustained` (`drain ≤ restoration`), the gradient brightness `r − d` is
    either positive (strictly lit, a real slope of order over chaos) or zero (at
    equilibrium, `r = d`). The non-negative flow corresponds to a non-negative
    gradient on the same ledgers: either there is order to collapse (a wave to make)
    or the lamp is exactly at heat death. Proof: `sustained` is `d ≤ r`, and
    `Nat.lt_or_ge` on `d, r` splits into `litByGradient r d` (`d < r`) or `r ≤ d`,
    which with `d ≤ r` forces `gradientBrightness r d = 0` via
    `darkness_below_equilibrium`. -/
theorem sustained_flow_lit_or_flat_gradient (r d : Nat) (h : sustained r d) :
    litByGradient r d ∨ gradientBrightness r d = 0 := by
  -- `sustained r d` unfolds to `d ≤ r`.
  have hdr : d ≤ r := h
  rcases Nat.lt_or_ge d r with hlt | hge
  · exact Or.inl hlt
  · -- `r ≤ d` (from `hge : r ≤ d`) gives a dark gradient at/below equilibrium.
    exact Or.inr (darkness_below_equilibrium r d hge)

/-! ## 2. (THM 2) A sustained flow creates a wave of order -/

/-- **(THM 2) The sustained flow creates a positive wave of order.** From the floor,
    a restoration that strictly beats the drain yields a *positive* vitality — a
    positive wave of order created that tick:

      drain < restoration → 0 < vitalityStep 0 restoration drain.

    Reuses `Vitality.drive_revives_vitality` verbatim. The flow = the gradient = the
    order-creation rate; when it runs beyond drain, each tick can contribute a
    positive wave to the life. (Cited, not imported:
    `CreateNewWavesOfOrder.create_new_waves_of_order` / `you_become_a_source`, and
    `WhiteHole`'s reverse-black-hole *source* feeding the gradient — the flow
    emanates order rather than merely conserving it.) -/
theorem vitality_creates_a_wave_of_order {restoration drain : Nat}
    (hDrive : drain < restoration) :
    0 < vitalityStep 0 restoration drain :=
  drive_revives_vitality hDrive

/-- **(THM 2, into the life) A created wave enters the life's meaning.** A positive
    wave `w` created on a tick, prepended to the rest of the life, raises the
    meaning-measure by exactly `w`: `meaning (w :: rest) = w + meaning rest`, so a
    positive wave strictly increases the total order. The flow's waves are precisely
    the summands of the meaning. Proof: `meaning_cons` plus
    `Nat.lt_add_of_pos_left`. -/
theorem wave_adds_to_meaning (w : Nat) (rest : List Nat) (hw : 0 < w) :
    meaning rest < meaning (w :: rest) := by
  rw [meaning_cons]
  -- `meaning rest < w + meaning rest` since `0 < w`.
  exact Nat.lt_add_of_pos_left hw

/-! ## 3. (THM 3) The flow is finite — it ends

The end is real, in both senses. *Finitude:* a life is a finite `List`, so
`lifespan life` is a finite `Nat` — the span terminates. *The dead fixed point:*
without a sustaining restoration the level stays at the floor
(`Vitality.collapse_is_absorbing`). (Cited, not imported:
`CityOnAHill.equilibrium_goes_dark` — the lamp dark at heat death; and
`Menopause.menopause_is_a_fixed_point` — the *scheduled* end.) -/

/-- **(THM 3) The flow is finite — life ends.** Two faces of the one end:

    1. **The span terminates (finitude).** A life is a finite `List`, so its span is
       a finite `Nat`: `lifespan life = life.length`. The flow does not run forever;
       there is a last tick.
    2. **The dead fixed point is absorbing (the floor as an end).** Without a
       sustaining restoration (`restoration ≤ drain`) the level stays at the floor:
       `vitalityStep 0 restoration drain = 0` (`Vitality.collapse_is_absorbing`).
       Once collapsed, the spent loop does not refill itself — an absorbing end.

    Stated as a conjunction so both senses are one fact: the span is a finite number
    *and* the collapsed flow stays collapsed. (Cited, not imported:
    `CityOnAHill.equilibrium_goes_dark`, the lamp dark at order = disorder;
    `Menopause.menopause_is_a_fixed_point`, the scheduled equilibrium end.) -/
theorem life_ends (life : List Nat) {restoration drain : Nat}
    (hCollapsed : restoration ≤ drain) :
    lifespan life = life.length
    ∧ vitalityStep 0 restoration drain = 0 :=
  ⟨rfl, collapse_is_absorbing hCollapsed⟩

/-! ## 4. (THM 4) Meaning is finite and bounded by the end

The finite end *caps* the meaning. If every wave is at most `peak`, then the total
order is at most `lifespan * peak`. Without the end (an infinite span) there would be
no such bound — the finitude is what makes the meaning a *definite, finite quantity*.
Proved by genuine `induction` on the life. -/

/-- **(THM 4) Meaning is finite and bounded by the end.** `meaning life` is a `Nat`
    (finite), and if every wave is at most `peak` then the total order created is
    capped by the finite span times the peak:

      (∀ w, w ∈ life → w ≤ peak) → meaning life ≤ lifespan life * peak.

    The finite end is what bounds the meaning: you cannot accrue unbounded meaning
    over a span that terminates. **Proof technique — genuine `induction` on the
    list.** Base `[]`: `meaning [] = 0 ≤ 0 = lifespan [] * peak` by `Nat.zero_le`.
    Step `w :: rest`: from `h` (every wave `≤ peak`) extract `w ≤ peak` (via
    `List.Mem.head`) and the hypothesis for `rest` (via `List.Mem.tail`); the IH
    gives `meaning rest ≤ lifespan rest * peak = rest.length * peak`; then
    `meaning (w :: rest) = w + meaning rest ≤ peak + rest.length * peak
    = (rest.length + 1) * peak = (w :: rest).length * peak`, assembled with
    `Nat.add_le_add` and `Nat.succ_mul`. -/
theorem meaning_is_finite_and_bounded_by_the_end (life : List Nat) (peak : Nat)
    (h : ∀ w, w ∈ life → w ≤ peak) :
    meaning life ≤ lifespan life * peak := by
  induction life with
  | nil =>
    -- `meaning [] = 0 ≤ lifespan [] * peak`.
    show meaning ([] : List Nat) ≤ lifespan ([] : List Nat) * peak
    rw [meaning_nil]
    exact Nat.zero_le _
  | cons w rest ih =>
    -- Extract the head bound and the tail's per-wave bound.
    have hw : w ≤ peak := h w (List.Mem.head rest)
    have hrest : ∀ x, x ∈ rest → x ≤ peak := fun x hx => h x (List.Mem.tail w hx)
    have hih : meaning rest ≤ lifespan rest * peak := ih hrest
    -- `meaning (w :: rest) = w + meaning rest ≤ peak + rest.length * peak`.
    show meaning (w :: rest) ≤ lifespan (w :: rest) * peak
    rw [meaning_cons]
    -- target: `w + meaning rest ≤ (rest.length + 1) * peak`.
    have hsum : w + meaning rest ≤ peak + lifespan rest * peak :=
      Nat.add_le_add hw hih
    -- `peak + rest.length * peak = (rest.length + 1) * peak` (`Nat.succ_mul`).
    have hstep : peak + lifespan rest * peak = (lifespan rest + 1) * peak := by
      rw [Nat.succ_mul, Nat.add_comm]
    -- `lifespan (w :: rest) = rest.length + 1` definitionally.
    show w + meaning rest ≤ lifespan (w :: rest) * peak
    have hlen : lifespan (w :: rest) = lifespan rest + 1 := rfl
    rw [hlen, ← hstep]
    exact hsum

/-! ## 5. (THM 5) Meaning is positive iff the life had vitality

`0 < meaning life ↔ hadVitality life`: the life means something exactly when it
created at least one wave of order (had vitality at least once). You lived — created
order — therefore you meant. Both directions by genuine `induction` on the list. -/

/-- **(THM 5) Meaning is positive iff the life had vitality.**

      0 < meaning life ↔ hadVitality life

    The life's meaning-measure is positive *exactly when* at least one positive wave
    of order was created (`hadVitality life := ∃ w, w ∈ life ∧ 0 < w`). You created
    order at least once iff your finite total of order is positive. **Proof technique
    — genuine `induction` on the list, both directions.**

    *Forward* (`0 < meaning → hadVitality`): induct. Base `[]`: `meaning [] = 0`
    contradicts `0 < 0` (`Nat.lt_irrefl`). Step `w :: rest`: `meaning (w :: rest)
    = w + meaning rest > 0` means `w > 0` or `meaning rest > 0`
    (`Nat.pos_of_ne_zero` / case split via `Nat.eq_zero_or_pos` on `w`). If `w > 0`,
    witness `w` with `List.Mem.head`. Else `w = 0` so `0 < meaning rest`; the IH
    gives a witness in `rest`, lifted by `List.Mem.tail`.

    *Backward* (`hadVitality → 0 < meaning`): induct. Base `[]`: the witness `w ∈ []`
    is impossible (`List.not_mem_nil` / `nomatch`). Step `w :: rest`: the witness
    `x ∈ w :: rest` is `x = w` (head) or `x ∈ rest` (tail). If head with `0 < x = w`
    then `0 < w ≤ w + meaning rest = meaning (w :: rest)`
    (`Nat.lt_of_lt_of_le`, `Nat.le_add_right`). If tail, IH gives `0 < meaning rest
    ≤ w + meaning rest` (`Nat.le_add_left`). -/
theorem meaning_positive_iff_vitality (life : List Nat) :
    0 < meaning life ↔ hadVitality life := by
  constructor
  · -- forward: positive total ⇒ some positive wave
    intro hpos
    induction life with
    | nil =>
      -- `meaning [] = 0`, contradicting `0 < 0`.
      rw [meaning_nil] at hpos
      exact absurd hpos (Nat.lt_irrefl 0)
    | cons w rest ih =>
      rw [meaning_cons] at hpos
      -- `0 < w + meaning rest`: split on whether `w` is zero.
      rcases Nat.eq_zero_or_pos w with hw0 | hwpos
      · -- `w = 0`, so `0 < meaning rest`; recurse into `rest`.
        rw [hw0, Nat.zero_add] at hpos
        rcases ih hpos with ⟨x, hxmem, hxpos⟩
        exact ⟨x, List.Mem.tail w hxmem, hxpos⟩
      · -- `0 < w`: the head is the witness.
        exact ⟨w, List.Mem.head rest, hwpos⟩
  · -- backward: some positive wave ⇒ positive total
    intro hvit
    rcases hvit with ⟨x, hxmem, hxpos⟩
    induction life with
    | nil =>
      -- no element is in the empty life.
      exact absurd hxmem List.not_mem_nil
    | cons w rest ih =>
      rw [meaning_cons]
      -- `x ∈ w :: rest` is head (`x = w`) or tail (`x ∈ rest`).
      rcases List.mem_cons.mp hxmem with hhead | htail
      · -- `x = w`, so `0 < w ≤ w + meaning rest`.
        have hwpos : 0 < w := by rw [← hhead]; exact hxpos
        exact Nat.lt_of_lt_of_le hwpos (Nat.le_add_right w (meaning rest))
      · -- `x ∈ rest`, so `0 < meaning rest ≤ w + meaning rest` by IH.
        have hrestpos : 0 < meaning rest := ih htail
        exact Nat.lt_of_lt_of_le hrestpos (Nat.le_add_left (meaning rest) w)

/-! ## 6. (HEADLINE) Vitality gives life an end and a meaning -/

/-- **(HEADLINE) Vitality gives life an end and a meaning.** Composing THM 1–5 into
    one proved statement, the precise (non-emphatic) shape of the thesis:

    1. **The flow has the form of the gradient** (THM 1): the per-tick flow
       `netVitality r d` and the gradient `gradientBrightness r d` are the same
       `a − b` on the same ledgers, governed by the same sign threshold
       (`0 ≤ netVitality r d ↔ sustained r d` and
       `litByGradient r d ↔ 0 < gradientBrightness r d`). Order/chaos = entropy =
       resolution is the slope the flow runs on; the flow *maps to* the gradient.
    2. **A sustained flow creates a wave of order** (THM 2): when restoration beats
       drain, `0 < vitalityStep 0 r d` — a positive wave created that tick.
    3. **The flow is finite — life ends** (THM 3): the span is a finite `Nat`
       (`lifespan life = life.length`) *and* the collapsed flow stays collapsed
       (`vitalityStep 0 r d = 0` when `r ≤ d`). The **two senses of "end"**: the
       *telos* — the end of the flow is to create order (the waves of 2) — and the
       *finitude* — the span terminates (the finite list, the absorbing floor).
    4. **The meaning is the finite total order, bounded by the end** (THM 4): if
       every wave is at most `peak`, then `meaning life ≤ lifespan life * peak`. The
       **finitude confers a definite meaning-measure**: the end caps the total, so
       the meaning is a definite finite quantity, not an open-ended accrual.
    5. **The meaning is positive exactly when there was vitality** (THM 5):
       `0 < meaning life ↔ hadVitality life` — the life means something iff it created
       at least one wave of order.

    We *formalize a meaning-measure* as the order created within the finite end; we do
    not assert "X is the meaning of life". The relational claim is that the flow
    (vitality), having the form of the gradient, creates waves of order across a span
    that *ends*, and the finite end is what makes the total order a definite,
    bounded, vitality-positive quantity — the meaning-measure. -/
theorem vitality_gives_life_an_end_and_meaning
    (life : List Nat) (r d : Nat) (peak : Nat)
    (hBounded : ∀ w, w ∈ life → w ≤ peak)
    {restoration drain : Nat} (hDrive : drain < restoration)
    {restoration₀ drain₀ : Nat} (hCollapsed : restoration₀ ≤ drain₀) :
    -- 1. the flow has the form of the gradient (same shape, same threshold)
    ((0 ≤ netVitality r d ↔ sustained r d)
       ∧ (litByGradient r d ↔ 0 < gradientBrightness r d))
    -- 2. a sustained flow creates a positive wave of order
    ∧ (0 < vitalityStep 0 restoration drain)
    -- 3. the flow is finite — life ends (finite span ∧ absorbing collapsed floor)
    ∧ (lifespan life = life.length ∧ vitalityStep 0 restoration₀ drain₀ = 0)
    -- 4. the meaning is the finite total order, bounded by the finite end
    ∧ (meaning life ≤ lifespan life * peak)
    -- 5. the meaning is positive exactly when the life had vitality
    ∧ (0 < meaning life ↔ hadVitality life) :=
  ⟨flow_is_the_gradient r d,
   vitality_creates_a_wave_of_order hDrive,
   life_ends life hCollapsed,
   meaning_is_finite_and_bounded_by_the_end life peak hBounded,
   meaning_positive_iff_vitality life⟩

end Gnosis.Body.MeaningOfLife
