import Init
import Gnosis.TritonCanonical
import Gnosis.TritonForkRaceFold
import Gnosis.StandingWaveAmplitudeBridge

/-!
# OrientationSpinorBridge — the DISCRETE core of orientation-as-spinor perception

A perception layer treats a perceived ORIENTATION (a "director": an undirected axis, the
thing a double-headed arrow ↕ points along) as the IMAGE of a finer SPINOR datum that
additionally carries a SHEET / SIGN. The continuous picture is the universal cover
`SU(2) → SO(3)` (a 2:1 group homomorphism, the "double cover"); a `4π` rotation of the
spinor returns it to itself while a `2π` rotation flips its global sign, and only the
DIRECTOR (the `SO(3)` orientation, the squared/quotient datum) has period `2π`. This is
the orientation-entanglement / belt-trick / Dirac-scissors phenomenon.

**Scope, stated up front (honesty over coverage).** This module does NOT build the
continuous `SU(2) → SO(3)` Lie-group cover; that needs Mathlib's real manifold / Lie
machinery and is out of scope here. It formalizes only the DISCRETE/ALGEBRAIC content the
perception actually consumes, and cites the continuous picture in prose:

  * §1  **The ℤ/2 cover carried by the ledger's own `tritAmplitude = natAbs ∘ sign`.**
        The HEADLINE cover statement routes through the ledger's existing amplitude map
        (`StandingWaveAmplitudeBridge.tritAmplitude`), NOT a fresh parallel construction and
        NOT `intensity` (which is injective on `Nat` and carries no cover — see the NOTE).
        On the FULL `Verdict` trit, `tritAmplitude = natAbs ∘ sign` realizes a ℤ/2-cover-
        with-fixed-center: the orbit `{accept, decline}` (signs `+1`/`-1`) collapses 2-to-1
        onto amplitude `1` (the antinode pair), while the node `abstain` (sign `0`) is the
        UNIQUE fixed point at amplitude `0`. This is `natAbs`'s genuine 2-to-1 collapse on
        `{±1}` with `0` fixed — the real form of the `U(1)`/`SU(2)` sheet structure, reusing
        `antinodes_are_definite` + `node_is_abstain` + `abstain_is_superposed`. A supporting
        `Bool` development (`square : Bool → Int`) exhibits the same shape on the two definite
        sheets and is shown to AGREE with `tritAmplitude` on the `{accept, decline}` orbit.
  * §2  **Verdict map onto the spin triple `{-1,0,+1}`.** An OBSERVATION of the sheet
        (`some s` = resolved, `none` = unobserved) maps to `TritonCanonical.Verdict`:
        resolved `+`/`-` ↦ `accept`/`decline` (sign `±1`), unobserved ↦ `abstain` (sign
        `0`). The map is total/well-defined; the `0`/abstain case is tied to
        `StandingWaveAmplitudeBridge.node_is_abstain` (sign-`0` ⇔ `abstain` node) in prose
        and proved here via `TritonCanonical.sign` directly.
  * §3  **Periodicity (`4π` sheet, `2π` director).** Model "rotate by a quantum" as the
        generator `+1` on a `Fin 4` sheet-carrier, with the director read off by the
        order-2 quotient `Fin 4 → Fin 2` (reduction mod 2). Applying the generator TWICE
        returns the director but FLIPS the sheet; applying it FOUR times returns the sheet.
        The generator has order 4 upstairs (sheet) and order 2 downstairs (director) — the
        order halves under the 2:1 quotient. This is the discrete shadow of `4π = id`,
        `2π = -id` on the spinor, `2π = id` on the director.
  * §4  Master certificate + a NOTE relating §1's squaring to
        `StandingWaveAmplitudeBridge.born_intensity_is_weight`'s `intensity = amplitude²`.

## Encoding discipline

`import Init` + `Gnosis.TritonCanonical` only — no Mathlib. The sheet sign is `Bool`; the
director is a one-point image; the cyclic carriers are `Fin 4` / `Fin 2` with `Fin.add`.
Every theorem closes by `decide` over a finite/closed statement, by explicit small case
analysis, or by reusing an already-proven theorem. Zero `sorry`, zero `admit`, zero
`native_decide`, zero new `axiom`. The only axioms reached are `propext` (and `Quot.sound`
through library lemmas if any). Verify with `#print axioms <theorem>`.
-/

namespace Gnosis
namespace OrientationSpinorBridge

open Gnosis.TritonCanonical (Verdict sign)
open Gnosis.TritonForkRaceFold (abstain_is_superposed)
open Gnosis.StandingWaveAmplitudeBridge
  (tritAmplitude node_is_abstain antinodes_are_definite tritAmplitude_abstain
   tritAmplitude_accept tritAmplitude_decline)

-- ══════════════════════════════════════════════════════════
-- §1  The ℤ/2 cover — carried by the ledger's `tritAmplitude = natAbs ∘ sign`
-- ══════════════════════════════════════════════════════════

/-! **HEADLINE.** The genuine 2-to-1 sheet collapse already lives in the ledger, in the
    EXISTING map `StandingWaveAmplitudeBridge.tritAmplitude = (sign ·).natAbs`. We state the
    cover through it directly, on the FULL `Verdict` trit — not through a fresh parallel
    `Bool`-`square` (that is kept below as a supporting witness, §1b) and NOT through
    `intensity` (which is injective on `Nat`, carries no cover; see the §4 NOTE).

    `natAbs : Int → Nat` is the real-line analogue of the `U(1)` cover's quotient: it is
    2-to-1 on the antinode signs (`+1` and `-1` both `↦ 1`) and fixes the node (`0 ↦ 0`).
    Composed with `sign`, this makes the trit the REAL FORM of the ℤ/2 sheet cover — the
    cover restricted to the real slice `{+1, -1} ∪ {0}`, where the continuous phase circle
    degenerates to the two-point sign group ℤ/2 plus a fixed center. Concretely:

      * the ORBIT `{accept, decline}` (signs `+1`/`-1`) is the ℤ/2-torsor of two distinct
        sheets that COLLAPSE 2-to-1 onto the single amplitude `1` (the antinode pair), so
        `tritAmplitude` cannot tell `accept` from `decline` — `natAbs` has forgotten the sign;
      * the NODE `abstain` (sign `0`) is the UNIQUE FIXED POINT at amplitude `0` (the center
        the ℤ/2 action fixes, the superposed middle).

    The proof reuses `antinodes_are_definite` (amplitude `1 ↔ {accept, decline}`),
    `node_is_abstain` (amplitude `0 ↔ abstain`), and `abstain_is_superposed` (the two
    definite verdicts carry nonzero, oppositely-signed sign), rather than re-deriving. -/

/-- The two-element ℤ/2 orbit: the definite verdicts whose signs are the sheet pair `±1`. -/
def sheetOrbit : List Verdict := [.accept, .decline]

/-- **The orbit's two sheets carry the two signs `+1` and `-1`** — a genuine ℤ/2-torsor on
    the real slice. `accept ↦ +1`, `decline ↦ -1`, and they are NEGATIVES of each other:
    `sign decline = - sign accept`. The orbit is exactly the nonzero-sign verdicts. -/
theorem sheetOrbit_signs_are_pm_one :
    sign Verdict.accept = 1
    ∧ sign Verdict.decline = -1
    ∧ sign Verdict.decline = - sign Verdict.accept
    ∧ sign Verdict.accept ≠ 0
    ∧ sign Verdict.decline ≠ 0 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact (abstain_is_superposed).2.2.1
  · exact (abstain_is_superposed).2.2.2

/-- **The orbit collapses 2-to-1 onto amplitude `1`.** Both sheets of the orbit map to the
    SAME amplitude `1` under `tritAmplitude = natAbs ∘ sign`, yet are GENUINELY distinct
    verdicts: `natAbs` has identified `+1` and `-1`. This is the 2-to-1 sheet-forgetting,
    the precise discrete analogue of `±g ∈ SU(2)` covering one `R ∈ SO(3)`. -/
theorem orbit_collapses_two_to_one :
    tritAmplitude Verdict.accept = 1
    ∧ tritAmplitude Verdict.decline = 1
    ∧ tritAmplitude Verdict.accept = tritAmplitude Verdict.decline
    ∧ Verdict.accept ≠ Verdict.decline := by
  refine ⟨tritAmplitude_accept, tritAmplitude_decline, ?_, by decide⟩
  rw [tritAmplitude_accept, tritAmplitude_decline]

/-- **The node `abstain` is the unique fixed center at amplitude `0`.** `tritAmplitude
    abstain = 0`, and amplitude `0` characterizes `abstain` uniquely (`node_is_abstain`):
    the ℤ/2 action's fixed point, the superposed middle. -/
theorem node_is_fixed_center :
    tritAmplitude Verdict.abstain = 0
    ∧ (∀ v : Verdict, tritAmplitude v = 0 ↔ v = .abstain) := by
  exact ⟨tritAmplitude_abstain, node_is_abstain⟩

/-- **`trit_is_real_form_of_z2_cover` — the trit is the real form of the ℤ/2 sheet cover,
    carried by `tritAmplitude = natAbs ∘ sign`.**

    This is the HEADLINE cover statement. On the full `Verdict` trit, the ledger's own
    amplitude map `tritAmplitude = (sign ·).natAbs` realizes a ℤ/2-cover-with-fixed-center:

      (a) the ORBIT `{accept, decline}` carries the two sheets `sign = +1` / `sign = -1`
          (a ℤ/2-torsor: `sign decline = - sign accept`, both nonzero — `sheetOrbit_signs_are_pm_one`);
      (b) `tritAmplitude` COLLAPSES that orbit 2-to-1 onto the single amplitude `1`: both
          sheets `↦ 1`, yet `accept ≠ decline` — the sign is forgotten by `natAbs`
          (`orbit_collapses_two_to_one`, reusing `antinodes_are_definite`);
      (c) the amplitude-`1` fibre is EXACTLY the orbit `{accept, decline}` and nothing else
          (`antinodes_are_definite`) — the 2-to-1 fibre is precisely 2-element;
      (d) the NODE `abstain` (sign `0`) is the UNIQUE FIXED POINT at amplitude `0`
          (`node_is_fixed_center`, reusing `node_is_abstain`) — the center the ℤ/2 fixes.

    So the trit `{-1, 0, +1}` is the real form of the `U(1)`/`SU(2)` double cover restricted
    to the real slice `{±1} ∪ {0}`: the two-point sign group ℤ/2 (the orbit) plus a fixed
    center (the node). The 2-to-1 collapse is `natAbs` on `{±1}`; the squaring `intensity`
    is incidental here (`1² = 1`, `0² = 0`) and carries NO cover (§4 NOTE). -/
theorem trit_is_real_form_of_z2_cover :
    -- (a) the orbit is a ℤ/2-torsor of two sheets ±1
    (sign Verdict.accept = 1 ∧ sign Verdict.decline = -1
      ∧ sign Verdict.decline = - sign Verdict.accept)
    -- (b) the orbit collapses 2-to-1 onto amplitude 1, sheets indistinguishable but distinct
    ∧ (tritAmplitude Verdict.accept = 1 ∧ tritAmplitude Verdict.decline = 1
      ∧ tritAmplitude Verdict.accept = tritAmplitude Verdict.decline
      ∧ Verdict.accept ≠ Verdict.decline)
    -- (c) the amplitude-1 fibre is exactly the 2-element orbit {accept, decline}
    ∧ (∀ v : Verdict, tritAmplitude v = 1 ↔ (v = .accept ∨ v = .decline))
    -- (d) the node abstain is the unique fixed center at amplitude 0
    ∧ (tritAmplitude Verdict.abstain = 0
      ∧ (∀ v : Verdict, tritAmplitude v = 0 ↔ v = .abstain)) := by
  refine ⟨⟨(sheetOrbit_signs_are_pm_one).1, (sheetOrbit_signs_are_pm_one).2.1,
            (sheetOrbit_signs_are_pm_one).2.2.1⟩,
          orbit_collapses_two_to_one,
          antinodes_are_definite,
          node_is_fixed_center⟩

-- ══════════════════════════════════════════════════════════
-- §1b  Supporting `Bool`-sheet witness — and its agreement with `tritAmplitude`
-- ══════════════════════════════════════════════════════════

/-! The sheet-carrier is the spinor SIGN, the `{-1,+1}` we model as `Bool`
    (`false ↦ -1`, `true ↦ +1`). The DIRECTOR is the squared datum. Squaring sends both
    `+1` and `-1` to `+1`: the director cannot tell the two sheets apart. This mirrors
    `±g ∈ SU(2)` covering one `R ∈ SO(3)` (the 2:1 double cover) and
    `TritonCanonical.collapse`'s sign-loss for the verdict alphabet. -/

/-- The sheet sign as an integer: `false ↦ -1`, `true ↦ +1`. The `{-1,+1}` carrier. -/
def sheetSign : Bool → Int
  | false => -1
  | true  => 1

/-- The director is the SQUARE of the sheet sign, `s·s`. Both sheets square to `+1`. This
    is the discrete `SU(2) → SO(3)` projection: it forgets the global sign. -/
def square : Bool → Int := fun s => sheetSign s * sheetSign s

/-- The two sheets square to the same director (`(-1)² = (+1)² = 1`). The sign is lost —
    the discrete double-cover collision. -/
theorem square_loses_sign : square false = square true := by decide

/-- Both directors are `+1`: the image of `square` is the single point `{1}`. -/
theorem square_is_one : ∀ s : Bool, square s = 1 := by
  intro s; cases s <;> decide

/-- The two sheets are GENUINELY distinct (distinct signs `-1 ≠ +1`), yet collapse to the
    same director. The 2:1 map drops real information, exactly as `collapse_loses_neutral`
    drops the neutral middle for verdicts. -/
theorem sheets_distinct_but_collide :
    sheetSign false ≠ sheetSign true ∧ square false = square true := by
  refine ⟨by decide, by decide⟩

/-- **The squaring map is exactly 2:1.** For the director value `1` (the whole image), the
    preimage `{s : Bool // square s = 1}` is the full 2-element `Bool` — both sheets, no
    more, no fewer. Stated as: the list of sheets squaring to `1` is all of `Bool`,
    length `2`, no duplicates. -/
def preimageOfOne : List Bool := (([false, true]).filter (fun s => decide (square s = 1)))

/-- The preimage of the director `1` is both sheets — length `2`, the 2:1 fibre. -/
theorem preimage_is_two : preimageOfOne = [false, true] ∧ preimageOfOne.length = 2 := by
  refine ⟨by decide, by decide⟩

/-- **`squaring_is_double_cover` — the discrete 2:1 double cover (sign-loss).**

      (a) both sheets square to the same director (`square_loses_sign`);
      (b) that common director is the single point `1` (`square_is_one`);
      (c) the sheets are genuinely distinct (`sheetSign false ≠ sheetSign true`), so the
          collapse drops real information;
      (d) the fibre over the director is exactly 2-element (`preimage_is_two`) — the map is
          2:1, not 1:1, not 3:1.

    This is the discrete shadow of `SU(2) → SO(3)`: `±g` cover one rotation `R`. -/
theorem squaring_is_double_cover :
    (square false = square true)
    ∧ (∀ s : Bool, square s = 1)
    ∧ (sheetSign false ≠ sheetSign true)
    ∧ (preimageOfOne = [false, true] ∧ preimageOfOne.length = 2) := by
  refine ⟨square_loses_sign, square_is_one, by decide, preimage_is_two⟩

/-! ### The `Bool` sheets embed into the orbit `{accept, decline}`, and `square` agrees with
    the ledger's `tritAmplitude` there. This is what subordinates §1b to the §1 headline:
    the supporting `Bool` development is a faithful slice of the trit cover, not a rival. -/

/-- Embed a `Bool` sheet into the verdict orbit `{accept, decline}`: `true ↦ accept`
    (sheet `+1`), `false ↦ decline` (sheet `-1`). The two sheets land on the two definite
    verdicts — the ℤ/2-torsor of §1. -/
def sheetToVerdict : Bool → Verdict
  | true  => .accept
  | false => .decline

/-- The embedding lands in the orbit (its image is exactly `{accept, decline}`), and it is
    injective — the two `Bool` sheets are the two distinct sheets of the orbit. -/
theorem sheetToVerdict_into_orbit :
    sheetToVerdict true = .accept
    ∧ sheetToVerdict false = .decline
    ∧ sheetToVerdict true ≠ sheetToVerdict false := by
  refine ⟨by decide, by decide, by decide⟩

/-- **`square` agrees with `tritAmplitude` on the embedded sheets.** For every `Bool` sheet
    `s`, the supporting director `square s` equals (as an `Int`) the ledger amplitude
    `tritAmplitude (sheetToVerdict s)`: both are the single antinode value `1`. The two
    developments compute the SAME 2-to-1 collapse on the orbit — the `Bool`-`square` is a
    faithful slice of the headline `natAbs ∘ sign` cover, not a parallel claim. -/
theorem square_agrees_with_tritAmplitude :
    ∀ s : Bool, square s = (tritAmplitude (sheetToVerdict s) : Int) := by
  intro s; cases s <;> decide

-- ══════════════════════════════════════════════════════════
-- §2  The verdict map — sheet observation onto the spin triple {-1,0,+1}
-- ══════════════════════════════════════════════════════════

/-! An OBSERVATION of the sheet is an `Option Bool`: `some s` = the sheet sign was
    resolved, `none` = unobserved/superposed. We map it onto `TritonCanonical.Verdict`,
    landing in the spin triple `{-1,0,+1}` via `sign`:
      * resolved `some true`  (sheet `+1`) ↦ `accept`  (sign `+1`)
      * resolved `some false` (sheet `-1`) ↦ `decline` (sign `-1`)
      * unobserved `none`                  ↦ `abstain` (sign `0`, the node)
    The `0`/abstain case is the standing-wave NODE: by
    `StandingWaveAmplitudeBridge.node_is_abstain`, `tritAmplitude v = 0 ↔ v = abstain`, so
    the unobserved sheet is exactly the zero-amplitude / superposed middle. -/

/-- Map a sheet OBSERVATION to a verdict. Resolved `+`/`-` ↦ `accept`/`decline`;
    unobserved ↦ `abstain` (the neutral node). -/
def verdictOfObservation : Option Bool → Verdict
  | some true  => .accept
  | some false => .decline
  | none       => .abstain

/-- Resolved positive sheet ↦ `accept`. -/
theorem verdict_some_true : verdictOfObservation (some true) = .accept := by decide
/-- Resolved negative sheet ↦ `decline`. -/
theorem verdict_some_false : verdictOfObservation (some false) = .decline := by decide
/-- Unobserved sheet ↦ `abstain` (the node). -/
theorem verdict_none : verdictOfObservation none = .abstain := by decide

/-- **The verdict map lands in the spin triple `{-1,0,+1}`.** Composing with
    `TritonCanonical.sign`, every observation maps to one of `-1, 0, +1` — and to all
    three (resolved `+`/`-` give `±1`, unobserved gives `0`). The map is total. -/
theorem verdict_sign_in_spin_triple :
    (∀ o : Option Bool, sign (verdictOfObservation o) = -1
                        ∨ sign (verdictOfObservation o) = 0
                        ∨ sign (verdictOfObservation o) = 1)
    ∧ sign (verdictOfObservation (some false)) = -1
    ∧ sign (verdictOfObservation none) = 0
    ∧ sign (verdictOfObservation (some true)) = 1 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  intro o
  cases o with
  | none => exact Or.inr (Or.inl (by decide))
  | some b => cases b <;> first | exact Or.inr (Or.inr (by decide)) | exact Or.inl (by decide)

/-- **`unobserved_is_abstain_node` — the `0`/abstain tie to the standing-wave node.**
    The unobserved sheet maps to the verdict with sign `0`, and the sign-`0` verdict is
    EXACTLY `abstain`: `sign v = 0 ↔ v = abstain`. By
    `StandingWaveAmplitudeBridge.node_is_abstain`, that sign-`0` `abstain` is the
    zero-amplitude standing-wave NODE. So "unobserved sheet" ⇔ "abstain" ⇔ "node". -/
theorem unobserved_is_abstain_node :
    verdictOfObservation none = .abstain
    ∧ sign (verdictOfObservation none) = 0
    ∧ (∀ v : Verdict, sign v = 0 ↔ v = .abstain) := by
  refine ⟨by decide, by decide, ?_⟩
  intro v
  cases v <;> (constructor <;> intro h <;> first | rfl | (exact absurd h (by decide)) | (exact absurd ‹_› (by decide)))

/-- **The verdict map is well-defined / total and injective on resolved observations.**
    Distinct observations that BOTH resolve a sheet map to distinct verdicts (the resolved
    information is preserved — unlike §1's squaring, the verdict map keeps the sheet sign
    where it is observed). The unobserved `none` is the unique preimage of `abstain`. -/
theorem verdict_map_total_and_resolved_injective :
    -- total: every observation has a verdict (definitional)
    (∀ o : Option Bool, verdictOfObservation o = .decline
                       ∨ verdictOfObservation o = .abstain
                       ∨ verdictOfObservation o = .accept)
    -- resolved-injective: distinct resolved sheets ↦ distinct verdicts
    ∧ (verdictOfObservation (some false) ≠ verdictOfObservation (some true))
    -- abstain has the unique preimage `none`
    ∧ (∀ o : Option Bool, verdictOfObservation o = .abstain → o = none) := by
  refine ⟨?_, by decide, ?_⟩
  · intro o
    cases o with
    | none => exact Or.inr (Or.inl rfl)
    | some b => cases b <;> first | exact Or.inr (Or.inr rfl) | exact Or.inl rfl
  · intro o h
    cases o with
    | none => rfl
    | some b => cases b <;> exact absurd h (by decide)

-- ══════════════════════════════════════════════════════════
-- §3  Periodicity — sheet period 4 (4π), director period 2 (2π)
-- ══════════════════════════════════════════════════════════

/-! Model "rotate by a quantum" as adding the generator `1` on a cyclic sheet-carrier
    `Sheet := Fin 4` (four quanta = `4π` back to start). The DIRECTOR is read off by the
    order-2 quotient `toDirector : Fin 4 → Fin 2` (reduction mod 2): the director only sees
    the sheet mod 2. The generator's order is 4 UPSTAIRS (sheet) and 2 DOWNSTAIRS (director)
    — the order halves under the 2:1 quotient. Discrete shadow of: spinor period `4π`,
    director period `2π`, with `2π` flipping the spinor's sign. -/

/-- The sheet carrier: a `Fin 4` cyclic group. Four quanta = `4π`. -/
abbrev Sheet := Fin 4
/-- The director carrier: a `Fin 2` cyclic group. Two quanta = `2π`. -/
abbrev Director := Fin 2

/-- Rotate the sheet by one quantum: `+1 mod 4` (the generator upstairs). -/
def rotSheet (x : Sheet) : Sheet := x + 1

/-- The order-2 quotient `Fin 4 → Fin 2`, reduction mod 2: the director read off the
    sheet. `0,2 ↦ 0` (director A); `1,3 ↦ 1` (director B). This is the 2:1 cover map at the
    cyclic level (analogue of §1's squaring: it forgets the "which of the two sheets"
    bit — here the `+2` summand). -/
def toDirector (x : Sheet) : Director :=
  match x with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1

/-- Rotate the director by one quantum: `+1 mod 2` (the generator downstairs). -/
def rotDirector (d : Director) : Director := d + 1

/-- **The quotient intertwines the generators.** `toDirector (rotSheet x) = rotDirector
    (toDirector x)` for every sheet — rotating upstairs then projecting equals projecting
    then rotating downstairs. The cover map is equivariant (a group homomorphism at the
    cyclic level). -/
theorem toDirector_intertwines :
    ∀ x : Sheet, toDirector (rotSheet x) = rotDirector (toDirector x) := by
  decide

/-- **`square`-style 2:1 at the cyclic level.** The quotient `toDirector` is exactly 2:1:
    each director value has a 2-element fibre (`0 ↤ {0,2}`, `1 ↤ {1,3}`). -/
theorem toDirector_two_to_one :
    (([0,1,2,3] : List Sheet).filter (fun x => decide (toDirector x = 0))).length = 2
    ∧ (([0,1,2,3] : List Sheet).filter (fun x => decide (toDirector x = 1))).length = 2 := by
  refine ⟨by decide, by decide⟩

/-- **TWO quanta (`2π`): the director RETURNS but the sheet is FLIPPED.** Applying the
    generator twice (`rotSheet (rotSheet x)`) leaves the DIRECTOR unchanged
    (`toDirector (rotSheet (rotSheet x)) = toDirector x`) but does NOT return the sheet —
    it advances it by `2` (the orientation-entanglement sign flip: spinor at `2π` is `-`
    itself, only the director has come back). -/
theorem two_quanta_director_returns_sheet_flips :
    -- director returns after 2 quanta (2π)
    (∀ x : Sheet, toDirector (rotSheet (rotSheet x)) = toDirector x)
    -- but the sheet does NOT return: it advances by 2 (the sign flip)
    ∧ (∀ x : Sheet, rotSheet (rotSheet x) = x + 2)
    ∧ (∃ x : Sheet, rotSheet (rotSheet x) ≠ x) := by
  refine ⟨by decide, by decide, ⟨0, by decide⟩⟩

/-- **FOUR quanta (`4π`): the SHEET returns.** Applying the generator four times returns
    the sheet to itself (`rotSheet⁴ = id`) — the spinor's `4π` identity. -/
theorem four_quanta_sheet_returns :
    ∀ x : Sheet, rotSheet (rotSheet (rotSheet (rotSheet x))) = x := by
  decide

/-- The sheet generator has order 4: `rot¹, rot², rot³ ≠ id`, `rot⁴ = id` (witnessed at
    the basepoint `0`, where the orbit is `0,1,2,3` then back to `0`). -/
theorem sheet_generator_order_four :
    rotSheet (0 : Sheet) ≠ 0
    ∧ rotSheet (rotSheet (0 : Sheet)) ≠ 0
    ∧ rotSheet (rotSheet (rotSheet (0 : Sheet))) ≠ 0
    ∧ rotSheet (rotSheet (rotSheet (rotSheet (0 : Sheet)))) = 0 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The director generator has order 2: `rot¹ ≠ id`, `rot² = id`. Half the sheet's order —
    the order halves under the 2:1 quotient. -/
theorem director_generator_order_two :
    rotDirector (0 : Director) ≠ 0
    ∧ rotDirector (rotDirector (0 : Director)) = 0 := by
  refine ⟨by decide, by decide⟩

/-- **`order_halves_under_quotient` — the generator's order is 4 upstairs, 2 downstairs.**
    The sheet generator has order 4 (`rot⁴ = id`, smaller powers ≠ id); its image under
    the quotient, the director generator, has order 2 (`rot² = id`, `rot¹ ≠ id`). Two
    full director periods (`2π + 2π`) fit in one sheet period (`4π`). -/
theorem order_halves_under_quotient :
    -- upstairs (sheet): order 4
    (rotSheet (rotSheet (rotSheet (rotSheet (0 : Sheet)))) = 0
      ∧ rotSheet (rotSheet (0 : Sheet)) ≠ 0)
    -- downstairs (director): order 2
    ∧ (rotDirector (rotDirector (0 : Director)) = 0
      ∧ rotDirector (0 : Director) ≠ 0)
    -- the quotient is equivariant
    ∧ (∀ x : Sheet, toDirector (rotSheet x) = rotDirector (toDirector x)) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, toDirector_intertwines⟩

-- ══════════════════════════════════════════════════════════
-- §4  Master certificate + Born-intensity NOTE
-- ══════════════════════════════════════════════════════════

/-- **ORIENTATION-SPINOR-BRIDGE (discrete core).**

      (0) §1  HEADLINE. The trit is the REAL FORM of the ℤ/2 sheet cover, carried by the
              ledger's own `tritAmplitude = natAbs ∘ sign` (`trit_is_real_form_of_z2_cover`):
              the orbit `{accept, decline}` (signs `+1`/`-1`) collapses 2-to-1 onto amplitude
              `1`, and the node `abstain` (sign `0`) is the unique fixed center at amplitude
              `0`. This routes through `tritAmplitude`, NOT `intensity` (§5 NOTE).
      (1) §1b The supporting `Bool` squaring `square : Bool → Int` is a 2:1 collapse on the
              two sheets (`squaring_is_double_cover`); it AGREES with the headline
              `tritAmplitude` on the embedded orbit `{accept, decline}`
              (`square_agrees_with_tritAmplitude`).
      (2) §2  The sheet-observation map lands in the spin triple `{-1,0,+1}` and is total;
              the unobserved sheet is the sign-`0` `abstain` node
              (`verdict_sign_in_spin_triple`, `unobserved_is_abstain_node`).
      (3) §3  Periodicity: two quanta (`2π`) return the director but flip the sheet
              (`two_quanta_director_returns_sheet_flips`); four quanta (`4π`) return the
              sheet (`four_quanta_sheet_returns`); the generator's order halves under the
              2:1 quotient, 4 upstairs to 2 downstairs (`order_halves_under_quotient`). -/
theorem orientation_spinor_bridge_master :
    -- (0) HEADLINE ℤ/2 cover via the ledger's tritAmplitude = natAbs ∘ sign
    ((tritAmplitude Verdict.accept = 1 ∧ tritAmplitude Verdict.decline = 1
        ∧ tritAmplitude Verdict.accept = tritAmplitude Verdict.decline
        ∧ Verdict.accept ≠ Verdict.decline)
      ∧ (∀ v : Verdict, tritAmplitude v = 1 ↔ (v = .accept ∨ v = .decline))
      ∧ tritAmplitude Verdict.abstain = 0
      ∧ (∀ v : Verdict, tritAmplitude v = 0 ↔ v = .abstain))
    -- (1) supporting Bool 2:1 collapse, agreeing with tritAmplitude on the orbit
    ∧ ((square false = square true ∧ (∀ s : Bool, square s = 1)
        ∧ preimageOfOne.length = 2)
      ∧ (∀ s : Bool, square s = (tritAmplitude (sheetToVerdict s) : Int)))
    -- (2) verdict map into the spin triple, unobserved = abstain node
    ∧ (sign (verdictOfObservation (some false)) = -1
      ∧ sign (verdictOfObservation none) = 0
      ∧ sign (verdictOfObservation (some true)) = 1
      ∧ verdictOfObservation none = Verdict.abstain
      ∧ (∀ v : Verdict, sign v = 0 ↔ v = .abstain))
    -- (3) periodicity: 2π director-returns/sheet-flips, 4π sheet-returns, order halves
    ∧ ((∀ x : Sheet, toDirector (rotSheet (rotSheet x)) = toDirector x)
      ∧ (∀ x : Sheet, rotSheet (rotSheet (rotSheet (rotSheet x))) = x)
      ∧ rotSheet (rotSheet (0 : Sheet)) ≠ 0
      ∧ rotDirector (rotDirector (0 : Director)) = 0
      ∧ (∀ x : Sheet, toDirector (rotSheet x) = rotDirector (toDirector x))) := by
  refine ⟨⟨orbit_collapses_two_to_one, antinodes_are_definite,
            tritAmplitude_abstain, node_is_abstain⟩,
          ⟨⟨square_loses_sign, square_is_one, (preimage_is_two).2⟩,
            square_agrees_with_tritAmplitude⟩,
          ⟨by decide, by decide, by decide, by decide,
            (unobserved_is_abstain_node).2.2⟩,
          (two_quanta_director_returns_sheet_flips).1, four_quanta_sheet_returns,
          ?_, ?_, toDirector_intertwines⟩
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- §5  Reading
-- ══════════════════════════════════════════════════════════

/-! The perception's orientation-as-spinor structure, formalized at the level it actually
uses — discrete and algebraic, no continuous Lie group.

§1 (HEADLINE) The trit is the REAL FORM of the ℤ/2 sheet cover, carried by the ledger's
OWN amplitude map `tritAmplitude = natAbs ∘ sign` (`trit_is_real_form_of_z2_cover`). The
genuine 2-to-1 collapse is `natAbs` on `{±1}`: the orbit `{accept, decline}` (signs
`+1`/`-1`, a ℤ/2-torsor — `sheetOrbit_signs_are_pm_one`) collapses onto the single
amplitude `1` (`orbit_collapses_two_to_one`, reusing `antinodes_are_definite`), and the
node `abstain` (sign `0`) is the UNIQUE fixed center at amplitude `0` (`node_is_fixed_center`,
reusing `node_is_abstain` and `abstain_is_superposed`). This MAPS TO (does not reconstruct)
the `SU(2) → SO(3)` double cover restricted to the real slice `{±1} ∪ {0}`, where `±g`
cover one rotation. It routes through `tritAmplitude`, NOT through `intensity` (see NOTE).

§1b (supporting) The `Bool` development `square : Bool → Int` sends both `-1` and `+1` to
`+1` (`square_loses_sign`), a 2:1 map with a 2-element fibre over its single image point
(`squaring_is_double_cover`). It is a faithful SLICE of the headline cover, not a rival:
the embedding `sheetToVerdict` (`sheetToVerdict_into_orbit`) lands the two `Bool` sheets in
the orbit `{accept, decline}`, and `square` AGREES with `tritAmplitude` there
(`square_agrees_with_tritAmplitude`). The sign-loss is the same shape as
`TritonCanonical.collapse`'s loss of the neutral middle.

§2 A sheet OBSERVATION (`Option Bool`) maps to `TritonCanonical.Verdict` and thence into
the spin triple `{-1,0,+1}` (`verdict_sign_in_spin_triple`): resolved `±` ↦ `accept`/
`decline` (sign `±1`), unobserved ↦ `abstain` (sign `0`). The unobserved sheet is the
sign-`0` `abstain` (`unobserved_is_abstain_node`), which by
`StandingWaveAmplitudeBridge.node_is_abstain` is the zero-amplitude standing-wave NODE.
The map is total and injective on resolved sheets (`verdict_map_total_and_resolved_injective`).

§3 Periodicity is the order-halving quotient `Fin 4 → Fin 2` (`toDirector`, equivariant by
`toDirector_intertwines`). Two quanta (`2π`) return the DIRECTOR but advance the sheet by
`2` — the orientation-entanglement / belt-trick sign flip
(`two_quanta_director_returns_sheet_flips`). Four quanta (`4π`) return the SHEET
(`four_quanta_sheet_returns`). The generator's order halves, 4 upstairs to 2 downstairs
(`order_halves_under_quotient`). This is the discrete shadow of spinor-`4π`-identity vs
director-`2π`-identity, NOT a proof of the continuous statement.

NOTE (Born intensity is NOT the cover). The cover lives in `tritAmplitude = natAbs ∘ sign`
(the 2-to-1 collapse, §1), NOT in `StandingWaveAmplitudeBridge.intensity a = a * a`. The
squaring `intensity` is INJECTIVE on `Nat` (`a ↦ a²` is strictly monotone), so it has
trivial fibres and carries NO cover: over `Nat` the phase/sign has already been quotiented
away by `natAbs` BEFORE squaring, so there is no `-a` to collide with `a`. On the trit the
squaring is moreover incidental — it merely fixes the amplitude values (`0² = 0`, `1² = 1`,
`StandingWaveAmplitudeBridge.trit_intensity_is_amplitude`) and contributes nothing to the
collapse. So `square`/`intensity` and the ℤ/2 cover are two USES of "squaring" on different
carriers — a structural parallel — but the COVER is carried by the modulus `natAbs`, not by
the squaring. Do not advertise "Born's rule = the spinor cover": as morphisms they differ
(injective squaring vs 2-to-1 modulus). The cover-ness was in the complex structure the
ledger discards at step one.

-- Next exploration:
--   The CONTINUOUS cover, the one piece deferred here. The DISCRETE real-form cover is now
--   carried by the ledger's own `tritAmplitude = natAbs ∘ sign` (`trit_is_real_form_of_z2_cover`),
--   so the open frontier is purely the continuous lift. With Mathlib, build the genuine
--   `SU(2) → SO(3)` 2:1 group homomorphism (e.g. via unit quaternions / `Quaternion`
--   acting on `ℝ³` by conjugation, or `Matrix.SpecialUnitaryGroup (Fin 2) ℂ →
--   Matrix.specialOrthogonalGroup`), and prove (i) it is surjective with kernel `{±1}`
--   (the 2:1 property — the continuous lift of §1's orbit-collapse, whose discrete real form
--   is `natAbs` identifying `{+1,-1} ↦ 1` with `0` fixed), and (ii) the
--   `2π`/`4π` periodicity as a statement about the rotation-by-angle one-parameter
--   subgroup: `exp(2π) = -I` in `SU(2)` but `= I` in `SO(3)`, `exp(4π) = I` in both (the
--   continuous lift of §3's `order_halves_under_quotient`). Then prove the DISCRETE maps
--   here are the `π₀`/order-2 shadow of that continuous cover: `square` factors through
--   `SU(2) → SO(3) → {±1}`-component, and `Fin 4 → Fin 2` is the induced map on the order-4
--   subgroup generated by `exp(2π/2)`. The hard part is real-manifold continuity and the
--   surjectivity-with-`{±1}`-kernel argument; until those are machine-checked the cover
--   stays a cited continuous picture and only its discrete shadow is proven here.
-/

end OrientationSpinorBridge
end Gnosis
