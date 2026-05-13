import Init

/-!
# Combinatorial floor for a full Kauffman-cube IUPAC atlas (118 rows)

A `KhovanovCategorifiesJones.Diagram` whose `resolutions` list is **complete** for
`n = n₊ + n₋` signed crossings has `resolutions.length = 2^n` rows (one per
`α ∈ {0,1}^n`).

To give **118** distinct resolution-table indices injectively inside such a cube,
one needs `2^n ≥ 118`. The first `n` with that property is **7**, since

`2^6 = 64 < 118 ≤ 128 = 2^7`.

This file proves only the **numeric** constraints and supplies a canonical
embedding `Fin 118 → Fin (2^7)` for hypothetical slot labeling. For a concrete
`Diagram` bookkeeping shell with `n₊ + n₋ = 7` and `128` `List.ofFn` rows, see
`Gnosis.SevenCrossingIupacShell`.  Khovanov **bracket fold split** at a resolution index:
`KhovanovCategorifiesJones.bracketResolutions_split`; peeled diagram **`jonesPoly`** with the
canonical-slot middle summand **expanded**: `SevenCrossingIupacShell.jonesPoly_sevenCrossingTaggedDiagram_rowSlotFin128_closedSummand`.

## Twelve-cycle chord carrier (**`ℤ/12ℤ`**) vs this cube

`Gnosis.AeonCycleTwelveShadow` fixes **`pairsIJ`** (**`pairsIJ_length = 66`**). Numeric sandwich
**`unordered_pairs_twelve_eq_sixty_six`**, **`sixty_six_lt_iupac_row_count`**, **`sixty_six_lt_two_pow_seven`**
records **`66 < 118 ≤ 2^7`**.

For **constructive**, **injective** interaction with **`rowSlotFin128`** (canonical **`Fin 118 → Fin 128`** slotting),
see **`Gnosis.AeonTwelveResolutionSlotEmbedding`** (**`chordGateResolutionSlot`**, **`pairsIJ_lex_rank_core_eq_idxOf`**).
For why **additive** twelve-phase clocks cannot embed as **order-`12` subgroups** of **`ℤ/128ℤ`**, see
**`AeonTwelveResolutionSlotEmbedding.twelve_not_dvd_two_pow_seven`** (Lagrange obstruction).

Hypercube-scale Gray / full chord-shear census: **`Gnosis.AeonTwelveHypercubeMajorization`**.

Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace IupacResolutionCubeBound

/-- Six crossings do not provide enough resolution rows for 118 distinct labels. -/
theorem six_crossing_resolution_slots_lt_row_count : 2 ^ 6 < 118 := by native_decide

/-- Seven crossings supply a `2^7`-fold cube — enough slots for 118 rows. -/
theorem seven_crossing_resolution_cube_covers_rows : 118 ≤ 2 ^ 7 := by native_decide

theorem two_pow_seven_eq_128 : 2 ^ 7 = 128 := by native_decide

/-- Canonical injective labeling of IUPAC rows into the `2^7` resolution slots. -/
def rowSlotFin128 (row : Fin 118) : Fin 128 :=
  ⟨row.val, Nat.lt_trans row.isLt (by decide : 118 < 128)⟩

theorem rowSlotFin128_injective : Function.Injective rowSlotFin128 := by
  intro i j h
  have hv : i.val = j.val := by simpa [rowSlotFin128] using congrArg Fin.val h
  exact Fin.ext hv

/-! ## Bridges to the twelve-point chord list (**`66`** gates)

Cardinality (**below**) plus **`Gnosis.AeonTwelveResolutionSlotEmbedding`** (**lex rank ↔ `idxOf`**, injective slot lift).
-/

/-- **`C(12,2)`** unordered pairs on twelve labeled vertices (matches **`pairsIJ_length`** there). -/
theorem unordered_pairs_twelve_eq_sixty_six : 12 * 11 / 2 = 66 := by native_decide

/-- **`66`** chord gates lie strictly below **`118`** atlas rows (**`rowSlotFin128`** injectivity targets). -/
theorem sixty_six_lt_iupac_row_count : 66 < 118 := by native_decide

/-- **`66`** chord gates lie strictly below **`2^7`** Kauffman-cube rows. -/
theorem sixty_six_lt_two_pow_seven : 66 < 2 ^ 7 := by native_decide

end IupacResolutionCubeBound
end Gnosis
