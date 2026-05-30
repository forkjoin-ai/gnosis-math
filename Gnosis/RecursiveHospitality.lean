/-
  RecursiveHospitality.lean
  =========================

  The world grows UPWARD by re-applying `Gnosis.Hospitality` at each layer, where
  the OUTPUT of one layer becomes the SUBSTRATE of the next:

      dirt → life grows on it → life's detritus becomes soil → richer life → …

  Foundations that JOIN become ONE larger foundation, which permits a higher build
  (tiles on tiles, cities on cities, sky cities) — but a thing can only build on its
  own foundation. Diversity — a polyculture of companion strata, the Three Sisters
  (thriller in the canopy, filler in the middle, spiller on the ground) — is
  RESILIENT; a monoculture is fragile: a single point of failure.

  PROVEN (omega, Init-only):
    * `succession_rises`           : each layer's substrate is strictly higher
                                     (life builds on dirt, detritus on life).
    * `buildAllowance_monotone`    : a bigger foundation never permits less height.
    * `merge_never_shrinks`,
      `merge_permits_higher`       : joined foundations grow and let the skyline rise.
    * `monoculture_collapses`      : one lost species ⇒ a monoculture goes to 0.
    * `polyculture_survives`       : ≥2 companion strata ⇒ something always stands.
    * `diversity_beats_monoculture`: diversity strictly out-survives monoculture.
  WITNESSED (decide):
    * a diverse polyculture on rich detritus out-scores a lone monoculture on dirt,
      read through `Hospitality.score3` (diversity ≫ substrate ≫ height).

  No Mathlib.
-/

import Gnosis.Hospitality

namespace Gnosis
namespace RecursiveHospitality

-- ── Substrate succession: the world turns each layer's output into the next
--    layer's ground. ──────────────────────────────────────────────────────────
/-- Bare ground — where pioneers start. -/
def dirt : Nat := 0
/-- Living matter grown on the layer below. -/
def life : Nat := 1
/-- The material detritus life leaves behind — the richer substrate it builds. -/
def detritus : Nat := 2

/-- A built layer's material becomes the substrate for the next (succession). -/
def nextSubstrate (current : Nat) : Nat := current + 1

/-- Succession strictly rises: you always end one substrate-level higher than the
    layer you grew on — never lower. -/
theorem succession_rises (s : Nat) : s < nextSubstrate s := by
  unfold nextSubstrate
  omega

-- ── Build only on your foundation; foundations that join grow. ────────────────
/-- A thing can build only as high as its foundation supports. -/
def buildAllowance (foundation : Nat) : Nat := foundation

/-- A bigger foundation never permits a lower build. -/
theorem buildAllowance_monotone (a b : Nat) (h : a ≤ b) :
    buildAllowance a ≤ buildAllowance b := by
  unfold buildAllowance
  omega

/-- Foundations that join become ONE larger foundation. -/
def mergeFoundations (a b : Nat) : Nat := a + b

/-- Merging never shrinks a foundation. -/
theorem merge_never_shrinks (a b : Nat) :
    a ≤ mergeFoundations a b ∧ b ≤ mergeFoundations a b := by
  unfold mergeFoundations
  omega

/-- A merged foundation permits building at least as high as either piece alone —
    joining foundations is exactly what lets the skyline rise (cities on cities). -/
theorem merge_permits_higher (a b : Nat) :
    buildAllowance a ≤ buildAllowance (mergeFoundations a b)
    ∧ buildAllowance b ≤ buildAllowance (mergeFoundations a b) := by
  unfold buildAllowance mergeFoundations
  omega

-- ── Diversity (Three Sisters) vs monoculture: resilience. ─────────────────────
-- A site is held up by `companions` distinct strata — the Three Sisters: thriller
-- (canopy), filler (middle), spiller (ground). Count the strata still standing
-- after a shock (disease, fire) removes ONE companion.
/-- Strata still standing after one companion is lost (Nat: 1 companion → 0). -/
def survivingCompanions (companions : Nat) : Nat := companions - 1

/-- A MONOCULTURE — one companion, one stratum — collapses to nothing when its single
    species is lost. The fragile case. -/
theorem monoculture_collapses : survivingCompanions 1 = 0 := by
  unfold survivingCompanions
  omega

/-- A POLYCULTURE — ≥2 companion strata (at least two of the Three Sisters) — survives
    the loss of any one: something is always still standing. -/
theorem polyculture_survives (companions : Nat) (h : 2 ≤ companions) :
    1 ≤ survivingCompanions companions := by
  unfold survivingCompanions
  omega

/-- Diversity strictly beats monoculture under loss — the polyculture keeps strata a
    monoculture cannot. This is why a living world favours the Three Sisters over a
    fragile monoculture. -/
theorem diversity_beats_monoculture (companions : Nat) (h : 2 ≤ companions) :
    survivingCompanions 1 < survivingCompanions companions := by
  unfold survivingCompanions
  omega

-- ── Tie-back: recursive hospitality reads as Hospitality.score3. ──────────────
-- The three lexicographic tiers are (surviving diversity ≫ substrate richness ≫
-- build height): a resilient, well-substrated, build-ready site is most hospitable.
/-- A diverse polyculture on rich detritus (surviving strata 2 = three sisters minus
    one, substrate 2 = detritus) is strictly more hospitable than a lone monoculture
    on bare dirt (surviving 0, substrate 0) — even where the monoculture sat on a
    taller (999) foundation. Diversity + substrate dominate raw height. -/
theorem polyculture_on_detritus_wins :
    Hospitality.score3 0 0 999 < Hospitality.score3 2 2 0 := by
  decide

end RecursiveHospitality
end Gnosis
