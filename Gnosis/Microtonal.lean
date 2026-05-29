/-
  Microtonal.lean
  ===============

  Beyond the twelve: quartertones and the Arabic maqam. Init-only, zero sorry.

  Equal temperament need not stop at twelve. The 24-tone system divides the octave
  into quartertones (50 cents each); the familiar 12-TET sits inside it as the even
  positions. What 24-TET buys is the NEUTRAL third (7 quartertones = 350 cents),
  the note halfway between minor (300) and major (400) — the colour of maqam Sikah
  and the third of jins Rast, audibly "in the crack" and unreachable on the piano.

  This extends ChromaticChord's Z/12 to Z/24, with 12-TET as the index-2 subgroup.
-/

namespace Microtonal

/-- Quartertones per octave. -/
def octave24 : Nat := 24

/-- Cents of a quartertone interval (50 cents per step). -/
def qcents (steps : Nat) : Nat := 50 * steps

/-- A 24-TET position belongs to 12-TET exactly when it is an even quartertone. -/
def isTwelveTET (q : Nat) : Bool := q % 2 == 0

def minorThird24 : Nat := 6  -- 300 cents
def neutralThird : Nat := 7  -- 350 cents — the maqam third
def majorThird24 : Nat := 8  -- 400 cents

/-- 12-TET embeds in 24-TET as the even positions (the index-2 subgroup). -/
theorem twelve_embeds_in_twentyfour :
    ([0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22].all (fun q => isTwelveTET q)) = true := by
  decide

/-- The neutral third sits exactly between the minor and major thirds. -/
theorem neutral_third_is_between :
    qcents minorThird24 < qcents neutralThird ∧ qcents neutralThird < qcents majorThird24 := by
  decide

/-- And it is genuinely microtonal — an odd quartertone, NOT in 12-TET (no piano
    key for it). -/
theorem neutral_third_is_microtonal : isTwelveTET neutralThird = false := by decide

/-- 350 cents, the half-flat third. -/
theorem neutral_third_cents : qcents neutralThird = 350 := by decide

/-- Jins Rast — the lower tetrachord of maqam Rast — steps whole, 3/4-tone,
    3/4-tone (4,3,3 quartertones) and spans a perfect fourth (500 cents). -/
def jinsRast : List Nat := [4, 3, 3]

theorem jins_rast_spans_a_fourth :
    jinsRast.foldl (· + ·) 0 = 10 ∧ qcents 10 = 500 := by decide

/-- Maqam Rast as quartertone positions: C D Eˀ F G A Bˀ (neutral 3rd and 7th). -/
def maqamRast : List Nat := [0, 4, 7, 10, 14, 18, 21]

theorem rast_has_seven_notes : maqamRast.length = 7 := by decide

/-- Rast takes the neutral third (7), not the major third (8) — its signature. -/
theorem rast_uses_the_neutral_third :
    maqamRast.contains 7 = true ∧ maqamRast.contains 8 = false := by decide

end Microtonal
