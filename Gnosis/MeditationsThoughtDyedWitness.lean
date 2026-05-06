/-
  MeditationsThoughtDyedWitness.lean
  ==================================

  Marcus Aurelius, *Meditations* 5.16 (tr. Long / Haines, common paraphrase):

    “The soul becomes dyed with the color of its thoughts.”

  **Finitary model:** each admitted thought carries a non-negative **tint**
  (`Nat`); the soul’s recorded hue is the running **supremum** (`Nat.max`).
  Successive thoughts **monotone** the dye — no separate “soul pigment” beyond
  what the trace admits. This is the honest discrete spine for “you become what
  you rehearse.”

  **Same verse, two repo neighbors (re your overflow vs void contrast):**

  * **Rumination / consciousness overflow** (`LocalizedOverflowConsciousness`):
    long conscious traces where structured signal exceeds stable capacity — the
    Aurelius line read as **too much dye volume**: the loom keeps taking pigment
    (`rumination_is_conscious_local_overflow`).

  * **Catullan explanatory void** (`CatullusOdiEtAmoWitness`): torment with an
    empty *why* slot — the line read as **affect without the color of a reason**;
    not saturation, but missing chart next to feeling.

  * **Training saturation** (`TrainingSaturation`): same “trace reshapes you”
    moral on a different carrier — energy headroom vs McNally wall; see that
    file’s module doc.

  * **Mencken conscience shadow** (`MenckenConscienceShadowWitness`): “inner voice”
    as **social detection** telemetry — not dye volume, but *who might be watching*
    feeding the loop; cousin to rumination only at the level of **self-monitoring**
    noise, not identical math.

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace MeditationsThoughtDyedWitness

/-- One admittance of a thought-tint updates the soul’s recorded upper hue. -/
def applyThoughtDye (soulHue thoughtHue : Nat) : Nat :=
  Nat.max soulHue thoughtHue

theorem applyThoughtDye_ge_left (s t : Nat) : s ≤ applyThoughtDye s t :=
  Nat.le_max_left s t

theorem applyThoughtDye_ge_right (s t : Nat) : t ≤ applyThoughtDye s t :=
  Nat.le_max_right s t

theorem applyThoughtDye_idem (s : Nat) : applyThoughtDye s s = s :=
  Nat.max_self s

/-- Soul hue after a finite thought trace, starting from undyed `0`. -/
def soulHueAfterThoughts (thoughts : List Nat) : Nat :=
  thoughts.foldl applyThoughtDye 0

theorem soulHue_monotone_snoc (xs : List Nat) (t : Nat) :
    soulHueAfterThoughts xs ≤ soulHueAfterThoughts (xs ++ [t]) := by
  have hsnoc :
      soulHueAfterThoughts (xs ++ [t]) = applyThoughtDye (soulHueAfterThoughts xs) t := by
    simp [soulHueAfterThoughts, applyThoughtDye, List.foldl_append]
  rw [hsnoc]
  exact applyThoughtDye_ge_left _ _

end MeditationsThoughtDyedWitness
