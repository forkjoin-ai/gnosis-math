/-
  HeraclitusUpDownPathWitness.lean
  =================================

  Heraclitus (trad. DK B60), *On Nature* (one English gloss + transliteration):

    “The upward and downward paths are one and the same.”

    Greek gloss: *hodos anō katō mia kai hōutē* (ι / η / ω spelling varies by edition).

  Why it stings: the fragment refuses to treat “up” and “down” as
  intrinsic predicates of the trail. On a hill, your “up” is someone else’s
  “down”; the path is the invariant, while direction is a local
  assignment from the observer’s frame. Read as a formal witness that
  perspective is metadata, not a property of the ground — the “road metric”
  as *felt ascent/descent* is observer-indexed; the same ground can wear two
  honest signs.

  Lean hook: we reuse `LiBaiQuietNightThoughtWitness.HeadTilt` as a minimal
  posture / observer-frame tag (this file depends only on that Init-only
  witness, not on Li Bai’s Chinese text).

  Repo cousins: `HeraclitusBowLifeDeathWitness` (B48 name/work tension);
  `HeraclitusRiverTwiceWitness` (B12-style flux — not the same river / not the same man);
  `LiBaiQuietNightThoughtWitness` (vertical charts + `HeadTilt`);
  `ParmenidesOnNatureWitness` (Eleatic floor vs Heraclitean flux witness).

  Zero `sorry`, zero new `axiom`.
-/

import Init
import Gnosis.LiBaiQuietNightThoughtWitness

namespace HeraclitusUpDownPathWitness

open LiBaiQuietNightThoughtWitness

/-- Local “gradient sign” only — not a claim on the path itself. -/
inductive LocalDirection where
  | callsItUp
  | callsItDown
  deriving DecidableEq, Repr

def flipDirection (d : LocalDirection) : LocalDirection :=
  match d with
  | .callsItUp => .callsItDown
  | .callsItDown => .callsItUp

theorem flipDirection_involutive (d : LocalDirection) : flipDirection (flipDirection d) = d := by
  cases d <;> rfl

/--
  Convention (witness only): map `HeadTilt` to which *label* the observer applies.
  This is not physics; it pins “metadata layer” to an existing repo type.
-/
def directionFromTilt (tilt : HeadTilt) : LocalDirection :=
  match tilt with
  | .raised => .callsItUp
  | .lowered => .callsItDown

theorem opposite_observers_disagree_on_labels :
    directionFromTilt .raised ≠ directionFromTilt .lowered := by
  simp [directionFromTilt]

/--
  Ground invariant: any fact about the path that is already established does not
  depend on which `HeadTilt` metadata you hold up beside it.
-/
theorem ground_independent_of_headTilt (FactsAboutPath : Prop) (h : FactsAboutPath)
    (_observer : HeadTilt) : FactsAboutPath :=
  h

end HeraclitusUpDownPathWitness
