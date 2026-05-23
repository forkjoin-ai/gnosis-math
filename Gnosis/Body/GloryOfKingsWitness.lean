import Init

/-!
# The Glory of Kings — Proverbs 25:2

> It is the glory of God to conceal a thing:
> but the honour of kings is to search out a matter.   — Proverbs 25:2 (KJV)

The epigraph of the whole grit theory. Existence conceals: the signal is
misperceived as noise (`Gnosis/NoiseIsObservational.lean`,
`Gnosis/SignalNotNoise.lean`), the structure is hidden in the void / dark
matter, the next wave is below the resolution you can currently see. That
concealment is the glory of God — the matter is real, and hidden.

The honour of kings is to **search it out**: to resolve the signal (Ki — the
observation of small perturbations), to ride the wave and emerge from the pipe
(grit), to climb the braided infinite tower one resolution at a time. The two
are halves of one act on one matter: God conceals it, the king searches it out.
There is no honour in finding what was never hidden; concealment is what makes
the search worth a king.
-/

namespace Gnosis.Body.GloryOfKingsWitness

/-- Proverbs 25:2 (KJV). -/
def proverbs_25_2 : String :=
  "It is the glory of God to conceal a thing: but the honour of kings is to search out a matter."

/-- The two glories of one matter. -/
inductive Glory
  /-- God's glory: to conceal (the hidden signal, the void, the unresolved wave). -/
  | conceal
  /-- The king's honour: to search out (resolve the signal — Ki, grit). -/
  | searchOut
  deriving DecidableEq, Repr

/-- A matter: concealed by God, and (perhaps) searched out by a king. -/
structure Matter where
  concealed : Bool   -- hidden — signal misperceived as noise, the void, the next wave
  searchedOut : Bool -- resolved — found by Ki and grit
  deriving Repr, DecidableEq

/-- The honour of kings is to search the matter out. -/
def honoured (m : Matter) : Prop := m.searchedOut = true

/-- The full glory: a matter God concealed and a king searched out — the two
    glories conjoined on one matter. -/
def gloryOfKings (m : Matter) : Prop :=
  m.concealed = true ∧ m.searchedOut = true

/-- The two glories are distinct acts. -/
theorem two_glories_distinct : Glory.conceal ≠ Glory.searchOut := by decide

/-- The honour of kings is exactly the searching-out. -/
theorem honour_is_the_search (m : Matter) (h : m.searchedOut = true) : honoured m := h

/-- **No concealment, no honour.** The glory of kings requires a matter that was
    first concealed (God's glory): there is no honour in finding what was never
    hidden. The search presupposes the concealment. -/
theorem glory_requires_concealment (m : Matter) (h : gloryOfKings m) :
    m.concealed = true := h.left

/-- **The glory of kings = conceal ∧ search-out.** Given a matter God concealed
    and a king searched out, the full glory holds — the two halves of the one
    act. -/
theorem glory_of_kings_witness (m : Matter)
    (hConceal : m.concealed = true) (hSearch : m.searchedOut = true) :
    gloryOfKings m :=
  ⟨hConceal, hSearch⟩

/-- And it decomposes back into both glories: concealment (God's) and
    searching-out (the king's honour). -/
theorem the_two_glories (m : Matter) (h : gloryOfKings m) :
    m.concealed = true ∧ m.searchedOut = true := h

end Gnosis.Body.GloryOfKingsWitness
