import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraMessengersThroneLightWitness

/-!
# Quran 2:253-257, Al-Baqara -- Messengers, Throne Verse, No Compulsion, Light

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1946-1975`.

This witness tracks ranked messengers, Jesus' clear signs and holy spirit,
successor disagreement, giving before the no-bargaining Day, the Throne Verse:
Ever Living, Ever Watchful, no slumber or sleep, universal ownership, intercession
by leave, knowledge, throne, preservation, Most High and Tremendous, then no
compulsion, firm handhold, God as ally bringing believers from darkness to light,
and false-god allies taking disbelievers from light to darkness and Fire.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive MessengersThroneLightMoment
  | messengersFavored
  | jesusClearSigns
  | disagreementAfterSigns
  | giveBeforeDay
  | noGodButEverLiving
  | noSlumberSleep
  | intercessionByLeave
  | thronePreserves
  | noCompulsionFirmHandhold
  | godAllyLight
  | falseAlliesFire
deriving DecidableEq, Repr

def messengersThroneLightMoments : List MessengersThroneLightMoment :=
  [ .messengersFavored, .jesusClearSigns, .disagreementAfterSigns, .giveBeforeDay
  , .noGodButEverLiving, .noSlumberSleep, .intercessionByLeave, .thronePreserves
  , .noCompulsionFirmHandhold, .godAllyLight, .falseAlliesFire ]

theorem quran_al_baqara_messengers_throne_light_witness :
    messengersThroneLightMoments.length = 11
    ∧ messengersThroneLightMoments.head? = some .messengersFavored
    ∧ messengersThroneLightMoments.getLast? = some .falseAlliesFire := by
  exact ⟨rfl, rfl, rfl⟩

end QuranAlBaqaraMessengersThroneLightWitness
end Gnosis.Witnesses.Islam
