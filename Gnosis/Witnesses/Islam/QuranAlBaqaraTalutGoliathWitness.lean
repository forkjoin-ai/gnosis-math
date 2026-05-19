import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraTalutGoliathWitness

/-!
# Quran 2:246-252, Al-Baqara -- Talut, River Test, Goliath, David

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1905-1945`.

This witness tracks Israel's request for a king, reluctance once fighting is
commanded, Talut's appointment over objections of status and wealth, knowledge
and stature as divine choice, Ark tranquillity as sign, the river test, the small
faithful force against Goliath, prayer for patience and firmness, David killing
Goliath, sovereignty, wisdom, and God's prevention of earth's corruption.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive TalutGoliathMoment
  | kingRequested
  | fightingReluctance
  | talutAppointed
  | knowledgeStatureAuthority
  | arkSignTranquillity
  | riverTest
  | smallForceFaith
  | patienceFirmnessPrayer
  | davidKillsGoliath
  | sovereigntyWisdom
  | corruptionPrevented
  | revelationsTruth
deriving DecidableEq, Repr

def talutGoliathMoments : List TalutGoliathMoment :=
  [ .kingRequested, .fightingReluctance, .talutAppointed, .knowledgeStatureAuthority
  , .arkSignTranquillity, .riverTest, .smallForceFaith, .patienceFirmnessPrayer
  , .davidKillsGoliath, .sovereigntyWisdom, .corruptionPrevented, .revelationsTruth ]

theorem quran_al_baqara_talut_goliath_witness :
    talutGoliathMoments.length = 12
    ∧ talutGoliathMoments.head? = some .kingRequested
    ∧ talutGoliathMoments.getLast? = some .revelationsTruth := by
  exact ⟨rfl, rfl, rfl⟩

end QuranAlBaqaraTalutGoliathWitness
end Gnosis.Witnesses.Islam
