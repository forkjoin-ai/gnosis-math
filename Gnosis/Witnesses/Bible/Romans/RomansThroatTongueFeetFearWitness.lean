import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansThroatTongueFeetFearWitness

/-!
# Romans 3:13-18 (KJV) -- Throat, Tongue, Feet, and Fear

This unit gives one bounded bodily-catalogue topology:

  * throat, tongue, lips, and mouth are marked by death, deceit, poison, cursing,
    and bitterness;
  * feet are swift to shed blood;
  * destruction and misery are in their ways;
  * the way of peace is unknown;
  * there is no fear of God before their eyes.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 3:13-18 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_3_13_18_quote : String :=
  "3:13 Their throat is an open sepulchre; with their tongues they have " ++
  "used deceit; the poison of asps is under their lips: 3:14 Whose mouth " ++
  "is full of cursing and bitterness: 3:15 Their feet are swift to shed " ++
  "blood: 3:16 Destruction and misery are in their ways: 3:17 And the " ++
  "way of peace have they not known: 3:18 There is no fear of God " ++
  "before their eyes."

/-! ## Section 1: Speech organs -/

/-- Speech-related bodily markers in Romans 3:13-14. -/
inductive SpeechMarker
  | throatOpenSepulchre
  | tonguesUsedDeceit
  | poisonOfAspsUnderLips
  | mouthFullOfCursingBitterness
deriving DecidableEq, Repr

/-- Speech markers in source order. -/
def speechMarkers : List SpeechMarker :=
  [ SpeechMarker.throatOpenSepulchre
  , SpeechMarker.tonguesUsedDeceit
  , SpeechMarker.poisonOfAspsUnderLips
  , SpeechMarker.mouthFullOfCursingBitterness
  ]

/-- The speech chain begins with the throat as open sepulchre. -/
theorem speech_begins_with_throat_sepulchre :
    speechMarkers.head? = some SpeechMarker.throatOpenSepulchre := rfl

/-- The speech chain closes with the mouth full of cursing and bitterness. -/
theorem speech_closes_with_cursing_bitterness :
    speechMarkers.getLast? =
      some SpeechMarker.mouthFullOfCursingBitterness := rfl

/-! ## Section 2: Ways and feet -/

/-- Movement and way markers in Romans 3:15-17. -/
structure WayViolencePattern where
  feetSwiftToShedBlood : Bool
  destructionAndMiseryInWays : Bool
  wayOfPeaceNotKnown : Bool
deriving DecidableEq, Repr

/-- Feet, ways, and peace are bound in a violence pattern. -/
def wayViolencePattern : WayViolencePattern where
  feetSwiftToShedBlood := true
  destructionAndMiseryInWays := true
  wayOfPeaceNotKnown := true

/-- The way pattern names swift bloodshed, destruction, misery, and no peace. -/
theorem violent_ways_no_peace :
    wayViolencePattern.feetSwiftToShedBlood = true
    ∧ wayViolencePattern.destructionAndMiseryInWays = true
    ∧ wayViolencePattern.wayOfPeaceNotKnown = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 3: No fear before eyes -/

/-- The concluding fear-of-God negation in Romans 3:18. -/
structure FearBeforeEyes where
  noFearOfGod : Bool
  beforeTheirEyes : Bool
deriving DecidableEq, Repr

/-- There is no fear of God before their eyes. -/
def fearBeforeEyes : FearBeforeEyes where
  noFearOfGod := true
  beforeTheirEyes := true

/-- The closing negation locates no fear before their eyes. -/
theorem no_fear_of_god_before_eyes :
    fearBeforeEyes.noFearOfGod = true
    ∧ fearBeforeEyes.beforeTheirEyes = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 4: Master witness -/

/-- The bounded Romans 3:13-18 witness. -/
theorem romans_throat_tongue_feet_fear_witness :
    speechMarkers.length = 4
    ∧ speechMarkers.head? = some SpeechMarker.throatOpenSepulchre
    ∧ speechMarkers.getLast? =
      some SpeechMarker.mouthFullOfCursingBitterness
    ∧ wayViolencePattern.feetSwiftToShedBlood = true
    ∧ wayViolencePattern.destructionAndMiseryInWays = true
    ∧ wayViolencePattern.wayOfPeaceNotKnown = true
    ∧ fearBeforeEyes.noFearOfGod = true
    ∧ fearBeforeEyes.beforeTheirEyes = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end RomansThroatTongueFeetFearWitness
end Gnosis.Witnesses.Bible.Romans
