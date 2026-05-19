import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansGreetingSanctifiedWitness

/-!
# 1 Corinthians 1:1-3 (KJV) -- Greeting, Sanctified, Called Saints

This unit gives one bounded greeting topology:

  * Paul is called to be an apostle of Jesus Christ through the will of God;
  * Sosthenes is named as brother;
  * the address is to the church of God at Corinth;
  * the recipients are sanctified in Christ Jesus and called saints;
  * the scope includes all who call on the name of Jesus Christ our Lord;
  * the greeting gives grace and peace from God the Father and the Lord Jesus Christ.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- 1 Corinthians 1:1-3 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def first_corinthians_1_1_3_quote : String :=
  "1:1 Paul, called to be an apostle of Jesus Christ through the will of " ++
  "God, and Sosthenes our brother, 1:2 Unto the church of God which is " ++
  "at Corinth, to them that are sanctified in Christ Jesus, called to be " ++
  "saints, with all that in every place call upon the name of Jesus " ++
  "Christ our Lord, both theirs and ours: 1:3 Grace be unto you, and " ++
  "peace, from God our Father, and from the Lord Jesus Christ."

/-! ## Section 1: Sender and address -/

/-- The sender pattern in 1 Corinthians 1:1. -/
structure SenderPattern where
  paulCalledApostle : Bool
  throughWillOfGod : Bool
  sosthenesBrotherNamed : Bool
deriving DecidableEq, Repr

/-- Paul and Sosthenes are named in the opening sender line. -/
def senderPattern : SenderPattern where
  paulCalledApostle := true
  throughWillOfGod := true
  sosthenesBrotherNamed := true

/-- The address pattern in 1 Corinthians 1:2. -/
structure CorinthAddressPattern where
  churchOfGodAtCorinth : Bool
  sanctifiedInChristJesus : Bool
  calledSaints : Bool
  allEveryPlaceCallName : Bool
  jesusChristLordTheirsAndOurs : Bool
deriving DecidableEq, Repr

/-- The Corinth address includes sanctification, calling, and wider invocation. -/
def corinthAddressPattern : CorinthAddressPattern where
  churchOfGodAtCorinth := true
  sanctifiedInChristJesus := true
  calledSaints := true
  allEveryPlaceCallName := true
  jesusChristLordTheirsAndOurs := true

/-! ## Section 2: Grace and peace -/

/-- The blessing pattern in 1 Corinthians 1:3. -/
structure GracePeacePattern where
  graceUntoYou : Bool
  peaceUntoYou : Bool
  fromGodOurFather : Bool
  fromLordJesusChrist : Bool
deriving DecidableEq, Repr

/-- Grace and peace come from God the Father and the Lord Jesus Christ. -/
def gracePeacePattern : GracePeacePattern where
  graceUntoYou := true
  peaceUntoYou := true
  fromGodOurFather := true
  fromLordJesusChrist := true

/-! ## Section 3: Master witness -/

/-- The bounded 1 Corinthians 1:1-3 witness. -/
theorem first_corinthians_greeting_sanctified_witness :
    senderPattern.paulCalledApostle = true
    ∧ senderPattern.throughWillOfGod = true
    ∧ senderPattern.sosthenesBrotherNamed = true
    ∧ corinthAddressPattern.churchOfGodAtCorinth = true
    ∧ corinthAddressPattern.sanctifiedInChristJesus = true
    ∧ corinthAddressPattern.calledSaints = true
    ∧ corinthAddressPattern.allEveryPlaceCallName = true
    ∧ corinthAddressPattern.jesusChristLordTheirsAndOurs = true
    ∧ gracePeacePattern.graceUntoYou = true
    ∧ gracePeacePattern.peaceUntoYou = true
    ∧ gracePeacePattern.fromGodOurFather = true
    ∧ gracePeacePattern.fromLordJesusChrist = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansGreetingSanctifiedWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
