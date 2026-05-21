namespace Gnosis.Witnesses.Mandaean
namespace MandaeanJordanVoiceJohnWitness

/-!
# Mandaean Book of John -- Jordan Voice and Johannine Background Topology

Source slice:
- `docs/ebooks/source-texts/mandaean-book-of-john-haberl-mcgrath.pdf`,
  sections 8-9: "A Voice Came to Me in the Jordan" and "Whom Shall I Call,
  Who Would Answer Me".
- Background comparison: KJV John 1:19-34, John 3:22-30, John 10:40-42.

Invariant: the Mandaean Book of John is a baptismal voice topology before it is
a set of "John the Baptist legends." Voice arrives in the Jordan, light becomes
abundant in the world, baptism can set a disturbed claimant straight, and the
Great Life remains the source whose name authorizes relief and recognition.

Johannine bridge, stated carefully: this does not prove dependence between the
Mandaean text and the New Testament Gospel of John. It records a shared topology
worth using as background while reading the Gospel: John is a voice/witness
carrier at Jordan; water is a manifestation boundary; the real authority is not
the carrier's ego but the one from above / the Great Life / the source that
authorizes the witness. The Gospel's "he must increase, but I must decrease"
and the Mandaean correction of unauthorized forgiveness rhyme as anti-capture
logic around the baptismal office.

Counterproof: the naive reading asks which community "owns" John. The witness
topology asks a better question: what happens when a baptismal carrier confuses
office, name, water, and source? The answer is boundary discipline. The voice
may shake worlds; the Jordan may be precious; but the carrier is not the source.

No `sorry`, no new `axiom`.
-/

structure MandaeanJordanVoice where
  voiceCameInJordan : Bool := true
  lightAbundantInWorld : Bool := true
  splendidPlantStandsAtGate : Bool := true
  gateOpenedInSplendor : Bool := true
  feetGroundedOnTruth : Bool := true
  baptismInJordanEstablished : Bool := true
deriving DecidableEq, Repr

def mandaeanJordanVoice : MandaeanJordanVoice := {}

def jordanVoiceManifestsLight (j : MandaeanJordanVoice) : Prop :=
  j.voiceCameInJordan = true ∧
  j.lightAbundantInWorld = true ∧
  j.splendidPlantStandsAtGate = true ∧
  j.gateOpenedInSplendor = true ∧
  j.feetGroundedOnTruth = true ∧
  j.baptismInJordanEstablished = true

structure LifeAuthorizationBoundary where
  greatLifeNameAuthorizesRelief : Bool := true
  baptismCanSetDisturbedMindStraight : Bool := true
  unauthorizedForgivenessRejected : Bool := true
  preciousJordanNamed : Bool := true
  soothingWordsReturnToFather : Bool := true
  lifePraisedAndTriumphant : Bool := true
deriving DecidableEq, Repr

def lifeAuthorizationBoundary : LifeAuthorizationBoundary := {}

def baptismalOfficeNeedsSourceAuthority (l : LifeAuthorizationBoundary) : Prop :=
  l.greatLifeNameAuthorizesRelief = true ∧
  l.baptismCanSetDisturbedMindStraight = true ∧
  l.unauthorizedForgivenessRejected = true ∧
  l.preciousJordanNamed = true ∧
  l.soothingWordsReturnToFather = true ∧
  l.lifePraisedAndTriumphant = true

structure JohannineBackgroundBridge where
  gospelJohnHasVoiceAtJordan : Bool := true
  gospelJohnWitnessDeniesBeingChrist : Bool := true
  gospelJohnWaterBaptismManifestsAnother : Bool := true
  gospelJohnSpiritDescentTransfersWitness : Bool := true
  gospelJohnIncreaseDecreaseAntiCapture : Bool := true
  gospelJohnReturnsBeyondJordanToFirstBaptismPlace : Bool := true
  dependenceClaimWithheld : Bool := true
deriving DecidableEq, Repr

def johannineBackgroundBridge : JohannineBackgroundBridge := {}

def sharedTopologyWithoutDependenceClaim (b : JohannineBackgroundBridge) : Prop :=
  b.gospelJohnHasVoiceAtJordan = true ∧
  b.gospelJohnWitnessDeniesBeingChrist = true ∧
  b.gospelJohnWaterBaptismManifestsAnother = true ∧
  b.gospelJohnSpiritDescentTransfersWitness = true ∧
  b.gospelJohnIncreaseDecreaseAntiCapture = true ∧
  b.gospelJohnReturnsBeyondJordanToFirstBaptismPlace = true ∧
  b.dependenceClaimWithheld = true

theorem mandaean_jordan_voice_manifests_light :
    jordanVoiceManifestsLight mandaeanJordanVoice := by
  unfold jordanVoiceManifestsLight mandaeanJordanVoice
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mandaean_baptismal_office_needs_source_authority :
    baptismalOfficeNeedsSourceAuthority lifeAuthorizationBoundary := by
  unfold baptismalOfficeNeedsSourceAuthority lifeAuthorizationBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mandaean_johannine_shared_topology_without_dependence :
    sharedTopologyWithoutDependenceClaim johannineBackgroundBridge := by
  unfold sharedTopologyWithoutDependenceClaim johannineBackgroundBridge
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mandaean_jordan_voice_john_witness :
    jordanVoiceManifestsLight mandaeanJordanVoice ∧
    baptismalOfficeNeedsSourceAuthority lifeAuthorizationBoundary ∧
    sharedTopologyWithoutDependenceClaim johannineBackgroundBridge := by
  exact ⟨mandaean_jordan_voice_manifests_light,
    mandaean_baptismal_office_needs_source_authority,
    mandaean_johannine_shared_topology_without_dependence⟩

end MandaeanJordanVoiceJohnWitness
end Gnosis.Witnesses.Mandaean
