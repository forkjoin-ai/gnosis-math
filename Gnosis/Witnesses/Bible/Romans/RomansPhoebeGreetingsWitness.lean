namespace Gnosis.Witnesses.Bible.Romans
namespace RomansPhoebeGreetingsWitness

/-!
# Romans 16 -- Phoebe, House-Church Network, Division Firewall, and Doxology

Source slice: Romans 16:1-27.

Invariant: the greetings are not filler. Phoebe carries the letter as servant
and succourer; Priscilla and Aquila expose risk-bearing house-church topology;
named laborers make memory auditable instead of abstract. Hospitality is not
soft scenery: Gaius hosts the whole church, and the network has faces.

Counterproof: smooth speech is a belly-routing exploit. After all the doctrine,
Paul still installs a division firewall: mark offences contrary to learned
teaching, avoid the charming splitter, be wise to good and simple concerning
evil. The closing mystery is not private gnosis; it is once-kept secret now
manifest to all nations for obedience of faith.

No `sorry`, no new `axiom`.
-/

structure NamedNetworkHospitality where
  phoebeCommendedForReception : Bool := true
  phoebeSuccourerOfMany : Bool := true
  priscillaAquilaRiskNecks : Bool := true
  houseChurchesNamed : Bool := true
  laborersAndPrisonersRemembered : Bool := true
  gaiusHostsWholeChurch : Bool := true
  tertiusScribeSalutes : Bool := true
deriving DecidableEq, Repr

def namedNetworkHospitality : NamedNetworkHospitality := {}

def greetingsExposeRealTopology (n : NamedNetworkHospitality) : Prop :=
  n.phoebeCommendedForReception = true ∧
  n.phoebeSuccourerOfMany = true ∧
  n.priscillaAquilaRiskNecks = true ∧
  n.houseChurchesNamed = true ∧
  n.laborersAndPrisonersRemembered = true ∧
  n.gaiusHostsWholeChurch = true ∧
  n.tertiusScribeSalutes = true

structure DivisionDoxologyFirewall where
  divisiveOffencesMarked : Bool := true
  fairSpeechDeceivesSimpleHearts : Bool := true
  wiseToGoodSimpleConcerningEvil : Bool := true
  peaceBruisesSatanUnderFeet : Bool := true
  mysteryOnceSecretNowManifest : Bool := true
  propheticScripturesKnownToNations : Bool := true
  obedienceOfFaithClosesBook : Bool := true
deriving DecidableEq, Repr

def divisionDoxologyFirewall : DivisionDoxologyFirewall := {}

def doctrineEndsWithNetworkHygiene (d : DivisionDoxologyFirewall) : Prop :=
  d.divisiveOffencesMarked = true ∧
  d.fairSpeechDeceivesSimpleHearts = true ∧
  d.wiseToGoodSimpleConcerningEvil = true ∧
  d.peaceBruisesSatanUnderFeet = true ∧
  d.mysteryOnceSecretNowManifest = true ∧
  d.propheticScripturesKnownToNations = true ∧
  d.obedienceOfFaithClosesBook = true

theorem romans_greetings_expose_real_topology :
    greetingsExposeRealTopology namedNetworkHospitality := by
  unfold greetingsExposeRealTopology namedNetworkHospitality
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem romans_doctrine_ends_with_network_hygiene :
    doctrineEndsWithNetworkHygiene divisionDoxologyFirewall := by
  unfold doctrineEndsWithNetworkHygiene divisionDoxologyFirewall
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem romans_phoebe_greetings_witness :
    greetingsExposeRealTopology namedNetworkHospitality ∧
    doctrineEndsWithNetworkHygiene divisionDoxologyFirewall := by
  exact ⟨romans_greetings_expose_real_topology,
    romans_doctrine_ends_with_network_hygiene⟩

end RomansPhoebeGreetingsWitness
end Gnosis.Witnesses.Bible.Romans
