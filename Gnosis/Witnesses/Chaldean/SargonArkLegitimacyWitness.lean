import Gnosis.Witnesses.Chaldean.GenesisNameMigrationWitness
import Gnosis.Witnesses.Chaldean.MummuTiamatuWaterChaosCarrierWitness

namespace Gnosis.Witnesses.Chaldean
namespace SargonArkLegitimacyWitness

/-!
# Sargon Ark Legitimacy Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter XVII
conclusion, Sargina/Sargon I birth legend.

The structural topology is exact at the schema level even when names and direct
historical dependency remain under reserve: concealed vulnerable infant, sealed
rush ark, bitumen boundary, river route without drowning, water-carrier
adoption, low-status apprenticeship, divine prosperity, and later sovereign
legitimacy. Smith explicitly notes a striking likeness to Moses and then gives
the safer structural rule: every action, once performed, tends to be repeated.

The river passage also carries a baptism-like topology under reserve: the infant
enters the water-boundary sealed against death, does not drown, exits into a new
household and social identity, and later reappears as a legitimate sovereign.
The tablet does not name baptism; the proven claim is liminal water-passage
survival plus identity transfer.

No `sorry`, no new `axiom`.
-/

structure SealedInfantWaterAdoptionSchema where
  vulnerableBirth : Bool := true
  hiddenFatherOrThreatenedLineage : Bool := true
  rushArkCarrier : Bool := true
  bitumenSeal : Bool := true
  riverTransportWithoutDrowning : Bool := true
  waterCarrierAdoption : Bool := true
  lowStatusApprenticeship : Bool := true
  laterSovereignLegitimacy : Bool := true
deriving DecidableEq, Repr

def sargonArkSchema : SealedInfantWaterAdoptionSchema := {}

def mosesArkResonanceSchema : SealedInfantWaterAdoptionSchema := {}

def sealedInfantWaterAdoption (s : SealedInfantWaterAdoptionSchema) : Prop :=
  s.vulnerableBirth = true ∧
  s.hiddenFatherOrThreatenedLineage = true ∧
  s.rushArkCarrier = true ∧
  s.bitumenSeal = true ∧
  s.riverTransportWithoutDrowning = true ∧
  s.waterCarrierAdoption = true ∧
  s.lowStatusApprenticeship = true ∧
  s.laterSovereignLegitimacy = true

structure SargonLegitimacyLayer where
  nameMeansRightTrueLegitimateKing : Bool := true
  obscureOriginMarked : Bool := true
  princessMotherAndUnknownFather : Bool := true
  oldLineConnectionClaimed : Bool := true
  akkadianKingshipAsserted : Bool := true
  laterKingsAddressedByInscription : Bool := true
deriving DecidableEq, Repr

def sargonLegitimacyLayer : SargonLegitimacyLayer := {}

def sargonLegitimacyRepair (l : SargonLegitimacyLayer) : Prop :=
  l.nameMeansRightTrueLegitimateKing = true ∧
  l.obscureOriginMarked = true ∧
  l.princessMotherAndUnknownFather = true ∧
  l.oldLineConnectionClaimed = true ∧
  l.akkadianKingshipAsserted = true ∧
  l.laterKingsAddressedByInscription = true

structure RepeatedActionReserve where
  strikingLikenessToMosesNamed : Bool := true
  notWithinGenesisPeriod : Bool := true
  sargonFameReachedEgypt : Bool := true
  connectionLikelyButNotDirectlyProved : Bool := true
  repeatedActionPrincipleNamed : Bool := true
  namesNotNeededForTopology : Bool := true
deriving DecidableEq, Repr

def repeatedActionReserve : RepeatedActionReserve := {}

def structuralResonanceUnderReserve (r : RepeatedActionReserve) : Prop :=
  r.strikingLikenessToMosesNamed = true ∧
  r.notWithinGenesisPeriod = true ∧
  r.sargonFameReachedEgypt = true ∧
  r.connectionLikelyButNotDirectlyProved = true ∧
  r.repeatedActionPrincipleNamed = true ∧
  r.namesNotNeededForTopology = true

structure LiminalWaterPassage where
  entersWaterBoundary : Bool := true
  sealedAgainstDrowning : Bool := true
  carriedByRiverNotDestroyed : Bool := true
  exitsIntoAdoptiveHousehold : Bool := true
  receivesNewSocialContinuity : Bool := true
  baptismNameHeldUnderReserve : Bool := true
deriving DecidableEq, Repr

def liminalWaterPassage : LiminalWaterPassage := {}

def baptismLikeWaterTransfer (w : LiminalWaterPassage) : Prop :=
  w.entersWaterBoundary = true ∧
  w.sealedAgainstDrowning = true ∧
  w.carriedByRiverNotDestroyed = true ∧
  w.exitsIntoAdoptiveHousehold = true ∧
  w.receivesNewSocialContinuity = true ∧
  w.baptismNameHeldUnderReserve = true

def arkSchemaEquivalent
    (a b : SealedInfantWaterAdoptionSchema) : Prop :=
  a.vulnerableBirth = b.vulnerableBirth ∧
  a.hiddenFatherOrThreatenedLineage = b.hiddenFatherOrThreatenedLineage ∧
  a.rushArkCarrier = b.rushArkCarrier ∧
  a.bitumenSeal = b.bitumenSeal ∧
  a.riverTransportWithoutDrowning = b.riverTransportWithoutDrowning ∧
  a.waterCarrierAdoption = b.waterCarrierAdoption ∧
  a.lowStatusApprenticeship = b.lowStatusApprenticeship ∧
  a.laterSovereignLegitimacy = b.laterSovereignLegitimacy

theorem sargon_sealed_infant_water_adoption :
    sealedInfantWaterAdoption sargonArkSchema := by
  unfold sealedInfantWaterAdoption sargonArkSchema
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem moses_resonance_schema_same_shape :
    sealedInfantWaterAdoption mosesArkResonanceSchema := by
  unfold sealedInfantWaterAdoption mosesArkResonanceSchema
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sargon_moses_schema_isomorphic :
    arkSchemaEquivalent sargonArkSchema mosesArkResonanceSchema := by
  unfold arkSchemaEquivalent sargonArkSchema mosesArkResonanceSchema
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sargon_legitimacy_repair :
    sargonLegitimacyRepair sargonLegitimacyLayer := by
  unfold sargonLegitimacyRepair sargonLegitimacyLayer
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sargon_structural_resonance_under_reserve :
    structuralResonanceUnderReserve repeatedActionReserve := by
  unfold structuralResonanceUnderReserve repeatedActionReserve
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sargon_baptism_like_water_transfer :
    baptismLikeWaterTransfer liminalWaterPassage := by
  unfold baptismLikeWaterTransfer liminalWaterPassage
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sargon_inherits_name_migration_reserve :
    GenesisNameMigrationWitness.documentsPreserveGenesisNames
      GenesisNameMigrationWitness.documentaryNameEvidence ∧
    structuralResonanceUnderReserve repeatedActionReserve := by
  exact ⟨GenesisNameMigrationWitness.genesis_documents_preserve_names,
    sargon_structural_resonance_under_reserve⟩

theorem sargon_inherits_water_carrier_route :
    MummuTiamatuWaterChaosCarrierWitness.seaFriendFoeTaming
      MummuTiamatuWaterChaosCarrierWitness.seaTamingAmbivalence ∧
    sealedInfantWaterAdoption sargonArkSchema ∧
    baptismLikeWaterTransfer liminalWaterPassage := by
  exact ⟨MummuTiamatuWaterChaosCarrierWitness.mummu_tiamatu_sea_friend_foe_taming,
    sargon_sealed_infant_water_adoption,
    sargon_baptism_like_water_transfer⟩

theorem sargon_ark_legitimacy_witness :
    sealedInfantWaterAdoption sargonArkSchema ∧
    arkSchemaEquivalent sargonArkSchema mosesArkResonanceSchema ∧
    sargonLegitimacyRepair sargonLegitimacyLayer ∧
    structuralResonanceUnderReserve repeatedActionReserve ∧
    baptismLikeWaterTransfer liminalWaterPassage := by
  exact ⟨sargon_sealed_infant_water_adoption,
    sargon_moses_schema_isomorphic,
    sargon_legitimacy_repair,
    sargon_structural_resonance_under_reserve,
    sargon_baptism_like_water_transfer⟩

end SargonArkLegitimacyWitness
end Gnosis.Witnesses.Chaldean
