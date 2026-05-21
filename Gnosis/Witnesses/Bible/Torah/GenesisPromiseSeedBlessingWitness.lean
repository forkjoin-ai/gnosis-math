import Init

namespace Gnosis.Witnesses.Bible.Torah
namespace GenesisPromiseSeedBlessingWitness

/-!
# Genesis 15, 22, 26 -- Seed Promise and Nations Blessing

Source text:
- `docs/ebooks/source-texts/bible-kjv.txt:1185-1198`
- `docs/ebooks/source-texts/bible-kjv.txt:1760-1789`
- `docs/ebooks/source-texts/bible-kjv.txt:2190-2198`

This Torah witness owns the promise-source material that Galatians later
projects into its faith argument: seed, covenant, multiplied descendants, and
all-nations blessing.

No `sorry`, no new `axiom`.
-/

structure GenesisSeedPromise where
  covenantWithAbramMade : Bool := true
  seedGivenLandPromise : Bool := true
  nationsBoundaryListed : Bool := true
  seedMultipliedAsStars : Bool := true
  seedPossessesGate : Bool := true
deriving DecidableEq, Repr

def genesisSeedPromise : GenesisSeedPromise := {}

def seedPromiseAnchor (p : GenesisSeedPromise) : Prop :=
  p.covenantWithAbramMade = true ∧
  p.seedGivenLandPromise = true ∧
  p.nationsBoundaryListed = true ∧
  p.seedMultipliedAsStars = true ∧
  p.seedPossessesGate = true

structure GenesisNationsBlessing where
  allNationsBlessedInSeed : Bool := true
  abrahamObeyedVoice : Bool := true
  oathTransferredThroughIsaac : Bool := true
  allCountriesGivenToSeed : Bool := true
  commandmentsStatutesLawsKept : Bool := true
deriving DecidableEq, Repr

def genesisNationsBlessing : GenesisNationsBlessing := {}

def nationsBlessingAnchor (n : GenesisNationsBlessing) : Prop :=
  n.allNationsBlessedInSeed = true ∧
  n.abrahamObeyedVoice = true ∧
  n.oathTransferredThroughIsaac = true ∧
  n.allCountriesGivenToSeed = true ∧
  n.commandmentsStatutesLawsKept = true

theorem genesis_seed_promise_anchor :
    seedPromiseAnchor genesisSeedPromise := by
  unfold seedPromiseAnchor genesisSeedPromise
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem genesis_nations_blessing_anchor :
    nationsBlessingAnchor genesisNationsBlessing := by
  unfold nationsBlessingAnchor genesisNationsBlessing
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem genesis_promise_seed_blessing_witness :
    seedPromiseAnchor genesisSeedPromise ∧
    nationsBlessingAnchor genesisNationsBlessing := by
  exact ⟨genesis_seed_promise_anchor,
    genesis_nations_blessing_anchor⟩

end GenesisPromiseSeedBlessingWitness
end Gnosis.Witnesses.Bible.Torah
