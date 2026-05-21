import Init

namespace Gnosis.Witnesses.Bible.Ephesians
namespace EphesiansArmorBoldnessClosingWitness

/-!
# Ephesians 6:10-24 -- Whole Armor, Bold Mystery Speech, and Closing Peace

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94315-94362`.

The final conflict is not flesh and blood. Armor names truth, righteousness,
peace, faith, salvation, Spirit-word, prayer, perseverance, and bold speech in
bonds; the close sends comfort and peace-love-faith-grace.

No `sorry`, no new `axiom`.
-/

structure ArmorStand where
  strongInLordPower : Bool := true
  wholeArmorPutOn : Bool := true
  standAgainstWiles : Bool := true
  notFleshBloodWrestling : Bool := true
  highPowersDarknessNamed : Bool := true
  withstandEvilDay : Bool := true
  truthRighteousnessPeace : Bool := true
  faithShieldQuenchesDarts : Bool := true
  salvationHelmetSpiritSwordWord : Bool := true
deriving DecidableEq, Repr

def armorStand : ArmorStand := {}

def armorStandWitness (a : ArmorStand) : Prop :=
  a.strongInLordPower = true ∧ a.wholeArmorPutOn = true ∧
  a.standAgainstWiles = true ∧ a.notFleshBloodWrestling = true ∧
  a.highPowersDarknessNamed = true ∧ a.withstandEvilDay = true ∧
  a.truthRighteousnessPeace = true ∧ a.faithShieldQuenchesDarts = true ∧
  a.salvationHelmetSpiritSwordWord = true

structure BoldnessClosing where
  prayerSupplicationSpirit : Bool := true
  watchPerseveranceAllSaints : Bool := true
  utteranceForBoldMystery : Bool := true
  ambassadorInBonds : Bool := true
  tychicusComfortsHearts : Bool := true
  peaceLoveFaithClosing : Bool := true
  graceWithSincereLove : Bool := true
deriving DecidableEq, Repr

def boldnessClosing : BoldnessClosing := {}

def boldnessClosingWitness (b : BoldnessClosing) : Prop :=
  b.prayerSupplicationSpirit = true ∧ b.watchPerseveranceAllSaints = true ∧
  b.utteranceForBoldMystery = true ∧ b.ambassadorInBonds = true ∧
  b.tychicusComfortsHearts = true ∧ b.peaceLoveFaithClosing = true ∧
  b.graceWithSincereLove = true

theorem ephesians_armor_stand :
    armorStandWitness armorStand := by
  unfold armorStandWitness armorStand
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_boldness_closing :
    boldnessClosingWitness boldnessClosing := by
  unfold boldnessClosingWitness boldnessClosing
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_armor_boldness_closing_witness :
    armorStandWitness armorStand ∧ boldnessClosingWitness boldnessClosing := by
  exact ⟨ephesians_armor_stand, ephesians_boldness_closing⟩

end EphesiansArmorBoldnessClosingWitness
end Gnosis.Witnesses.Bible.Ephesians
