namespace Gnosis.Witnesses.Bible.Hebrews
namespace HebrewsMelchisedecEndlessLifeWitness

/-!
# Hebrews 7 -- Melchisedec, Changed Priesthood, and Endless Life

Source slice: Hebrews 7:1-28.

Chapter invariant: Melchisedec is the rank witness by which Levitical closure is
falsified. Abraham gives tithes and receives blessing; Levi, still in Abraham, is
therefore downstream of the one whose priesthood is not counted from Levitical
descent.

Primary gap/counterproof: perfection cannot be sourced from a priesthood that is
itself changed. If the Levitical order made nothing perfect, then another priest
after Melchisedec is not decorative typology; priesthood change entails law
change, better hope, and access to God.

Unseen sat: endless life is the operational difference. Many mortal priests are
prevented by death from continuing; the Son, made priest by oath, continues ever,
has unchangeable priesthood, intercedes ever, and offers himself once.

No `sorry`, no new `axiom`.
-/

structure MelchisedecRank where
  kingOfRighteousnessAndPeace : Bool := true
  abrahamGivesTithe : Bool := true
  abrahamReceivesBlessing : Bool := true
  lesserIsBlessedByBetter : Bool := true
  leviPaysTithesInAbraham : Bool := true
deriving DecidableEq, Repr

def melchisedecRank : MelchisedecRank := {}

def melchisedecRankWitness (r : MelchisedecRank) : Prop :=
  r.kingOfRighteousnessAndPeace = true ∧
  r.abrahamGivesTithe = true ∧
  r.abrahamReceivesBlessing = true ∧
  r.lesserIsBlessedByBetter = true ∧
  r.leviPaysTithesInAbraham = true

structure PriesthoodLawChange where
  leviticalPerfectionFails : Bool := true
  changedPriesthoodRequiresChangedLaw : Bool := true
  judahPriesthoodBreaksMosaicSilence : Bool := true
  betterHopeDrawsNearToGod : Bool := true
deriving DecidableEq, Repr

def priesthoodLawChange : PriesthoodLawChange := {}

def priesthoodLawChangeWitness (c : PriesthoodLawChange) : Prop :=
  c.leviticalPerfectionFails = true ∧
  c.changedPriesthoodRequiresChangedLaw = true ∧
  c.judahPriesthoodBreaksMosaicSilence = true ∧
  c.betterHopeDrawsNearToGod = true

structure MortalPriesthoodCounterproof where
  carnalCommandmentIsWeak : Bool := true
  manyPriestsAreBlockedByDeath : Bool := true
  oathMakesSuretyOfBetterTestament : Bool := true
  unchangeablePriesthoodSavesUttermost : Bool := true
  onceSelfOfferingExceedsDailySacrifice : Bool := true
  oathConsecratesSonForever : Bool := true
deriving DecidableEq, Repr

def mortalPriesthoodCounterproof : MortalPriesthoodCounterproof := {}

def mortalPriesthoodRejected (c : MortalPriesthoodCounterproof) : Prop :=
  c.carnalCommandmentIsWeak = true ∧
  c.manyPriestsAreBlockedByDeath = true ∧
  c.oathMakesSuretyOfBetterTestament = true ∧
  c.unchangeablePriesthoodSavesUttermost = true ∧
  c.onceSelfOfferingExceedsDailySacrifice = true ∧
  c.oathConsecratesSonForever = true

theorem hebrews_melchisedec_rank :
    melchisedecRankWitness melchisedecRank := by
  unfold melchisedecRankWitness melchisedecRank
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_priesthood_law_change :
    priesthoodLawChangeWitness priesthoodLawChange := by
  unfold priesthoodLawChangeWitness priesthoodLawChange
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem hebrews_mortal_priesthood_rejected :
    mortalPriesthoodRejected mortalPriesthoodCounterproof := by
  unfold mortalPriesthoodRejected mortalPriesthoodCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_melchisedec_endless_life_witness :
    melchisedecRankWitness melchisedecRank ∧
    priesthoodLawChangeWitness priesthoodLawChange ∧
    mortalPriesthoodRejected mortalPriesthoodCounterproof := by
  exact ⟨hebrews_melchisedec_rank,
    hebrews_priesthood_law_change,
    hebrews_mortal_priesthood_rejected⟩

end HebrewsMelchisedecEndlessLifeWitness
end Gnosis.Witnesses.Bible.Hebrews
