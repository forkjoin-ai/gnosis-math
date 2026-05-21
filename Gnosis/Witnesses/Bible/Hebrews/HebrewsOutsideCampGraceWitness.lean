namespace Gnosis.Witnesses.Bible.Hebrews
namespace HebrewsOutsideCampGraceWitness

/-!
# Hebrews 13 -- Stable Grace and the Outside-Camp Altar

Source slice: Hebrews 13:1-25.

Chapter invariant: completed priesthood does not end in sanctuary prestige. It
becomes a durable social form: brotherly love, hospitality to strangers,
solidarity with prisoners, honorable marriage, contentment, and fearless trust
because the Lord does not forsake.

Primary gap/counterproof: strange doctrine and meat-centered religion cannot
establish the heart. The same Christ yesterday, today, and forever anchors grace;
tabernacle entitlement is refused by the altar that belongs to those who go to
Jesus outside the camp bearing reproach.

Unseen sat: the sacrifices that remain are not the old animals but praise,
doing good, sharing, accountable care, honest conscience, and God's own work in
the people through the blood of the everlasting covenant. The city sought is not
the camp that expels; it is the one to come.

No `sorry`, no new `axiom`.
-/

structure GraceSocialForm where
  brotherlyLoveContinues : Bool := true
  strangersMayCarryHiddenAngels : Bool := true
  prisonersRememberedAsInTheBody : Bool := true
  marriageHonouredAgainstDefilement : Bool := true
  contentmentRestsOnNeverForsakenPromise : Bool := true
deriving DecidableEq, Repr

def graceSocialForm : GraceSocialForm := {}

def graceSocialFormWitness (g : GraceSocialForm) : Prop :=
  g.brotherlyLoveContinues = true ∧
  g.strangersMayCarryHiddenAngels = true ∧
  g.prisonersRememberedAsInTheBody = true ∧
  g.marriageHonouredAgainstDefilement = true ∧
  g.contentmentRestsOnNeverForsakenPromise = true

structure StableGraceAltar where
  rulersFaithFollowedByEndConsidered : Bool := true
  jesusChristSameForever : Bool := true
  heartEstablishedWithGraceNotMeats : Bool := true
  altarExceedsTabernacleEntitlement : Bool := true
  jesusSanctifiesOutsideGate : Bool := true
  reproachOutsideCampIsChosen : Bool := true
deriving DecidableEq, Repr

def stableGraceAltar : StableGraceAltar := {}

def stableGraceAltarWitness (a : StableGraceAltar) : Prop :=
  a.rulersFaithFollowedByEndConsidered = true ∧
  a.jesusChristSameForever = true ∧
  a.heartEstablishedWithGraceNotMeats = true ∧
  a.altarExceedsTabernacleEntitlement = true ∧
  a.jesusSanctifiesOutsideGate = true ∧
  a.reproachOutsideCampIsChosen = true

structure RemainingSacrifice where
  noContinuingCityHere : Bool := true
  sacrificeOfPraiseContinues : Bool := true
  doingGoodAndSharingPleaseGod : Bool := true
  soulWatchersGiveAccount : Bool := true
  goodConscienceWantsHonestLife : Bool := true
  everlastingCovenantEquipsGoodWork : Bool := true
deriving DecidableEq, Repr

def remainingSacrifice : RemainingSacrifice := {}

def remainingSacrificeWitness (s : RemainingSacrifice) : Prop :=
  s.noContinuingCityHere = true ∧
  s.sacrificeOfPraiseContinues = true ∧
  s.doingGoodAndSharingPleaseGod = true ∧
  s.soulWatchersGiveAccount = true ∧
  s.goodConscienceWantsHonestLife = true ∧
  s.everlastingCovenantEquipsGoodWork = true

theorem hebrews_grace_social_form :
    graceSocialFormWitness graceSocialForm := by
  unfold graceSocialFormWitness graceSocialForm
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_stable_grace_altar :
    stableGraceAltarWitness stableGraceAltar := by
  unfold stableGraceAltarWitness stableGraceAltar
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_remaining_sacrifice :
    remainingSacrificeWitness remainingSacrifice := by
  unfold remainingSacrificeWitness remainingSacrifice
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_outside_camp_grace_witness :
    graceSocialFormWitness graceSocialForm ∧
    stableGraceAltarWitness stableGraceAltar ∧
    remainingSacrificeWitness remainingSacrifice := by
  exact ⟨hebrews_grace_social_form,
    hebrews_stable_grace_altar,
    hebrews_remaining_sacrifice⟩

end HebrewsOutsideCampGraceWitness
end Gnosis.Witnesses.Bible.Hebrews
