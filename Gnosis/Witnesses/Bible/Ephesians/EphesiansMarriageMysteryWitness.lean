import Init

namespace Gnosis.Witnesses.Bible.Ephesians
namespace EphesiansMarriageMysteryWitness

/-!
# Ephesians 5:22-33 -- Marriage, Body Love, and Christ-Church Mystery

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94273-94289`.

The household instruction is explicitly marked as mystery concerning Christ and
the church. The witness therefore records body-love and self-giving sanctification
as the controlling analogy.

No `sorry`, no new `axiom`.
-/

structure MarriageMystery where
  wivesAsUntoLord : Bool := true
  christHeadOfChurchSaviourBody : Bool := true
  husbandsLoveAsChristLovedChurch : Bool := true
  christGaveSelfForChurch : Bool := true
  sanctifyCleanseByWord : Bool := true
  presentGloriousWithoutBlemish : Bool := true
  loveWifeAsOwnBody : Bool := true
  membersOfBodyNamed : Bool := true
  oneFleshQuoted : Bool := true
  greatMysteryChristChurch : Bool := true
deriving DecidableEq, Repr

def marriageMystery : MarriageMystery := {}

def marriageMysteryWitness (m : MarriageMystery) : Prop :=
  m.wivesAsUntoLord = true ∧ m.christHeadOfChurchSaviourBody = true ∧
  m.husbandsLoveAsChristLovedChurch = true ∧ m.christGaveSelfForChurch = true ∧
  m.sanctifyCleanseByWord = true ∧ m.presentGloriousWithoutBlemish = true ∧
  m.loveWifeAsOwnBody = true ∧ m.membersOfBodyNamed = true ∧
  m.oneFleshQuoted = true ∧ m.greatMysteryChristChurch = true

theorem ephesians_marriage_mystery :
    marriageMysteryWitness marriageMystery := by
  unfold marriageMysteryWitness marriageMystery
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EphesiansMarriageMysteryWitness
end Gnosis.Witnesses.Bible.Ephesians
