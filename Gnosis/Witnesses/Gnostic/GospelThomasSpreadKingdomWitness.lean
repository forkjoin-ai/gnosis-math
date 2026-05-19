import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Gnostic
namespace GospelThomasSpreadKingdomWitness

/-!
# Gospel of Thomas -- Spread-Out Kingdom and Final Integration

Source text: `docs/ebooks/source-texts/gospel-of-thomas.txt`;
text anchor `docs/ebooks/source-texts/gospel-of-thomas.txt:351-414`.

Sat/unseen reading:

The closing Thomas cluster rejects deferred spectacle. The kingdom will not come
by waiting or by pointing "here" or "there"; it is already spread out upon the
earth and unseen. The final hard saying about Mary is not biological hierarchy
but integration into living spirit in the text's own two-made-one grammar.

Gap / counterproof:

Jar-handle leakage, business excuses, sleeping dog gatekeeping, Caesar-token
misallocation, and waiting-for-the-kingdom all model attention lost to the wrong
ledger.

No `sorry`, no new `axiom`.
-/

structure HiddenLeakage where
  leavenConcealedWorks : Bool
  jarEmptiesUnnoticed : Bool
  treasureUnknownInField : Bool
  brigandEntryPreparedFor : Bool
  dogBlocksManger : Bool
deriving DecidableEq, Repr

def thomasHiddenLeakage : HiddenLeakage where
  leavenConcealedWorks := true
  jarEmptiesUnnoticed := true
  treasureUnknownInField := true
  brigandEntryPreparedFor := true
  dogBlocksManger := true

def hiddenProcessesNeedDiscernment (h : HiddenLeakage) : Prop :=
  h.leavenConcealedWorks = true ∧
  h.jarEmptiesUnnoticed = true ∧
  h.treasureUnknownInField = true ∧
  h.brigandEntryPreparedFor = true ∧
  h.dogBlocksManger = true

structure LedgerSorting where
  caesarToCaesar : Bool
  godToGod : Bool
  mineToMine : Bool
  giveWithoutInterest : Bool
  powerRenounced : Bool
deriving DecidableEq, Repr

def thomasLedgerSorting : LedgerSorting where
  caesarToCaesar := true
  godToGod := true
  mineToMine := true
  giveWithoutInterest := true
  powerRenounced := true

def ledgersMustNotBeConfused (l : LedgerSorting) : Prop :=
  l.caesarToCaesar = true ∧
  l.godToGod = true ∧
  l.mineToMine = true ∧
  l.giveWithoutInterest = true ∧
  l.powerRenounced = true

structure SpreadKingdom where
  notWaiting : Bool
  notHereThere : Bool
  spreadUponEarth : Bool
  unseenByMen : Bool
  twoOneSonsOfMan : Bool
  maryMadeLivingSpirit : Bool
deriving DecidableEq, Repr

def thomasSpreadKingdom : SpreadKingdom where
  notWaiting := true
  notHereThere := true
  spreadUponEarth := true
  unseenByMen := true
  twoOneSonsOfMan := true
  maryMadeLivingSpirit := true

def kingdomAlreadySpreadUnseen (k : SpreadKingdom) : Prop :=
  k.notWaiting = true ∧
  k.notHereThere = true ∧
  k.spreadUponEarth = true ∧
  k.unseenByMen = true ∧
  k.twoOneSonsOfMan = true ∧
  k.maryMadeLivingSpirit = true

theorem thomas_hidden_process_discernment :
    hiddenProcessesNeedDiscernment thomasHiddenLeakage := by
  unfold hiddenProcessesNeedDiscernment thomasHiddenLeakage
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_ledger_sorting :
    ledgersMustNotBeConfused thomasLedgerSorting := by
  unfold ledgersMustNotBeConfused thomasLedgerSorting
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_spread_kingdom :
    kingdomAlreadySpreadUnseen thomasSpreadKingdom := by
  unfold kingdomAlreadySpreadUnseen thomasSpreadKingdom
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_spread_recovery :
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom :=
  Gnosis.GnosisTriptychBraid.two_step_recovery

theorem gospel_thomas_spread_kingdom_witness :
    hiddenProcessesNeedDiscernment thomasHiddenLeakage ∧
    ledgersMustNotBeConfused thomasLedgerSorting ∧
    kingdomAlreadySpreadUnseen thomasSpreadKingdom ∧
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom := by
  exact ⟨thomas_hidden_process_discernment,
    thomas_ledger_sorting,
    thomas_spread_kingdom,
    thomas_spread_recovery⟩

end GospelThomasSpreadKingdomWitness
end Gnosis.Witnesses.Gnostic
