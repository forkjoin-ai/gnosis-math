import Init
import Gnosis.AkerlofLemons
import Gnosis.CoaseTheorem
import Gnosis.SkyrmsBuleyEquilibria

namespace Gnosis
namespace BuleyWalrasGnosisCertificate

open AkerlofLemons CoaseTheorem SkyrmsBuleyEquilibria
open Gnosis (godWeight godWeight_eq_succ_iff_v_zero)

/-!
# Buley–Walras layered certificate (“general equilibrium’’ scaffold)

Composite **witness** aligning three pinned subsystems:

1. **Goods / information** (Akerlof layer): pooled **both** qualities trade (`PeachChannelClear`), or separating **certified** prices clear both qualities (`SeparatingClear`).
2. **Institutions** (Coase layer): bargaining hits optimal `q*` with **zero** transaction wedge (`transactionCost = 0`).
3. **Temporal closure** (Buley layer): `IsBuleyEquilibrium` on **`BuleyState`**.

**Master conclusion (honest).** At shared budget **`R`**, each pillar’s God-weight **`godWeight R vᵢ`**
hits its own **individual ceiling `R + 1`** exactly when that pillar’s vent **`vᵢ` is `0`** in its own bookkeeping (`buleyVent`, Coase **`totalVent`**, Akerlof peach branch at **`v = 0`** when active).

This is **not** a continuum Walras–Arrow–Debreu equilibrium; **not** a uniqueness or existence theorem across all markets forever; **not** literal “perfect society’’.

It **is** a **ledger-level** coincidence certificate: simultaneous **triple ceiling** — what you formalize below as **`TriplePillarCeiling`**.

See also **`tripleVentSumPooling`** / **`fusedPoolingGodWeight`** below: **`fork`** (three parallel pillar vents summed), **`fold`** into one **`Nat`** fed to a single **`godWeight`** — interdependence packaged as **`add = 0 ↔` each storey zero** (**`tripleVentSumPooling_eq_zero_iff`**), not pillar-to-pillar implication without extra morphisms.

Interpretation hygiene: tying “total’’ to **`R + 1`** here means **per-pillar maximal weight at identical `R` once every pillar’s modeled rejection hits zero**.
-/

/-- Pooled-price **market clearing**: both qualities participate under common no-signal bid. -/
def PeachChannelClear (vals : SellerValues) (lemons peaches : Nat) : Prop :=
  ValidTradeNoSignal vals lemons peaches Good.Peach ∧
  ValidTradeNoSignal vals lemons peaches Good.Lemon

/-- Separating/certificate clearing: conditioned prices satisfy both reservations. -/
def SeparatingClear (vals : SellerValues) (ppe lpe : Nat) : Prop :=
  CertifiedSignal vals ppe lpe ∧
  ValidTrade vals ppe Good.Peach ∧ ValidTrade vals lpe Good.Lemon

instance decidablePeachChannelClear (vals : SellerValues) (lemons peaches : Nat) :
    Decidable (PeachChannelClear vals lemons peaches) := by
  unfold PeachChannelClear
  infer_instance

instance decidableSeparatingClear (vals : SellerValues) (ppe lpe : Nat) :
    Decidable (SeparatingClear vals ppe lpe) := by
  unfold SeparatingClear
  infer_instance

/--
Layered equilibrium certificate at shared budget **`R`** (predicates reused by fused vent defs below).

Pooling (`PeachChannelClear`) and separating (`SeparatingClear`) hypotheses are bundled as witnesses.
-/
structure WalrasPoolingWitness (R : Nat) where
  vals : SellerValues
  lemons : Nat
  peaches : Nat
  env : CoaseEnv
  legal : LegalRight
  coop : BargainingUpdate env legal
  time : BuleyState
  hMarket : PeachChannelClear vals lemons peaches
  hCoaseTx : env.transactionCost = 0
  hBuley : IsBuleyEquilibrium time

structure WalrasSeparatingWitness (R : Nat) where
  vals : SellerValues
  ppe : Nat
  lpe : Nat
  env : CoaseEnv
  legal : LegalRight
  coop : BargainingUpdate env legal
  time : BuleyState
  hSep : SeparatingClear vals ppe lpe
  hCoaseTx : env.transactionCost = 0
  hBuley : IsBuleyEquilibrium time

/-- Convenient bundle: simultaneous **triple `R + 1`** (three parallel pillar weights). -/
def TriplePillarCeiling (R : Nat)
    (peachWt : Nat) (instWt : Nat) (clockWt : Nat) : Prop :=
  peachWt = R + 1 ∧ instWt = R + 1 ∧ clockWt = R + 1

/-! ## Fused vent stack (explicit interdependence bookkeeping) -/

/--
**Market pillar vent** (`0/1`): vanishes iff **`PeachChannelClear`** (`dite` sentinel; not a calibrated surplus gap).
-/
def marketVentPooling (vals : SellerValues) (lemons peaches : Nat) : Nat :=
  if _ : PeachChannelClear vals lemons peaches then 0 else 1

/--
Separating-route market vent (**`0/1`**): zero iff **`SeparatingClear`**.
-/
def marketVentSeparating (vals : SellerValues) (ppe lpe : Nat) : Nat :=
  if _ : SeparatingClear vals ppe lpe then 0 else 1

/--
**Fold-sum** over three pillar vents (**pooling bookkeeping**):

`market pooling` + **`CoaseTheorem.totalVent`** + **`SkyrmsBuleyEquilibria.buleyVent`**.
-/
def tripleVentSumPooling (vals : SellerValues) (lemons peaches : Nat)
    {env : CoaseEnv} {legal : LegalRight} (coop : BargainingUpdate env legal)
    (time : BuleyState) : Nat :=
  marketVentPooling vals lemons peaches + totalVent coop + buleyVent time

/-- Separating-route variant of **`tripleVentSumPooling`**. -/
def tripleVentSumSeparating (vals : SellerValues) (ppe lpe : Nat)
    {env : CoaseEnv} {legal : LegalRight} (coop : BargainingUpdate env legal)
    (time : BuleyState) : Nat :=
  marketVentSeparating vals ppe lpe + totalVent coop + buleyVent time

/-- Single fused scalar for one **`godWeight`** read (**Forkjoin-style fold funnel**). -/
def fusedPoolingGodWeight (R : Nat) (vals : SellerValues) (lemons peaches : Nat)
    {env : CoaseEnv} {legal : LegalRight} (coop : BargainingUpdate env legal)
    (time : BuleyState) : Nat :=
  godWeight R (tripleVentSumPooling vals lemons peaches coop time)

def fusedSeparatingGodWeight (R : Nat) (vals : SellerValues) (ppe lpe : Nat)
    {env : CoaseEnv} {legal : LegalRight} (coop : BargainingUpdate env legal)
    (time : BuleyState) : Nat :=
  godWeight R (tripleVentSumSeparating vals ppe lpe coop time)

theorem marketVentPooling_eq_zero_iff (vals : SellerValues) (lemons peaches : Nat) :
    marketVentPooling vals lemons peaches = 0 ↔ PeachChannelClear vals lemons peaches := by
  constructor
  · intro hz
    unfold marketVentPooling at hz
    cases Decidable.em (PeachChannelClear vals lemons peaches) with
    | inl hp =>
      rw [if_pos hp] at hz
      exact hp
    | inr hn =>
      rw [if_neg hn] at hz
      cases hz
  · intro hp
    unfold marketVentPooling
    rw [if_pos hp]

theorem marketVentSeparating_eq_zero_iff (vals : SellerValues) (ppe lpe : Nat) :
    marketVentSeparating vals ppe lpe = 0 ↔ SeparatingClear vals ppe lpe := by
  constructor
  · intro hz
    unfold marketVentSeparating at hz
    cases Decidable.em (SeparatingClear vals ppe lpe) with
    | inl hp =>
      rw [if_pos hp] at hz
      exact hp
    | inr hn =>
      rw [if_neg hn] at hz
      cases hz
  · intro hp
    unfold marketVentSeparating
    rw [if_pos hp]

/-! ### Factorization: summed vent vanishes iff every pillar storey does -/

theorem triple_add_eq_zero {a b c : Nat} : a + b + c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro habc
    have hab_c := Nat.add_eq_zero_iff.mp habc
    have habZero := Nat.add_eq_zero_iff.mp hab_c.1
    exact ⟨habZero.1, habZero.2, hab_c.2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem tripleVentSumPooling_eq_zero_iff (vals : SellerValues) (lemons peaches : Nat)
    {env : CoaseEnv} {legal : LegalRight} (coop : BargainingUpdate env legal)
    (time : BuleyState) :
    tripleVentSumPooling vals lemons peaches coop time = 0 ↔
      PeachChannelClear vals lemons peaches ∧
        totalVent coop = 0 ∧ buleyVent time = 0 := by
  dsimp [tripleVentSumPooling]
  rw [triple_add_eq_zero, marketVentPooling_eq_zero_iff]

theorem tripleVentSumPooling_eq_zero_iff' (vals : SellerValues) (lemons peaches : Nat)
    {env : CoaseEnv} {legal : LegalRight} (coop : BargainingUpdate env legal)
    (time : BuleyState) :
    tripleVentSumPooling vals lemons peaches coop time = 0 ↔
      PeachChannelClear vals lemons peaches ∧
        legalVent env = 0 ∧
          inefficiencyVent env coop.finalQ = 0 ∧
            IsBuleyEquilibrium time := by
  rw [tripleVentSumPooling_eq_zero_iff]
  constructor
  · rintro ⟨hp, hv, bv⟩
    have ⟨hl, hi⟩ := (totalVent_components_iff coop).mp hv
    refine ⟨hp, hl, hi, ?_⟩
    exact (buleyVent_eq_zero_iff time).mp bv
  · rintro ⟨hp, hL, hI, hb⟩
    refine ⟨hp, ?_, ?_⟩
    · exact (totalVent_components_iff coop).mpr ⟨hL, hI⟩
    · exact (buleyVent_eq_zero_iff time).mpr hb

theorem tripleVentSumSeparating_eq_zero_iff (vals : SellerValues) (ppe lpe : Nat)
    {env : CoaseEnv} {legal : LegalRight} (coop : BargainingUpdate env legal)
    (time : BuleyState) :
    tripleVentSumSeparating vals ppe lpe coop time = 0 ↔
      SeparatingClear vals ppe lpe ∧
        totalVent coop = 0 ∧ buleyVent time = 0 := by
  dsimp [tripleVentSumSeparating]
  rw [triple_add_eq_zero, marketVentSeparating_eq_zero_iff]

/-! ### Fused-godWeight ceiling (**fold funnel**) iff triple sum clears -/

theorem fusedPoolingGodWeight_eq_ceiling_iff_tripleVent
    {R : Nat} (hR : 0 < R) (vals : SellerValues) (lemons peaches : Nat)
    {env : CoaseEnv} {legal : LegalRight} (coop : BargainingUpdate env legal)
    (time : BuleyState) :
    fusedPoolingGodWeight R vals lemons peaches coop time = R + 1 ↔
      tripleVentSumPooling vals lemons peaches coop time = 0 :=
  (godWeight_eq_succ_iff_v_zero hR)

theorem fusedSeparatingGodWeight_eq_ceiling_iff_tripleVent
    {R : Nat} (hR : 0 < R) (vals : SellerValues) (ppe lpe : Nat)
    {env : CoaseEnv} {legal : LegalRight} (coop : BargainingUpdate env legal)
    (time : BuleyState) :
    fusedSeparatingGodWeight R vals ppe lpe coop time = R + 1 ↔
      tripleVentSumSeparating vals ppe lpe coop time = 0 :=
  (godWeight_eq_succ_iff_v_zero hR)

theorem peachMarketActive_true_of_peach_valid
    (vals : SellerValues) (lemons peaches : Nat)
    (hp : ValidTradeNoSignal vals lemons peaches Good.Peach) :
    peachMarketActive vals lemons peaches = true := by
  unfold peachMarketActive
  rw [if_pos hp]

/--
Peach-branch weight hits ceiling **iff** pooled participation includes peach —
here packaged from **`PeachChannelClear`** using just the peach conjunct for the **`Bool`** flag.
-/
theorem peachMarketWeight_ceiling_when_channel_clear (R : Nat)
    (vals : SellerValues) (lemons peaches : Nat)
    (hClr : PeachChannelClear vals lemons peaches) :
    peachMarketWeight R (peachMarketActive vals lemons peaches) = R + 1 := by
  have ht := peachMarketActive_true_of_peach_valid vals lemons peaches hClr.1
  rw [ht]
  exact certified_signal_recovers_ceiling R

/-!
Separating path: **`peachMarketWeight R true = R + 1`** is **literal** independently of the witness,
but **`SeparatingClear`** is bundled for narrative alignment (“both qualities trade at tagged prices’’).
-/

theorem peach_market_ceiling_under_separating (R : Nat) :
    peachMarketWeight R true = R + 1 :=
  certified_signal_recovers_ceiling R

/-! ## Witness ⇒ fused stack; fused stack ⇒ triple ceiling layer -/

/-- **`WalrasPoolingWitness`** ⇒ folded vent sum (**interdependent stack**) clears. -/
theorem walrasPoolingWitness_tripleVentSum_eq_zero {R : Nat}
    (w : WalrasPoolingWitness R) :
    tripleVentSumPooling w.vals w.lemons w.peaches w.coop w.time = 0 := by
  exact (tripleVentSumPooling_eq_zero_iff w.vals w.lemons w.peaches w.coop w.time).mpr
    ⟨w.hMarket,
      total_vent_zero_of_zero_tx_and_optimal w.coop w.hCoaseTx,
      buley_equilibrium_has_zero_vent w.time w.hBuley⟩

/-- Separating-route witness ⇒ **`tripleVentSumSeparating`** vanishes. -/
theorem walrasSeparatingWitness_tripleVentSum_eq_zero {R : Nat}
    (w : WalrasSeparatingWitness R) :
    tripleVentSumSeparating w.vals w.ppe w.lpe w.coop w.time = 0 := by
  exact (tripleVentSumSeparating_eq_zero_iff w.vals w.ppe w.lpe w.coop w.time).mpr
    ⟨w.hSep,
      total_vent_zero_of_zero_tx_and_optimal w.coop w.hCoaseTx,
      buley_equilibrium_has_zero_vent w.time w.hBuley⟩

/--
Summed pillar vents at **`0`** (**pooling bookkeeping**) ⇒ the same **`TriplePillarCeiling`** layer
already proved from disaggregated hypotheses.
-/
theorem triple_pillar_ceiling_of_tripleVentSumPooling_eq_zero (R : Nat)
    (vals : SellerValues) (lemons peaches : Nat)
    {env : CoaseEnv} {legal : LegalRight} (coop : BargainingUpdate env legal)
    (time : BuleyState)
    (hz : tripleVentSumPooling vals lemons peaches coop time = 0) :
    TriplePillarCeiling R
      (peachMarketWeight R (peachMarketActive vals lemons peaches))
      (finalWeight R coop)
      (buleyWeight R time) := by
  rcases (tripleVentSumPooling_eq_zero_iff vals lemons peaches coop time).mp hz with
    ⟨hClr, hv, hvB⟩
  have hBx : IsBuleyEquilibrium time := (buleyVent_eq_zero_iff time).mp hvB
  have hTx : env.transactionCost = 0 :=
    (totalVent_zero_imp_legal_and_ineff_zero coop hv).1
  refine ⟨?_, ?_, ?_⟩
  · exact peachMarketWeight_ceiling_when_channel_clear R vals lemons peaches hClr
  · exact final_weight_ceiling_of_zero_tx_and_optimal R coop hTx
  · exact buley_equilibrium_reaches_ceiling R time hBx

theorem triple_pillar_ceiling_of_tripleVentSumSeparating_eq_zero (R : Nat)
    (vals : SellerValues) (ppe lpe : Nat)
    {env : CoaseEnv} {legal : LegalRight} (coop : BargainingUpdate env legal)
    (time : BuleyState)
    (hz : tripleVentSumSeparating vals ppe lpe coop time = 0) :
    TriplePillarCeiling R (peachMarketWeight R true) (finalWeight R coop)
      (buleyWeight R time) := by
  rcases (tripleVentSumSeparating_eq_zero_iff vals ppe lpe coop time).mp hz with
    ⟨_, hv, hvB⟩
  have hBx : IsBuleyEquilibrium time := (buleyVent_eq_zero_iff time).mp hvB
  have hTx : env.transactionCost = 0 :=
    (totalVent_zero_imp_legal_and_ineff_zero coop hv).1
  refine ⟨peach_market_ceiling_under_separating R, ?_, ?_⟩
  · exact final_weight_ceiling_of_zero_tx_and_optimal R coop hTx
  · exact buley_equilibrium_reaches_ceiling R time hBx

/-- Pooling-route master certificate (disaggregated hypotheses). -/
theorem buleyWalras_master_pooling_cleared (R : Nat) (w : WalrasPoolingWitness R) :
    TriplePillarCeiling R
      (peachMarketWeight R (peachMarketActive w.vals w.lemons w.peaches))
      (finalWeight R w.coop)
      (buleyWeight R w.time) := by
  refine ⟨?_, ?_, ?_⟩
  · exact peachMarketWeight_ceiling_when_channel_clear R w.vals w.lemons w.peaches w.hMarket
  · exact final_weight_ceiling_of_zero_tx_and_optimal R w.coop w.hCoaseTx
  · exact buley_equilibrium_reaches_ceiling R w.time w.hBuley

/-- Separating-route master certificate. -/
theorem buleyWalras_master_separating_cleared (R : Nat) (w : WalrasSeparatingWitness R) :
    TriplePillarCeiling R (peachMarketWeight R true) (finalWeight R w.coop)
      (buleyWeight R w.time) := by
  refine ⟨peach_market_ceiling_under_separating R, ?_, ?_⟩
  · exact final_weight_ceiling_of_zero_tx_and_optimal R w.coop w.hCoaseTx
  · exact buley_equilibrium_reaches_ceiling R w.time w.hBuley

end BuleyWalrasGnosisCertificate
end Gnosis
