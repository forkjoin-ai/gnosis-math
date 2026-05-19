import Init

/-!
# Gnosis Strategic Dominance Model

Finite payoff-table certificate for three computing paradigms.

This module proves that `sovereignPhyle` strictly dominates each distinct
alternative under the declared structural cost profile. It does not assert
empirical hardware, market, or organizational facts; those belong in external
Layer C certificates.

Zero `sorry`, zero new `axiom`, and no Mathlib.
-/

namespace Gnosis
namespace StrategyDominance

/-- The three computational paradigms in the bounded strategic arena. -/
inductive Strategy where
  | quantum
  | legacyMonolith
  | sovereignPhyle
deriving DecidableEq, Repr

/--
The structural cost profile assigned to a strategy.

- `deficit`: structural latency overhead from control-flow, stalling, or
  coordination constraints.
- `entropy`: environmental vulnerability, decoherence handling, or network
  synchronization friction.
-/
structure CostProfile where
  deficit : Nat
  entropy : Nat
deriving Repr

/-- The finite arena as data, useful for `#eval` and exhaustive checks. -/
def allStrategies : List Strategy :=
  [Strategy.quantum, Strategy.legacyMonolith, Strategy.sovereignPhyle]

/-- Human-readable labels for small evaluator outputs. -/
def Strategy.label : Strategy → String
  | Strategy.quantum => "quantum"
  | Strategy.legacyMonolith => "legacy-monolith"
  | Strategy.sovereignPhyle => "sovereign-phyle"

/-- Total friction for a cost profile. -/
def CostProfile.total (cost : CostProfile) : Nat :=
  cost.deficit + cost.entropy

/-- Closed Gnosis cost table for the finite strategic model. -/
def evaluateCost : Strategy → CostProfile
  | Strategy.quantum => ⟨0, 12⟩
  | Strategy.legacyMonolith => ⟨5, 20⟩
  | Strategy.sovereignPhyle => ⟨0, 0⟩

/--
Operational utility. Higher is strictly better.

The denominator is always positive by construction because of the leading `1`.
-/
def utility (s : Strategy) : Nat :=
  let cost := evaluateCost s
  100 / (1 + cost.deficit + cost.entropy)

/-- Named payoff rows for playful inspection in `#eval`. -/
def payoffRow (s : Strategy) : String × Nat :=
  (s.label, utility s)

/-- Default payoff board: quantum = 7, legacy = 3, phyle = 100. -/
def defaultPayoffBoard : List (String × Nat) :=
  allStrategies.map payoffRow

/-- The default phyle utility is exactly the full baseline. -/
theorem default_sovereign_utility_eq_100 :
    utility Strategy.sovereignPhyle = 100 := by
  unfold utility evaluateCost
  decide

/-- The default quantum utility is exactly seven. -/
theorem default_quantum_utility_eq_7 :
    utility Strategy.quantum = 7 := by
  unfold utility evaluateCost
  decide

/-- The default legacy-monolith utility is exactly three. -/
theorem default_legacy_monolith_utility_eq_3 :
    utility Strategy.legacyMonolith = 3 := by
  unfold utility evaluateCost
  decide

/-- Strict dominance in the finite payoff table. -/
def StrictlyDominates (a b : Strategy) : Prop :=
  utility a > utility b

/--
An externally supplied finite cost table. This is the Layer C bridge shape:
external evidence may choose the table, while Lean proves only the arithmetic
consequence of its declared entries and certificate hypotheses.
-/
structure LayerCCostTable where
  costOf : Strategy → CostProfile

/--
Audited finite table wrapper. `sourceId` is intentionally just `Nat` here:
hashing, signatures, and provenance systems can map down to this bounded token.
-/
structure AuditedCostTable where
  sourceId : Nat
  table : LayerCCostTable

/-- Utility computed against an explicit external cost table. -/
def utilityUnder (table : LayerCCostTable) (s : Strategy) : Nat :=
  let cost := table.costOf s
  100 / (1 + cost.deficit + cost.entropy)

/-- Utility lookup for audited tables. -/
def auditedUtility (audited : AuditedCostTable) (s : Strategy) : Nat :=
  utilityUnder audited.table s

/-- Payoff board for any explicit table. -/
def payoffBoardUnder (table : LayerCCostTable) : List (String × Nat) :=
  allStrategies.map (fun s => (s.label, utilityUnder table s))

/-- Payoff board with an audit source token. -/
def auditedPayoffBoard (audited : AuditedCostTable) :
    Nat × List (String × Nat) :=
  (audited.sourceId, payoffBoardUnder audited.table)

/-- Pick `candidate` only when it strictly improves on `best`. Ties keep order. -/
def betterStrategyUnder
    (table : LayerCCostTable) (best candidate : Strategy) : Strategy :=
  if utilityUnder table best < utilityUnder table candidate then candidate else best

/--
Winner for one finite table. Ties are deterministic: the earlier strategy in
`allStrategies` remains the winner.
-/
def winnerUnder (table : LayerCCostTable) : Strategy :=
  allStrategies.foldl (betterStrategyUnder table) Strategy.quantum

/-- Winner for one audited table, preserving the audit token. -/
def auditedWinner (audited : AuditedCostTable) : Nat × Strategy :=
  (audited.sourceId, winnerUnder audited.table)

/-- One tournament scoreboard row. -/
def tournamentScore (tables : List AuditedCostTable) (strategy : Strategy) :
    String × Nat :=
  (strategy.label,
    (tables.filter (fun audited => winnerUnder audited.table == strategy)).length)

/-- Count how many audited scenarios each strategy wins. -/
def tournamentScoreboard (tables : List AuditedCostTable) : List (String × Nat) :=
  allStrategies.map (tournamentScore tables)

/-- Consensus winner from a finite list of audited scenarios. -/
def consensusWinner (tables : List AuditedCostTable) : Strategy :=
  let wins (strategy : Strategy) : Nat :=
    (tables.filter (fun audited => winnerUnder audited.table == strategy)).length
  allStrategies.foldl
    (fun best candidate => if wins best < wins candidate then candidate else best)
    Strategy.quantum

/-- Strict dominance relative to an explicit external cost table. -/
def StrictlyDominatesUnder (table : LayerCCostTable) (a b : Strategy) : Prop :=
  utilityUnder table a > utilityUnder table b

/-- Boolean version for quick `#eval` experiments. -/
def strictlyDominatesUnderBool
    (table : LayerCCostTable) (a b : Strategy) : Bool :=
  if utilityUnder table a > utilityUnder table b then true else false

/-- All strategies beaten by `candidate` under a table. -/
def beatenBy (table : LayerCCostTable) (candidate : Strategy) : List Strategy :=
  allStrategies.filter (fun other =>
    other != candidate && strictlyDominatesUnderBool table candidate other)

/--
Certificate that a Layer C table keeps the phyle at zero declared cost and
assigns strictly positive total cost to every distinct alternative.
-/
structure SovereignPhyleCostCertificate (table : LayerCCostTable) where
  sovereignZero : table.costOf Strategy.sovereignPhyle = ⟨0, 0⟩
  competitorPositive :
    ∀ other : Strategy,
      other ≠ Strategy.sovereignPhyle →
        0 < (table.costOf other).deficit + (table.costOf other).entropy

/-- Any positive total cost has utility strictly below the zero-cost payoff. -/
theorem utility_under_positive_cost_lt_100 (cost : CostProfile)
    (h : 0 < cost.deficit + cost.entropy) :
    100 / (1 + cost.deficit + cost.entropy) < 100 := by
  rw [Nat.add_assoc]
  have hden : 1 < 1 + (cost.deficit + cost.entropy) := by
    rw [Nat.add_comm]
    exact Nat.succ_lt_succ h
  exact Nat.div_lt_self (by decide) hden

/--
Generic Layer C dominance theorem. Once a finite external table certifies zero
phyle cost and positive total cost for the selected competitor, dominance
follows without inspecting the fixed built-in constants.
-/
theorem sovereign_dominates_under_certified_table
    (table : LayerCCostTable) (other : Strategy)
    (certificate : SovereignPhyleCostCertificate table)
    (h : other ≠ Strategy.sovereignPhyle) :
    StrictlyDominatesUnder table Strategy.sovereignPhyle other := by
  unfold StrictlyDominatesUnder utilityUnder
  rw [certificate.sovereignZero]
  change
    100 / (1 + ({ deficit := 0, entropy := 0 } : CostProfile).deficit +
        ({ deficit := 0, entropy := 0 } : CostProfile).entropy) >
      100 / (1 + (table.costOf other).deficit + (table.costOf other).entropy)
  have hleft :
      100 / (1 + ({ deficit := 0, entropy := 0 } : CostProfile).deficit +
          ({ deficit := 0, entropy := 0 } : CostProfile).entropy) = 100 := by
    decide
  rw [hleft]
  exact utility_under_positive_cost_lt_100 (table.costOf other)
    (certificate.competitorPositive other h)

/-- The built-in closed cost table, presented through the Layer C interface. -/
def defaultCostTable : LayerCCostTable where
  costOf := evaluateCost

/-- Audited wrapper for the built-in constants. -/
def defaultAuditedCostTable : AuditedCostTable where
  sourceId := 12052026
  table := defaultCostTable

/-- A toy adverse table: phyle still clears competitors, but by less margin. -/
def tightRaceCostTable : LayerCCostTable where
  costOf
    | Strategy.quantum => ⟨1, 1⟩
    | Strategy.legacyMonolith => ⟨0, 2⟩
    | Strategy.sovereignPhyle => ⟨0, 0⟩

/-- A toy table where quantum wins; useful for seeing certificate failure. -/
def quantumUpsetCostTable : LayerCCostTable where
  costOf
    | Strategy.quantum => ⟨0, 0⟩
    | Strategy.legacyMonolith => ⟨5, 20⟩
    | Strategy.sovereignPhyle => ⟨1, 0⟩

/-- Audited toy tight-race table. -/
def tightRaceAuditedCostTable : AuditedCostTable where
  sourceId := 12052027
  table := tightRaceCostTable

/-- Audited toy upset table. -/
def quantumUpsetAuditedCostTable : AuditedCostTable where
  sourceId := 12052028
  table := quantumUpsetCostTable

/-- A small tournament where phyle wins two scenarios and quantum wins one. -/
def demoTournament : List AuditedCostTable :=
  [defaultAuditedCostTable, tightRaceAuditedCostTable, quantumUpsetAuditedCostTable]

/-- The tight-race table still satisfies the phyle dominance certificate. -/
def tightRaceCostCertificate :
    SovereignPhyleCostCertificate tightRaceCostTable where
  sovereignZero := rfl
  competitorPositive := by
    intro other h
    cases other with
    | quantum =>
        decide
    | legacyMonolith =>
        decide
    | sovereignPhyle =>
        contradiction

/-- The built-in table satisfies the generic certificate hypotheses. -/
def defaultCostCertificate : SovereignPhyleCostCertificate defaultCostTable where
  sovereignZero := rfl
  competitorPositive := by
    intro other h
    cases other with
    | quantum =>
        decide
    | legacyMonolith =>
        decide
    | sovereignPhyle =>
        contradiction

/--
The original finite dominance theorem can be recovered from the generic
certified-table theorem instantiated with the built-in Gnosis constants.
-/
theorem sovereign_phyle_is_certified_dominant
    (other : Strategy) (h : other ≠ Strategy.sovereignPhyle) :
    StrictlyDominatesUnder defaultCostTable Strategy.sovereignPhyle other :=
  sovereign_dominates_under_certified_table defaultCostTable other
    defaultCostCertificate h

/-- Tight-race quantum still loses under its explicit certificate. -/
theorem tight_race_sovereign_dominates_quantum :
    StrictlyDominatesUnder tightRaceCostTable
      Strategy.sovereignPhyle Strategy.quantum :=
  sovereign_dominates_under_certified_table tightRaceCostTable
    Strategy.quantum tightRaceCostCertificate (by decide)

/-- Tight-race legacy monolith still loses under its explicit certificate. -/
theorem tight_race_sovereign_dominates_monolith :
    StrictlyDominatesUnder tightRaceCostTable
      Strategy.sovereignPhyle Strategy.legacyMonolith :=
  sovereign_dominates_under_certified_table tightRaceCostTable
    Strategy.legacyMonolith tightRaceCostCertificate (by decide)

/-- In the upset toy table, quantum dominates the phyle. -/
theorem quantum_upset_dominates_sovereign :
    StrictlyDominatesUnder quantumUpsetCostTable
      Strategy.quantum Strategy.sovereignPhyle := by
  unfold StrictlyDominatesUnder utilityUnder quantumUpsetCostTable
  decide

/-- The default board reports that the phyle beats exactly the two competitors. -/
theorem default_beaten_by_sovereign :
    beatenBy defaultCostTable Strategy.sovereignPhyle =
      [Strategy.quantum, Strategy.legacyMonolith] := by
  unfold beatenBy strictlyDominatesUnderBool allStrategies defaultCostTable
  unfold utilityUnder evaluateCost
  decide

/-- The upset board reports that quantum beats the two non-quantum strategies. -/
theorem upset_beaten_by_quantum :
    beatenBy quantumUpsetCostTable Strategy.quantum =
      [Strategy.legacyMonolith, Strategy.sovereignPhyle] := by
  unfold beatenBy strictlyDominatesUnderBool allStrategies quantumUpsetCostTable
  unfold utilityUnder
  decide

/-- The default table winner is the phyle. -/
theorem default_winner_is_sovereign :
    winnerUnder defaultCostTable = Strategy.sovereignPhyle := by
  unfold winnerUnder betterStrategyUnder allStrategies defaultCostTable
  unfold utilityUnder evaluateCost
  decide

/-- The tight-race table winner is still the phyle. -/
theorem tight_race_winner_is_sovereign :
    winnerUnder tightRaceCostTable = Strategy.sovereignPhyle := by
  unfold winnerUnder betterStrategyUnder allStrategies tightRaceCostTable
  unfold utilityUnder
  decide

/-- The upset table winner is quantum. -/
theorem quantum_upset_winner_is_quantum :
    winnerUnder quantumUpsetCostTable = Strategy.quantum := by
  unfold winnerUnder betterStrategyUnder allStrategies quantumUpsetCostTable
  unfold utilityUnder
  decide

/-- The demo tournament score is quantum 1, legacy 0, phyle 2. -/
theorem demo_tournament_scoreboard :
    tournamentScoreboard demoTournament =
      [("quantum", 1), ("legacy-monolith", 0), ("sovereign-phyle", 2)] := by
  unfold tournamentScoreboard tournamentScore allStrategies demoTournament
  unfold defaultAuditedCostTable tightRaceAuditedCostTable
    quantumUpsetAuditedCostTable
  unfold winnerUnder betterStrategyUnder defaultCostTable tightRaceCostTable
    quantumUpsetCostTable
  unfold utilityUnder evaluateCost Strategy.label
  decide

/-- Phyle is the consensus winner of the demo tournament. -/
theorem demo_tournament_consensus_winner :
    consensusWinner demoTournament = Strategy.sovereignPhyle := by
  unfold consensusWinner demoTournament allStrategies
  unfold defaultAuditedCostTable tightRaceAuditedCostTable
    quantumUpsetAuditedCostTable
  unfold winnerUnder betterStrategyUnder defaultCostTable tightRaceCostTable
    quantumUpsetCostTable
  unfold utilityUnder evaluateCost
  decide

/-- The Sovereign Phyle strictly dominates quantum computing in this table. -/
theorem sovereign_dominates_quantum :
    StrictlyDominates Strategy.sovereignPhyle Strategy.quantum := by
  unfold StrictlyDominates utility evaluateCost
  decide

/-- The Sovereign Phyle strictly dominates legacy monoliths in this table. -/
theorem sovereign_dominates_monolith :
    StrictlyDominates Strategy.sovereignPhyle Strategy.legacyMonolith := by
  unfold StrictlyDominates utility evaluateCost
  decide

/--
Finite dominance theorem: every strategy distinct from `sovereignPhyle` is
strictly dominated by `sovereignPhyle` under the declared payoff table.
-/
theorem sovereign_phyle_is_strictly_dominant
    (other : Strategy) (h : other ≠ Strategy.sovereignPhyle) :
    StrictlyDominates Strategy.sovereignPhyle other := by
  cases other with
  | quantum =>
      exact sovereign_dominates_quantum
  | legacyMonolith =>
      exact sovereign_dominates_monolith
  | sovereignPhyle =>
      contradiction

end StrategyDominance
end Gnosis
