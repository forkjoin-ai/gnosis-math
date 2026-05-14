import Init

namespace Gnosis

/-!
# Negotiation Equilibrium: BATNA Walking Is Void Walking

Finite Init core for the collapsed negotiation module. The historical file
connected negotiation theory to void walking, semiotic deficit, and heat.
This rebuild keeps the computable Nat spine: multi-dimensional interests are
compressed into a single offer stream, rejected offers accumulate as the BATNA
boundary, and concession weights are the complement of the rejection history.
-/

/-- A negotiation channel compresses each party's position space into one
offer stream. -/
structure NegotiationChannel where
  partyA_dimensions : Nat
  partyB_dimensions : Nat
  partyA_complex : 2 ≤ partyA_dimensions
  partyB_complex : 2 ≤ partyB_dimensions
  sharedContext : Nat

/-- Total finite semantic space present before the offer-stream compression. -/
def NegotiationChannel.totalDimensions (nc : NegotiationChannel) : Nat :=
  nc.partyA_dimensions + nc.partyB_dimensions

/-- Deficit left by compressing all dimensions into one offer stream. -/
def NegotiationChannel.deficit (nc : NegotiationChannel) : Nat :=
  nc.totalDimensions - 1

theorem negotiation_total_dimensions_at_least_four
    (nc : NegotiationChannel) :
    4 ≤ nc.totalDimensions := by
  exact Nat.add_le_add nc.partyA_complex nc.partyB_complex

theorem negotiation_deficit_positive (nc : NegotiationChannel) :
    0 < nc.deficit := by
  unfold NegotiationChannel.deficit
  exact Nat.sub_pos_of_lt
    (Nat.lt_of_lt_of_le (by decide : 1 < 4)
      (negotiation_total_dimensions_at_least_four nc))

theorem negotiation_deficit_value (nc : NegotiationChannel) :
    nc.deficit = nc.totalDimensions - 1 := rfl

theorem negotiation_deficit_bounded (nc : NegotiationChannel) :
    nc.deficit ≤ nc.totalDimensions := by
  unfold NegotiationChannel.deficit
  exact Nat.sub_le nc.totalDimensions 1

/-- One offer fork with a selected accepted or least-bad index. -/
structure NegotiationRound where
  offerCount : Nat
  nontrivial : 2 ≤ offerCount
  acceptedIdx : Fin offerCount

/-- Rejected alternatives form the finite BATNA boundary for a round. -/
def NegotiationRound.batnaBoundary (nr : NegotiationRound) : Nat :=
  nr.offerCount - 1

theorem batna_is_void_boundary (nr : NegotiationRound) :
    1 ≤ nr.batnaBoundary := by
  unfold NegotiationRound.batnaBoundary
  exact Nat.le_sub_of_add_le nr.nontrivial

theorem batna_boundary_positive (nr : NegotiationRound) :
    0 < nr.batnaBoundary :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (batna_is_void_boundary nr)

def batnaBoundarySum : List NegotiationRound → Nat
  | [] => 0
  | round :: rest => round.batnaBoundary + batnaBoundarySum rest

theorem batna_grows_with_round
    (rounds : List NegotiationRound) (step : NegotiationRound) :
    batnaBoundarySum rounds ≤ batnaBoundarySum (step :: rounds) := by
  cases rounds with
  | nil =>
      unfold batnaBoundarySum
      exact Nat.zero_le step.batnaBoundary
  | cons round rest =>
      unfold batnaBoundarySum
      exact Nat.le_add_left (round.batnaBoundary + batnaBoundarySum rest)
        step.batnaBoundary

/-- Rejection history over a finite term set. -/
structure NegotiationState where
  numTerms : Nat
  nontrivial : 2 ≤ numTerms
  rounds : Nat
  positiveRounds : 0 < rounds
  rejectionCounts : Fin numTerms → Nat
  rejectionBounded : ∀ i, rejectionCounts i ≤ rounds

/-- Complement weight: the less a term has been rejected, the larger its
remaining concession weight. The final `+ 1` keeps every term live. -/
def NegotiationState.complementWeight
    (ns : NegotiationState) (i : Fin ns.numTerms) : Nat :=
  ns.rounds - ns.rejectionCounts i + 1

theorem concession_gradient_positive
    (ns : NegotiationState) (i : Fin ns.numTerms) :
    0 < ns.complementWeight i := by
  unfold NegotiationState.complementWeight
  exact Nat.succ_pos (ns.rounds - ns.rejectionCounts i)

theorem concession_gradient_monotone
    (ns : NegotiationState) (i j : Fin ns.numTerms)
    (h : ns.rejectionCounts i ≤ ns.rejectionCounts j) :
    ns.complementWeight j ≤ ns.complementWeight i := by
  unfold NegotiationState.complementWeight
  exact Nat.succ_le_succ (Nat.sub_le_sub_left h ns.rounds)

/-- Two negotiators reading the same finite rejection history. -/
structure NegotiatorPair where
  numTerms : Nat
  nontrivial : 2 ≤ numTerms
  rounds : Nat
  sharedRejections : Fin numTerms → Nat

def NegotiatorPair.walkerAWeights
    (np : NegotiatorPair) (i : Fin np.numTerms) : Nat :=
  np.rounds - np.sharedRejections i + 1

def NegotiatorPair.walkerBWeights
    (np : NegotiatorPair) (i : Fin np.numTerms) : Nat :=
  np.rounds - np.sharedRejections i + 1

theorem negotiation_coherence
    (np : NegotiatorPair) (i : Fin np.numTerms) :
    np.walkerAWeights i = np.walkerBWeights i := rfl

theorem negotiation_full_coherence (np : NegotiatorPair) :
    np.walkerAWeights = np.walkerBWeights := rfl

/-- Finite heat proxy: every rejected alternative contributes one irreversible
counter unit. -/
def negotiationHeat (rounds : List NegotiationRound) : Nat :=
  batnaBoundarySum rounds

theorem negotiation_heat_monotone
    (rounds : List NegotiationRound) (step : NegotiationRound) :
    negotiationHeat rounds ≤ negotiationHeat (step :: rounds) :=
  batna_grows_with_round rounds step

/-- Bundle the restored finite claims for callers that need one witness. -/
theorem negotiation_convergence_core
    (nc : NegotiationChannel)
    (nr : NegotiationRound)
    (ns : NegotiationState)
    (i : Fin ns.numTerms) :
    0 < nc.deficit ∧
    nc.deficit ≤ nc.totalDimensions ∧
    0 < nr.batnaBoundary ∧
    0 < ns.complementWeight i := by
  exact ⟨negotiation_deficit_positive nc,
    negotiation_deficit_bounded nc,
    batna_boundary_positive nr,
    concession_gradient_positive ns i⟩

end Gnosis
