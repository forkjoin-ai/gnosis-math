import Gnosis.DeficitCapacity
import Gnosis.BuleIsValue
import Gnosis.NoiseLedgerTheorem
import Gnosis.SpectralNoiseEquilibrium

namespace Gnosis

open Gnosis.SpectralNoiseEquilibrium (BuleyUnit buleyUnitScore)

/-!
# The American Frontier

The frontier is the first point where transport capacity matches the path
count. Before that point there is positive deficit; at the frontier the
deficit closes to zero; beyond it there is no positive deficit left to close.

As a noise spectrum, the American frontier is the regime boundary itself:
under-streamed path space is brown-pressure baseline, the exact frontier is
pink contact turbulence, and over-streamed capacity is white integration.
-/

/-- The frontier is the exact stream count needed to match the path count. -/
def frontierStreamCount (pathCount : Nat) : Nat :=
  pathCount

/-- Being at the frontier means using exactly the frontier stream count. -/
def AtFrontier (pathCount streams : Nat) : Prop :=
  streams = frontierStreamCount pathCount

inductive FrontierRegime where
  | pre
  | at
  | post
  deriving DecidableEq, Repr

/-- The frontier's three regimes compile to the existing noise ledger. -/
def frontierNoise (r : FrontierRegime) : Nat :=
  match r with
  | .pre => NoiseLedger.brown_noise
  | .at => NoiseLedger.pink_noise
  | .post => NoiseLedger.white_noise

/-- Regime classifier on the 0/positive/covered frontier deficit shape. -/
def frontierRegime (pathCount streams : Nat) : FrontierRegime :=
  if streams < frontierStreamCount pathCount then .pre
  else if streams = frontierStreamCount pathCount then .at
  else .post

theorem frontier_noise_spectrum :
    frontierNoise FrontierRegime.pre = NoiseLedger.brown_noise ∧
    frontierNoise FrontierRegime.at = NoiseLedger.pink_noise ∧
    frontierNoise FrontierRegime.post = NoiseLedger.white_noise := by
  exact ⟨rfl, rfl, rfl⟩

theorem frontier_noise_is_gnosis_spectrum :
    frontierNoise FrontierRegime.pre = 1 ∧
    frontierNoise FrontierRegime.at = 3 ∧
    frontierNoise FrontierRegime.post = 4 := by
  exact ⟨NoiseLedger.brown_noise_order, NoiseLedger.pink_noise_chaos,
    NoiseLedger.white_noise_gnosis⟩

theorem frontier_noise_progression :
    frontierNoise FrontierRegime.pre < frontierNoise FrontierRegime.at ∧
    frontierNoise FrontierRegime.at < frontierNoise FrontierRegime.post := by
  exact NoiseLedger.noise_spectrum_progression

theorem below_frontier_is_brown_noise {pathCount streams : Nat}
    (hBelow : streams < frontierStreamCount pathCount) :
    frontierNoise (frontierRegime pathCount streams) = NoiseLedger.brown_noise := by
  unfold frontierRegime
  simp [hBelow, frontierNoise]

theorem exact_frontier_is_pink_noise {pathCount streams : Nat}
    (hAt : streams = frontierStreamCount pathCount) :
    frontierNoise (frontierRegime pathCount streams) = NoiseLedger.pink_noise := by
  unfold frontierRegime
  have hNotBelow : ¬ streams < frontierStreamCount pathCount := by
    rw [hAt]
    exact Nat.lt_irrefl _
  simp [hAt, frontierNoise]

theorem beyond_frontier_is_white_noise {pathCount streams : Nat}
    (hBeyond : frontierStreamCount pathCount < streams) :
    frontierNoise (frontierRegime pathCount streams) = NoiseLedger.white_noise := by
  unfold frontierRegime
  have hNotBelow : ¬ streams < frontierStreamCount pathCount :=
    Nat.not_lt_of_ge (Nat.le_of_lt hBeyond)
  have hNotAt : streams ≠ frontierStreamCount pathCount := by
    exact Nat.ne_of_gt hBeyond
  simp [hNotBelow, hNotAt, frontierNoise]

/-! ## Bule-unit face of the frontier -/

/-- The frontier state as a Bule unit: `waste` is unmet path demand,
    `diversity` is transport-side stream diversity, and `opportunity`
    is the remaining pre-frontier headroom. -/
def frontierBule (pathCount streams : Nat) : BuleyUnit :=
  { waste := pathCount - streams
    opportunity := frontierStreamCount pathCount - streams
    diversity := streams }

theorem frontier_bule_waste_eq_deficit_proxy (pathCount streams : Nat) :
    (frontierBule pathCount streams).waste = pathCount - streams := by
  rfl

theorem frontier_bule_diversity_eq_streams (pathCount streams : Nat) :
    (frontierBule pathCount streams).diversity = streams := by
  rfl

theorem frontier_bule_opportunity_eq_headroom (pathCount streams : Nat) :
    (frontierBule pathCount streams).opportunity = frontierStreamCount pathCount - streams := by
  rfl

theorem at_frontier_zero_waste {pathCount streams : Nat}
    (hAt : AtFrontier pathCount streams) :
    (frontierBule pathCount streams).waste = 0 := by
  unfold AtFrontier frontierStreamCount at hAt
  unfold frontierBule
  rw [hAt]
  exact Nat.sub_self pathCount

theorem below_frontier_positive_waste {pathCount streams : Nat}
    (hBelow : streams < frontierStreamCount pathCount) :
    0 < (frontierBule pathCount streams).waste := by
  unfold frontierBule frontierStreamCount at *
  exact Nat.sub_pos_of_lt hBelow

theorem frontier_bule_score_eq_curve (pathCount streams : Nat) :
    buleyUnitScore (frontierBule pathCount streams) =
      (pathCount - streams) + (frontierStreamCount pathCount - streams) + streams := by
  rfl

theorem frontier_bule_optimality_step
    {pathCount streams : Nat}
    (hBelow : streams < frontierStreamCount pathCount) :
    BuleThreeFaceOptimalMove
      (frontierBule pathCount streams)
      (frontierBule pathCount (streams + 1)) := by
  unfold frontierBule frontierStreamCount at *
  constructor
  · exact Nat.sub_succ_lt_self pathCount streams hBelow
  · exact Nat.sub_succ_lt_self pathCount streams hBelow
  · exact Nat.lt_succ_self streams

/-- Before the frontier, one more stream is a three-face Bule optimality move:
    waste and opportunity contract, and diversity expands. At the frontier,
    waste is already zero. -/
theorem american_frontier_bule_optimality
    {pathCount streams : Nat}
    (hBelow : streams < frontierStreamCount pathCount) :
    BuleThreeFaceOptimalMove
      (frontierBule pathCount streams)
      (frontierBule pathCount (streams + 1)) :=
  frontier_bule_optimality_step hBelow

/-- The frontier closes the topological deficit exactly. -/
theorem frontier_closes_deficit
    {pathCount : Nat}
    (hPaths : 1 ≤ pathCount) :
    topologicalDeficit pathCount (frontierStreamCount pathCount) = 0 := by
  simpa [frontierStreamCount] using matched_deficit_is_zero hPaths

/-- Any single-stream transport below a nontrivial path count sits before the frontier. -/
theorem single_stream_is_pre_frontier
    {pathCount : Nat}
    (hPaths : 2 ≤ pathCount) :
    ¬ AtFrontier pathCount 1 := by
  unfold AtFrontier frontierStreamCount
  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 2) hPaths)

/-- Before the frontier, a single stream carries a positive deficit. -/
theorem pre_frontier_single_stream_has_positive_deficit
    {pathCount : Nat}
    (hPaths : 2 ≤ pathCount) :
    0 < topologicalDeficit pathCount 1 := by
  exact single_stream_deficit_positive hPaths

/-- Increasing stream count toward the frontier never increases deficit. -/
theorem frontier_progress_monotone
    {pathCount s : Nat}
    (hBase : 1 ≤ s)
    (hProgress : s ≤ frontierStreamCount pathCount) :
    topologicalDeficit pathCount (frontierStreamCount pathCount) ≤
      topologicalDeficit pathCount s := by
  simpa [frontierStreamCount] using deficit_monotone_in_streams hBase hProgress

/-- The frontier has strictly less deficit than a single-stream transport when paths fork. -/
theorem frontier_strictly_improves_on_single_stream
    {pathCount : Nat}
    (hPaths : 2 ≤ pathCount) :
    topologicalDeficit pathCount (frontierStreamCount pathCount) <
      topologicalDeficit pathCount 1 := by
  have hFrontier : topologicalDeficit pathCount (frontierStreamCount pathCount) = 0 := by
    exact frontier_closes_deficit (Nat.le_trans (by decide) hPaths)
  have hSingle : 0 < topologicalDeficit pathCount 1 := by
    exact pre_frontier_single_stream_has_positive_deficit hPaths
  rw [hFrontier]
  exact hSingle

/-- Once the frontier is reached, adding more streams cannot create a positive deficit. -/
theorem post_frontier_has_no_positive_deficit
    {pathCount streams : Nat}
    (hCover : frontierStreamCount pathCount ≤ streams) :
    topologicalDeficit pathCount streams ≤ 0 := by
  simpa [frontierStreamCount] using deficit_nonpositive_when_streams_cover_paths hCover

end Gnosis
