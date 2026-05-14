import Init

namespace Gnosis
namespace CombinatorialBruteForce

/-!
# Combinatorial Brute Force

Finite Init-compatible search-space and pruning inequalities.  The old module
composed many unavailable theorem families; this restoration keeps the useful
kernel: candidate counts, deterministic pruning, bounded survivors, and work
savings.
-/

structure SearchSpace where
  candidates : Nat
  lowerBound : Nat
  lowerBoundFits : lowerBound ≤ candidates

namespace SearchSpace

def bruteForceWork (space : SearchSpace) : Nat :=
  space.candidates

def unresolved (space : SearchSpace) (examined : Nat) : Nat :=
  space.candidates - examined

theorem unresolved_le_candidates
    (space : SearchSpace)
    (examined : Nat) :
    space.unresolved examined ≤ space.candidates := by
  unfold unresolved
  exact Nat.sub_le _ _

theorem unresolved_zero_after_full_scan
    (space : SearchSpace)
    (hFull : space.candidates ≤ examined) :
    space.unresolved examined = 0 := by
  unfold unresolved
  exact Nat.sub_eq_zero_of_le hFull

theorem lower_bound_within_bruteforce
    (space : SearchSpace) :
    space.lowerBound ≤ space.bruteForceWork := by
  exact space.lowerBoundFits

end SearchSpace

structure PruningCertificate where
  space : SearchSpace
  pruned : Nat
  prunedFits : pruned ≤ space.candidates
  survivorFloor : Nat
  floorFits : survivorFloor ≤ space.candidates - pruned

namespace PruningCertificate

def survivors (certificate : PruningCertificate) : Nat :=
  certificate.space.candidates - certificate.pruned

def workSaved (certificate : PruningCertificate) : Nat :=
  certificate.pruned

theorem survivors_le_candidates
    (certificate : PruningCertificate) :
    certificate.survivors ≤ certificate.space.candidates := by
  unfold survivors
  exact Nat.sub_le _ _

theorem survivor_floor_holds
    (certificate : PruningCertificate) :
    certificate.survivorFloor ≤ certificate.survivors := by
  exact certificate.floorFits

theorem pruned_plus_survivors
    (certificate : PruningCertificate) :
    certificate.survivors + certificate.pruned =
      certificate.space.candidates := by
  unfold survivors
  exact Nat.sub_add_cancel certificate.prunedFits

theorem pruning_never_increases_work
    (certificate : PruningCertificate) :
    certificate.survivors ≤ certificate.space.bruteForceWork := by
  exact certificate.survivors_le_candidates

theorem positive_pruning_saves_work
    (certificate : PruningCertificate)
    (hPruned : 0 < certificate.pruned) :
    certificate.survivors < certificate.space.bruteForceWork := by
  unfold SearchSpace.bruteForceWork survivors
  exact Nat.sub_lt (Nat.lt_of_lt_of_le hPruned certificate.prunedFits) hPruned

theorem zero_pruning_matches_bruteforce
    (certificate : PruningCertificate)
    (hZero : certificate.pruned = 0) :
    certificate.survivors = certificate.space.bruteForceWork := by
  unfold survivors SearchSpace.bruteForceWork
  rw [hZero]
  exact Nat.sub_zero certificate.space.candidates

end PruningCertificate

structure RaceFoldSearch where
  candidateCount : Nat
  winnerCount : Nat
  winnerBound : winnerCount ≤ candidateCount
  nonemptyWinners : 0 < winnerCount

namespace RaceFoldSearch

def vented (race : RaceFoldSearch) : Nat :=
  race.candidateCount - race.winnerCount

theorem winners_survive_candidates
    (race : RaceFoldSearch) :
    race.winnerCount ≤ race.candidateCount := race.winnerBound

theorem vented_plus_winners
    (race : RaceFoldSearch) :
    race.vented + race.winnerCount = race.candidateCount := by
  unfold vented
  exact Nat.sub_add_cancel race.winnerBound

theorem single_winner_vents_all_but_one
    (race : RaceFoldSearch)
    (hOne : race.winnerCount = 1) :
    race.vented = race.candidateCount - 1 := by
  unfold vented
  rw [hOne]

end RaceFoldSearch

def sampleSearchSpace : SearchSpace where
  candidates := 64
  lowerBound := 8
  lowerBoundFits := by decide

def samplePruning : PruningCertificate where
  space := sampleSearchSpace
  pruned := 40
  prunedFits := by decide
  survivorFloor := 8
  floorFits := by decide

def sampleRaceFold : RaceFoldSearch where
  candidateCount := 64
  winnerCount := 8
  winnerBound := by decide
  nonemptyWinners := by decide

theorem sample_pruning_survivors :
    samplePruning.survivors = 24 := by
  rfl

theorem sample_pruning_saves_work :
    samplePruning.survivors < samplePruning.space.bruteForceWork := by
  exact samplePruning.positive_pruning_saves_work (by decide)

theorem sample_race_vents :
    sampleRaceFold.vented = 56 := by
  rfl

theorem combinatorial_bruteforce_restored_master :
    sampleSearchSpace.lowerBound ≤ sampleSearchSpace.bruteForceWork ∧
      samplePruning.survivors = 24 ∧
      samplePruning.survivors < samplePruning.space.bruteForceWork ∧
      sampleRaceFold.vented + sampleRaceFold.winnerCount =
        sampleRaceFold.candidateCount := by
  exact
    ⟨sampleSearchSpace.lower_bound_within_bruteforce,
      sample_pruning_survivors,
      sample_pruning_saves_work,
      sampleRaceFold.vented_plus_winners⟩

end CombinatorialBruteForce
end Gnosis
