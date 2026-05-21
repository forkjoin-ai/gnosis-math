import Init

namespace Gnosis

/-!
# Cache Hits As Zero-Marginal-Fold Observations

A cache hit reuses a previously folded sliver, so the marginal fold work of
that access is zero. Cold and stale misses pay positive fold work.
-/

def PositiveFoldWork := { work : Nat // 0 < work }

inductive CacheQueryResolution where
  | hit : CacheQueryResolution
  | cold_miss (work : PositiveFoldWork) : CacheQueryResolution
  | stale_miss (work : PositiveFoldWork) : CacheQueryResolution

def marginal_fold_work (query : CacheQueryResolution) : Nat :=
  match query with
  | .hit => 0
  | .cold_miss work => work.val
  | .stale_miss work => work.val

@[simp] theorem marginal_fold_hit :
    marginal_fold_work .hit = 0 := rfl

@[simp] theorem marginal_fold_cold (work : PositiveFoldWork) :
    marginal_fold_work (.cold_miss work) = work.val := rfl

@[simp] theorem marginal_fold_stale (work : PositiveFoldWork) :
    marginal_fold_work (.stale_miss work) = work.val := rfl

theorem marginal_fold_zero_iff_hit (query : CacheQueryResolution) :
    marginal_fold_work query = 0 ↔ query = .hit := by
  constructor
  · intro hZero
    cases query with
    | hit => rfl
    | cold_miss work =>
        rw [marginal_fold_cold] at hZero
        have hPositive : 0 < work.val := work.property
        rw [hZero] at hPositive
        exact False.elim (Nat.lt_irrefl 0 hPositive)
    | stale_miss work =>
        rw [marginal_fold_stale] at hZero
        have hPositive : 0 < work.val := work.property
        rw [hZero] at hPositive
        exact False.elim (Nat.lt_irrefl 0 hPositive)
  · intro hHit
    rw [hHit]
    rfl

theorem marginal_fold_pos_of_not_hit
    (query : CacheQueryResolution)
    (hNotHit : query ≠ .hit) :
    0 < marginal_fold_work query := by
  cases query with
  | hit => exact False.elim (hNotHit rfl)
  | cold_miss work => exact work.property
  | stale_miss work => exact work.property

theorem stale_miss_same_marginal_as_cold (work : PositiveFoldWork) :
    marginal_fold_work (.stale_miss work) =
      marginal_fold_work (.cold_miss work) := rfl

structure CacheLineView where
  occupied : Bool
  keyMatches : Bool
  entryValid : Bool
deriving Repr

def resolveQuery
    (line : CacheLineView)
    (work : PositiveFoldWork) : CacheQueryResolution :=
  match line with
  | ⟨true, true, true⟩ => .hit
  | ⟨true, true, false⟩ => .stale_miss work
  | _ => .cold_miss work

theorem resolve_marginal_zero_iff
    (line : CacheLineView)
    (work : PositiveFoldWork) :
    marginal_fold_work (resolveQuery line work) = 0 ↔
      line.occupied ∧ line.keyMatches ∧ line.entryValid := by
  cases line with
  | mk occupied keyMatches entryValid =>
      cases occupied <;> cases keyMatches <;> cases entryValid
      · simp [resolveQuery, marginal_fold_work]
        intro hZero
        have hPositive : 0 < work.val := work.property
        rw [hZero] at hPositive
        exact False.elim (Nat.lt_irrefl 0 hPositive)
      · simp [resolveQuery, marginal_fold_work]
        intro hZero
        have hPositive : 0 < work.val := work.property
        rw [hZero] at hPositive
        exact False.elim (Nat.lt_irrefl 0 hPositive)
      · simp [resolveQuery, marginal_fold_work]
        intro hZero
        have hPositive : 0 < work.val := work.property
        rw [hZero] at hPositive
        exact False.elim (Nat.lt_irrefl 0 hPositive)
      · simp [resolveQuery, marginal_fold_work]
        intro hZero
        have hPositive : 0 < work.val := work.property
        rw [hZero] at hPositive
        exact False.elim (Nat.lt_irrefl 0 hPositive)
      · simp [resolveQuery, marginal_fold_work]
        intro hZero
        have hPositive : 0 < work.val := work.property
        rw [hZero] at hPositive
        exact False.elim (Nat.lt_irrefl 0 hPositive)
      · simp [resolveQuery, marginal_fold_work]
        intro hZero
        have hPositive : 0 < work.val := work.property
        rw [hZero] at hPositive
        exact False.elim (Nat.lt_irrefl 0 hPositive)
      · simp [resolveQuery, marginal_fold_work]
        intro hZero
        have hPositive : 0 < work.val := work.property
        rw [hZero] at hPositive
        exact False.elim (Nat.lt_irrefl 0 hPositive)
      · simp [resolveQuery, marginal_fold_work]

structure CacheFillPulse where
  forkEnergy : Nat
  foldWork : Nat
  ventHeat : Nat
  conservation : forkEnergy = foldWork + ventHeat
  sliver : 1 ≤ ventHeat

theorem cache_fill_strict_loss (pulse : CacheFillPulse) :
    pulse.foldWork < pulse.forkEnergy := by
  cases hVent : pulse.ventHeat with
  | zero =>
      have hSliver := pulse.sliver
      rw [hVent] at hSliver
      exact False.elim ((Nat.not_succ_le_zero 0) hSliver)
  | succ heat =>
      rw [pulse.conservation, hVent]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos heat)

def totalMarginalFoldWork : List CacheQueryResolution → Nat
  | [] => 0
  | query :: rest => marginal_fold_work query + totalMarginalFoldWork rest

@[simp] theorem totalMarginalFoldWork_nil :
    totalMarginalFoldWork [] = 0 := rfl

theorem totalMarginalFoldWork_cons
    (query : CacheQueryResolution)
    (rest : List CacheQueryResolution) :
    totalMarginalFoldWork (query :: rest) =
      marginal_fold_work query + totalMarginalFoldWork rest := rfl

theorem totalMarginalFoldWork_replicate_hits (count : Nat) :
    totalMarginalFoldWork (List.replicate count .hit) = 0 := by
  induction count with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate, totalMarginalFoldWork, marginal_fold_work, ih]

theorem amortize_cold_then_hits
    (work : PositiveFoldWork)
    (count : Nat) :
    totalMarginalFoldWork (.cold_miss work :: List.replicate count .hit) =
      work.val := by
  simp [totalMarginalFoldWork, marginal_fold_work,
    totalMarginalFoldWork_replicate_hits]

theorem cache_observation_master
    (line : CacheLineView)
    (work : PositiveFoldWork)
    (count : Nat) :
    marginal_fold_work .hit = 0 ∧
      marginal_fold_work (.stale_miss work) =
        marginal_fold_work (.cold_miss work) ∧
      (marginal_fold_work (resolveQuery line work) = 0 ↔
        line.occupied ∧ line.keyMatches ∧ line.entryValid) ∧
      totalMarginalFoldWork (.cold_miss work :: List.replicate count .hit) =
        work.val := by
  exact
    ⟨rfl,
      rfl,
      resolve_marginal_zero_iff line work,
      amortize_cold_then_hits work count⟩

end Gnosis
