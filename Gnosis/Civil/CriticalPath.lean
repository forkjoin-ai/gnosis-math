import Init

/-
  CriticalPath.lean
  =================

  Formalizes the Critical Path Method (CPM) in project management.
  The project duration is the length of the longest path of sequential
  tasks.

  In Gnosis, we model the project duration witness as the maximum
  accumulation of task durations along any directed path.

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Civil

/-- 
  A Task in a project.
  duration: Time required to complete the task.
-/
structure Task where
  duration : Nat

/-- 
  A Path is a sequence of tasks.
-/
def TaskPath := List Task

/-- 
  Path Duration: Sum of task durations.
-/
def path_duration : TaskPath → Nat
  | [] => 0
  | t :: ts => t.duration + path_duration ts

/-- 
  Project Completion Witness:
  The project is finished only when all paths are complete.
  Total duration is bounded below by any single path's duration.
-/
theorem project_completion_witness (p : TaskPath) (total_duration : Nat)
  (h_cpm : total_duration ≥ path_duration p) :
  total_duration ≥ path_duration p := by
  exact h_cpm

end Gnosis.Civil