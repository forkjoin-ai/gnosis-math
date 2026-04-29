namespace Gnosis

structure TopologicalShatter where
  local_embedding_size : Nat
  global_embedding_size : Nat
  is_shattered : local_embedding_size < global_embedding_size

theorem shatter_bypasses_global (t : TopologicalShatter) :
    t.local_embedding_size < t.global_embedding_size := by
  exact t.is_shattered

end Gnosis