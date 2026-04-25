namespace QueueTheoreticInterpretationMapping

structure JacksonNetwork where
  queues : Nat

theorem interpretation_maps_to_queues (network : JacksonNetwork) : network.queues = network.queues := rfl

end QueueTheoreticInterpretationMapping