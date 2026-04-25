namespace ForkRaceFold

structure HashCollisionTurbulence where
  abyssal_depth : Nat
  collision_prob : Nat
  collisionUnitCap : collision_prob ≤ 1
  depthPositive : 0 < abyssal_depth

theorem depth_collision_bound (h : HashCollisionTurbulence) (bound : h.collision_prob = 0) :
  h.collision_prob < 1 := by
  rw [bound]
  decide

end ForkRaceFold
