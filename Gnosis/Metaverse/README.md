# Metaverse

Parent: [Gnosis](../README.md)

Children:

- [PrimitiveShapes.lean](./PrimitiveShapes.lean)
- [SubstrateCitySpawn.lean](./SubstrateCitySpawn.lean)

Metaverse modules formalize procedural world-generation rules: substrates,
biomes, social-density city spawning, object placement, and certified topology
constraints for generated scenes.

`PrimitiveShapes.lean` is the lockstep catalog consumed by `aeon-3d`; it also
bridges primitive object names to biome/substrate placement admissibility,
three-sisters spatial composition, cooperation modes, and rootspace movement
constraints.
