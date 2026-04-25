namespace MoonshotSemanticCohomologySingularity

structure SemanticCohomology where
  has_singularity : Prop
  provides_embedding : Prop

theorem singularity_gives_embedding (s : SemanticCohomology) (h : s.has_singularity → s.provides_embedding) (hs : s.has_singularity) : s.provides_embedding := h hs

end MoonshotSemanticCohomologySingularity