import Lake

open Lake DSL

package OAI where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]
  enableArtifactCache := if get_config? cacheWrite == some "true" then some true else none
  restoreAllArtifacts := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target]
lean_lib OAI.Computability where
  roots := #[`OAI.Computability.UniqueGames.Main]
  globs := #[`OAI.Computability.UniqueGames.+]

lean_lib ComparatorChallenges where
  globs := #[`ComparatorChallenges.+]
