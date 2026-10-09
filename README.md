# Unique Games: original minimal baseline

Exact transitive local proof sources extracted from `openai/math` commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, with the protected Comparator
challenge. Minimal Lake packaging preserves Lean 4.34.1, autoImplicit=false
and all retained dependency revisions. Original proof source bytes are unchanged.

Upstream: https://github.com/openai/math
License: Apache-2.0; see LICENSE.

This root commit is the original-minimal comparison baseline, not an assertion
that the upstream repository was authored here. The next proof commit contains
the simplification. Unrelated theorem projects are absent from BOTH snapshots.

After installing the pinned Lean toolchain and dependencies, build with
`lake build OAI.Computability.UniqueGames.Main`. Optional local sandbox/cache
helpers require Landrun and no-af-unix; see later publication documentation.
