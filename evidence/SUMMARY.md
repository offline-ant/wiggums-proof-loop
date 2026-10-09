# Publication packaging verification — PASS

Checked original-minimal `aea301ea6e3dff8103da30c5771e1f58b9debbc9` and simplified `b309f70ca0e80e9b1819b3c5c9177d7726fe139f` (including its modification-notice comments).

Both were built from initially empty private root build trees, with pinned shared dependencies read-only, two native sandboxed Lake readers and no concurrent cache publisher. Original Main + protected challenge passed (9402 jobs); simplified Main + protected challenge passed (9374 jobs). Both exit 0. Root sources and configs were hashed before/after and checked against their exact committed blobs.

On the published simplified snapshot, the original Comparator freshly exported the challenge and solution, matched the theorem, checked permitted axioms, and replayed the solution through Lean's default kernel. Exit 0: `Lean default kernel accepts the solution`; `Your solution is okay!`. Independent `#print axioms` returned exactly `[propext, Classical.choice, Quot.sound]`, exit 0. Model, challenge/config and toolchain match upstream original bytes. Nanoda remains disabled in the unchanged original configuration.

All commands use native Lake with real Landrun + no-af-unix, cleared environment, no network grants, and readonly dependencies. The outer Comparator sandbox includes readonly `/proc` so nested Landrun can initialize. Logs and exact commands are alongside this summary; `checked-source-sha256.json` records the proof/config snapshots and `result.json` records outcomes and log hashes. No sources were edited and no commits or GitHub actions were performed by the verifier.

After both builds and all checks, `./scripts/build.sh --publish --no-build` on the simplified snapshot succeeded: `All targets up-to-date (9373 jobs)`, exit 0. The new publication repository's checked artifact cache is populated. Both compiler panels and the Comparator panel are closed.

Limits: shared external dependencies reused their pinned existing artifacts; these were fresh root-project builds, not a forced cold rebuild of Mathlib. Comparator kernel replay actually reran. Verification trusts Lean/Comparator/exporter/toolchain and does not establish human readability, new mathematical insight, or independent 3SAT NP-completeness/P≠NP. The unchanged challenge's intentional `sorry` supplies only the comparison statement; the submitted theorem's transitive axiom set excludes `sorryAx`. Ordinary unused-variable/style warnings remain unchanged.
