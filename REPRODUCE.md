# Reproduce the comparison and checks

## What is being compared

- `original-minimal` (`aea301ea6e3dff8103da30c5771e1f58b9debbc9`): exact committed
  proof-source bytes from [openai/math](https://github.com/openai/math) at
  `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, restricted to the recursive local
  imports of `OAI.Computability.UniqueGames.Main`.
- `simplified` (`b309f70ca0e80e9b1819b3c5c9177d7726fe139f`): the final proof snapshot,
  including modification notices. Equivalent to local development commit
  `14af69d4e8f72b52765739d1d3506b9b8a18a4c0` plus one comment in each modified
  upstream source file. Both exact extractions were hash-checked.

The minimal Lake configuration is common to both snapshots. It is intentionally
not the original monorepo's larger package configuration. The Model, challenge,
challenge JSON, toolchain and retained dependency pins are unchanged.

This publication history is a consolidated before/after comparison, not a claim
that one edit produced the reduction. Original development history is preserved
locally. Intermediate stages in [stages.json](evidence/stages.json) were remeasured
from those recorded development commits using the same import-closure counter;
only the original and final source snapshots are bundled here.

```sh
python3 scripts/audit_proof.py --self-test
python3 scripts/audit_proof.py \
  --before-repo . --before-rev original-minimal \
  --after-repo . --after-rev simplified --output /tmp/wiggums-audit
git diff --stat original-minimal simplified -- OAI
```

The script reads committed blobs, follows local imports/reexports, handles nested
comments and strings, rejects unrecognized import syntax and missing OAI imports,
and counts **all retained project Lean sources** on the final side. None are
currently off-closure. The challenge, packaging, Mathlib and standard library are
excluded symmetrically. All six added proof files are included.

| Measure | Original | Published final |
|---|---:|---:|
| Proof files | 478 | 450 |
| Physical lines | 186,782 | 143,714 |
| Nonblank, noncomment lines | 151,287 | 113,990 |
| Approximate lexical tokens | 1,987,797 | 1,499,962 |
| Source bytes | 8,704,327 | 6,641,554 |

The headline **24.6531%** is the nonblank, noncomment line reduction. The token
count is a word/punctuation regex estimate, not Lean lexer tokens or billing tokens.
Published physical-line/byte totals include 387 license modification comments;
these do not change substantive-line/token totals. Source inventory:
387 changed, 57 unchanged, 34 removed, 6 added. Exact per-file hashes, imports and
metrics are in [audit.json](evidence/audit.json).

## Build

Install [elan](https://github.com/leanprover/elan), Git and the usual Lean build
prerequisites. From this checkout:

```sh
elan toolchain install leanprover/lean4:v4.34.1
lake exe cache get
lake build OAI.Computability.UniqueGames.Main ComparatorChallenges.UniqueGamesTheorem
```

Lake fetches dependencies from the committed manifest; do not update their pins.
The normal commands above are not a sandbox. To inspect untrusted modifications,
use a suitable isolation environment. Our actual build commands used the local
Landrun wrapper described below.

To build the baseline separately:

```sh
git worktree add --detach ../wiggums-original original-minimal
cd ../wiggums-original
lake exe cache get
lake build OAI.Computability.UniqueGames.Main ComparatorChallenges.UniqueGamesTheorem
```

## Kernel and axiom verification

Both publication snapshots passed builds starting with empty project build trees
(479 original and 451 simplified project/challenge modules compiled). Pinned
external dependency artifacts were reused; this was not a cold rebuild of Mathlib.

The exact simplified snapshot then passed a fresh protected-statement comparison,
permitted-axiom check, and Lean default-kernel replay. This was actually rerun,
not copied from an earlier result. See [verification summary](evidence/SUMMARY.md),
[machine-readable result](evidence/result.json), and the complete logs beside them.

Tools used:
- Lean **4.34.1**, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- [Comparator](https://github.com/leanprover/comparator)
  `d03acab154d269c06e60e4de7e4cc85deebff94b`.
- [lean4export](https://github.com/leanprover/lean4export)
  `076e8e57707e813375e8f9da8bf989799ace9680`.
- [Landrun](https://github.com/Zouuup/landrun)
  `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`.

Build Comparator/exporter with Lean 4.34.1, setting the exporter's Lake dependency
revision to the commit above. With those executables and Landrun on PATH, the core
verification command is:

```sh
lake env comparator ComparatorChallenges/UniqueGamesTheorem.json
```

The archived `*-command.txt` files contain our exact additional outer sandbox
and environment settings, including read-only dependencies. They contain local
installation paths and must be adapted to another machine. On our pre-7.1 Linux
kernel we also used the included x86_64-only `scripts/no-af-unix.c` mitigation:

```sh
cc -O2 -Wall -Wextra -Werror -o /path/to/bin/no-af-unix scripts/no-af-unix.c
# Place landrun in the same bin directory.
UG_SANDBOX_BIN=/path/to/bin ./scripts/build.sh --no-build
```

The wrapper's default sandbox path is specific to the development machine; set
`UG_SANDBOX_BIN` elsewhere. The mitigation is local security code, not a claim of
an independently certified sandbox. The publication wrapper keeps its parent
shell alive so cache locks survive the child's inherited-descriptor cleanup.

The independent axiom probe is just:

```lean
import OAI.Computability.UniqueGames.Main
#print axioms OAI.UniqueGamesTheorem.theorem11
```

Run it with `lake env lean /path/to/probe.lean` after building. Expected result:
`[propext, Classical.choice, Quot.sound]`. The challenge deliberately contains a
`sorry` placeholder for comparison; it is not the submitted proof. The target's
transitive axiom set contains no `sorryAx`. Nanoda is disabled in the unchanged
upstream configuration. Ordinary style/unused-variable warnings remain.

This verifies the formal fixed-error polynomial-time binary-3SAT-to-translation-
Unique-Games gap reduction under the installed Lean/tooling trust base. It does
not separately prove 3SAT NP-completeness, P≠NP, better human readability, or new
mathematical insight.
