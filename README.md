# wiggums-proof-loop

**“Simplify/shrink this proof”, repeatedly: 151,287 → 113,990 nonblank,
noncomment Lean lines. Down 24.65%, with the protected theorem unchanged.**

This is a human-directed, AI-executed experiment on the Unique Games formalization
from [openai/math](https://github.com/openai/math). Hours of churning through
consumer model access and credits—not a new mathematical result.

Infinite compression is impossible. But before deciding how much proof
simplification needs humans, test how much of that work models can do.
Inspired by [this HN comment](https://news.ycombinator.com/item?id=50008910)
on [Terence Tao’s Math 2.0 discussion](https://mathstodon.xyz/@tao/117395269325940185).
Smaller source does **not** establish better exposition or human understanding.

## Progress

Same counting method, complete local theorem import closure at each stage:

| Stage | Model / arrangement | Lines remaining |
|---|---|---:|
| Original | Upstream proof | 151,287 |
| Rounds 18–19 | Codex; sequential delegates | 141,443 |
| Round 20 | One Claude round | 120,980 |
| Round 21 | Codex; four parallel agents | 120,571 |
| Round 22 | Codex; 24 isolated worktrees | 117,213 |
| Round 23 | Codex; another 24-worktree batch | **113,990** |

Pi-reported model IDs: `openai-codex/gpt-6.1-sol` through round 21;
`claude-agent/claude-fable-5-1` for round 20;
`openai-codex/gpt-6-astra` for rounds 22–23. High thinking.
Earlier attempts produced no accepted commits. The 10%/40% prompts were ambitions,
not achieved per-round reductions.

Simplify, compile, commit, repeat. Later batches shared native compiler artifacts,
kept writable builds isolated, and used four compilation slots. Savings came from
removing redundant constructions and sharing machine, sampling and algebra proofs.

## Checked, not just counted

- Original-minimal and final snapshots both built from empty project build trees.
- Final protected-statement comparison, **fresh Lean kernel replay**, and axiom audit passed.
- Only `propext`, `Classical.choice`, `Quot.sound`; no proof `sorryAx`.
- Same Model/challenge bytes, Lean 4.34.1 and retained dependency pins. Nanoda disabled.
- All added helpers count. Unrelated monorepo projects do **not** count as savings.

History starts with `original-minimal`, then `simplified`; compare them directly.
The final count includes every retained project source, not just reachable files.
[Reproduction, exact manifests and verification evidence](REPRODUCE.md).

```sh
python3 scripts/audit_proof.py --before-repo . --before-rev original-minimal \
  --after-repo . --after-rev simplified --output /tmp/wiggums-audit
```

Apache-2.0; upstream attribution and changes: [MODIFICATIONS.md](MODIFICATIONS.md).
This README was written by the supervising AI at Roelof’s request.
