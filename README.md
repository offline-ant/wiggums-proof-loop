# wiggums-proof-loop

OpenAI dropped a set of proofs, and a lot of people are trying to formulate their interpretation on what this means for their field in general.

The goal here is to add a data point to the discussion.

**151,287 → 113,990 lines of Lean code: a 24.65% reduction.**
Blank lines and comments are not counted. The theorem statement stayed the same.

This experiment asks how much AI models can shrink an existing proof. The process
is simple: make changes, check them, save the working version, and repeat.
The starting point was the Unique Games proof from
[openai/math](https://github.com/openai/math).

This was a side project over a few hours. A few prompts set up the loop, then
the agents worked through repeated rounds of changes and checks.

## Progress

Each row uses the same counting method. It counts the proof and the local files
it needs.

| Stage | Models and setup | Lines left |
|---|---|---:|
| Original | Original proof | 151,287 |
| Rounds 18–19 | Codex agents, one after another | 141,443 |
| Round 20 | One Claude agent | 120,980 |
| Round 21 | Four Codex agents working at the same time | 120,571 |
| Round 22 | 24 Codex agents, each with a separate working copy | 117,213 |
| Round 23 | Another group of 24 Codex agents | **113,990** |

Model names reported by Pi:

- Rounds 18–19 and 21: `openai-codex/gpt-6.1-sol`
- Round 20: `claude-agent/claude-fable-5-1`
- Rounds 22–23: `openai-codex/gpt-6-astra`

All used the high thinking setting. Earlier attempts did not produce changes
that were kept. The prompts asked for 10% or 40% reductions, but these were goals,
not the results of each round.

The agents removed repeated code and reused existing proofs. In later rounds,
they shared build results but kept their working files separate. Up to four
build commands could run at once. After each group finished, their changes were
combined and checked together.

## Checks

- Both versions built successfully from empty project build folders. Existing
  builds of external libraries were reused.
- The final theorem statement matched the original. Lean's kernel, which checks
  proofs, checked the final proof again and accepted it.
- The proof uses only the allowed axioms: `propext`, `Classical.choice`, and
  `Quot.sound`. It does not use `sorryAx`, which allows unfinished proofs.
- The protected model and test files, Lean 4.34.1, and the versions of the external
  libraries stayed the same. The extra Nanoda check was not run.
- All new helper code is counted. Removing unrelated projects from the original
  repository does **not** count as a reduction.

## Check the numbers

The Git history starts with `original-minimal`, followed by `simplified`.
The final count includes all project proof files, even any files no longer used.

```sh
python3 scripts/audit_proof.py --before-repo . --before-rev original-minimal \
  --after-repo . --after-rev simplified --output /tmp/wiggums-audit
```

See [how to repeat the checks and read the results](REPRODUCE.md).

License: Apache-2.0. See [source and change details](MODIFICATIONS.md).
This README was written by the AI that led the work, at Roelof's request.
