#!/usr/bin/env bash
# Create one cheap research branch. No inference, compilation, or shared build dir.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
NAME=${1:?Usage: scripts/worktree.sh NAME [BASE_REF]}
[[ "$NAME" =~ ^[a-zA-Z0-9][a-zA-Z0-9_-]*$ ]] || { echo 'Use a simple branch name.' >&2; exit 2; }
[[ -d "$ROOT/.lake/packages/mathlib" ]] || { echo 'Bootstrap base dependencies first; see README.' >&2; exit 2; }
DEST=${UG_WORKTREE_ROOT:-$(dirname "$ROOT")/unique-games-worktrees}/$NAME
[[ ! -e "$DEST" ]] || { echo "Already exists: $DEST" >&2; exit 2; }
mkdir -p "$(dirname "$DEST")"
git -C "$ROOT" worktree add -b "attempt/$NAME" "$DEST" "${2:-HEAD}"
mkdir -p "$DEST/.lake/packages"
for p in "$ROOT"/.lake/packages/*; do
  [[ -d "$p" ]] || continue
  ln -s "$(realpath "$p")" "$DEST/.lake/packages/$(basename "$p")"
done
printf 'Ready: %s\nBuild changed modules there with ./scripts/build.sh MODULE...\n' "$DEST"
