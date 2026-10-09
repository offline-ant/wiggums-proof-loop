#!/usr/bin/env bash
# Thin native Lake wrapper: private outputs, shared immutable cache, one publisher.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
COMMON=$(git -C "$ROOT" rev-parse --path-format=absolute --git-common-dir)
CACHE=${UG_CACHE_DIR:-$COMMON/ug-artifacts}
BIN=${UG_SANDBOX_BIN:-/home/devops/Projects/math-verification-tools/bin}
mkdir -p "$ROOT/.lake" "$CACHE"
# Serialize configuration/output writes within one worktree, not across workers.
exec 201>"$ROOT/.lake/build.lock"
flock -x 201
publish=false; nobuild=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --publish) publish=true; shift ;;
    --no-build) nobuild=(--no-build); shift ;;
    --) shift; break ;;
    *) break ;;
  esac
done
[[ $# -gt 0 ]] || set -- +OAI.Computability.UniqueGames.Main
cd "$ROOT"
LEAN=$(elan which lean)
L=$(dirname "$(dirname "$LEAN")")
# get_config? is elaborated into the lakefile OLean; reconfigure on mode changes.
args=(-R --no-cache "${nobuild[@]}" build "$@")
vars=(PATH="$L/bin:/usr/bin" HOME="$ROOT/.lake" LANG=C.UTF-8 TERM=dumb
  GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null LEAN_ABORT_ON_PANIC=1
  LAKE_CACHE_DIR="$CACHE" LAKE_RESTORE_ARTIFACTS=true)
rights=(--ro "$CACHE"); lock=(-s)
if $publish; then
  # Explicit root setting overrides false; dependencies remain non-writers.
  vars+=(LAKE_ARTIFACT_CACHE=false)
  args=(-KcacheWrite=true "${args[@]}")
  rights=(--rw "$CACHE"); lock=(-x)
fi
ro=(--ro "$ROOT" --ro "$COMMON")
for p in "$ROOT"/.lake/packages/*; do
  [[ -d "$p" ]] || continue
  ro+=(--ro "$(realpath "$p")")
done
[[ -x "$BIN/landrun" && -x "$BIN/no-af-unix" ]] || {
  echo 'Set UG_SANDBOX_BIN to the installed landrun/no-af-unix directory.' >&2; exit 2;
}
# All wrappers use this lock: readers can coexist; publishing excludes readers.
exec 200>"$COMMON/ug-cache.lock"
flock "${lock[@]}" 200
cmd=("$BIN/landrun" --best-effort "${ro[@]}" "${rights[@]}"
  --rw "$ROOT/.lake" --rox "$L" --rox /usr/bin/git --ro /usr/lib
  --ro /etc/ld.so.cache --rw /dev/null --ro /dev/urandom --ldd --add-exec)
for v in "${vars[@]}"; do cmd+=(--env "$v"); done
# Keep this shell alive holding flock descriptors: no-af-unix closes inherited FDs.
env -i "${vars[@]}" "$BIN/no-af-unix" "${cmd[@]}" -- "$L/bin/lake" "${args[@]}"
