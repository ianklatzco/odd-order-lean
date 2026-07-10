#!/usr/bin/env bash
#
# bundle-submission.sh — vendor this repo's OddOrder modules into a
# lean-eval submission workspace's Submission/ tree.
#
# lean-eval submissions must compile against Mathlib ONLY (they cannot
# `import OddOrder.…`). Given a workspace under leaneval/ and one or more
# root modules, this script copies the root modules and their transitive
# OddOrder imports into `<workspace>/Submission/<Basename>.lean`, rewriting
# `import OddOrder.Mathlib.<Area>.<Name>` -> `import Submission.<Name>`.
# Basenames must be unique across OddOrder/Mathlib/ (they currently are).
#
# Pattern adopted from rkirov/jordan_pick's submission/bundle-engine.sh.
#
# Usage:  scripts/bundle-submission.sh <workspace-dir> <RootModuleBasename>…
#   e.g.  scripts/bundle-submission.sh \
#           leaneval/finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow \
#           Burnside
#
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WS="$1"; shift
OUT="$ROOT/$WS/Submission"
mkdir -p "$OUT"

# find OddOrder/Mathlib/*/<Name>.lean for a basename
srcfile() {
  local hits
  hits=$(find "$ROOT/OddOrder/Mathlib" -name "$1.lean" | head -2)
  [[ $(wc -l <<<"$hits") -eq 1 && -n "$hits" ]] || {
    echo "ERROR: expected exactly one OddOrder/Mathlib/**/$1.lean, got:" >&2
    echo "$hits" >&2; exit 1; }
  echo "$hits"
}

rewrite() { sed -E 's/^import OddOrder\.Mathlib\.[A-Za-z]+\.([A-Za-z0-9]+)/import Submission.\1/'; }

# BFS over the OddOrder import closure
declare -A seen
queue=("$@")
while ((${#queue[@]})); do
  name="${queue[0]}"; queue=("${queue[@]:1}")
  [[ -n "${seen[$name]:-}" ]] && continue
  seen[$name]=1
  src="$(srcfile "$name")"
  rewrite < "$src" > "$OUT/$name.lean"
  while read -r dep; do
    [[ -n "$dep" && -z "${seen[$dep]:-}" ]] && queue+=("$dep")
  done < <(grep -oE '^import OddOrder\.Mathlib\.[A-Za-z]+\.[A-Za-z0-9]+' "$src" \
           | sed -E 's/.*\.([A-Za-z0-9]+)$/\1/')
done

echo "Bundled ${#seen[@]} module(s) -> $OUT: ${!seen[*]}"
echo "Remember: Submission.lean must import the root module(s) as Submission.<Name>,"
echo "keep the harness theorem name/signature verbatim, and pass 'lake build' +"
echo "an axiom check (#print axioms …) inside the workspace."
