#!/usr/bin/env bash
# Counts sorries in OddOrder/. CI compares against .sorry-budget.
# Prints a bare integer (0 when there are no matches).
set -euo pipefail
(grep -rc --include='*.lean' -E '\bsorry\b' OddOrder/ || true) | awk -F: '{s+=$2} END {print s+0}'
