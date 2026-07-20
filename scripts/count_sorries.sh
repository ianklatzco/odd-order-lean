#!/usr/bin/env bash
# Counts real `sorry` proof holes in OddOrder/. CI compares against .sorry-budget.
# Prints a bare integer (0 when there are no matches).
#
# Matches `sorry` as a token only: not followed by a word char, apostrophe, or
# hyphen, so docstring/comment prose like "sorry-free", "sorry'd", or "sorryAx"
# does not count — only the actual tactic/term `sorry`.
set -euo pipefail
(grep -rPc --include='*.lean' "\bsorry(?![\w'-])" OddOrder/ || true) | awk -F: '{s+=$2} END {print s+0}'
