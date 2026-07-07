#!/usr/bin/env bash
# Counts sorries in OddOrder/. CI compares against .sorry-budget.
grep -rc --include='*.lean' -E '\bsorry\b' OddOrder/ | awk -F: '{s+=$2} END {print s}'
