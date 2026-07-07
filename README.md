# odd-order-lean

A Lean 4 / Mathlib port of the Coq/MathComp formalization of the
**Feit–Thompson odd order theorem** (every finite group of odd order is
solvable). The port mirrors the Coq development at statement granularity
while proving in idiomatic Mathlib style: a Mathlib-prerequisites layer
(Hall theory, coprime actions, the Fitting subgroup, character theory, …)
under `OddOrder/Mathlib/`, followed by the Bender–Glauberman local analysis
and the Peterfalvi character-theoretic chapters.

The source being ported is [math-comp/odd-order](https://github.com/math-comp/odd-order)
(Gonthier et al.), distributed under the CeCILL-B license.

This repository is licensed under Apache 2.0 (see `LICENSE`).

Roadmap: `docs/superpowers/plans/2026-07-06-odd-order-port.md`.
