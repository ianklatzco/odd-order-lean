# odd-order-lean

A Lean 4 / Mathlib port of the Coq/MathComp formalization of the
**Feit–Thompson odd order theorem** (every finite group of odd order is
solvable). The port mirrors the Coq development at statement granularity
while proving in idiomatic Mathlib style: a Mathlib-prerequisites layer
(Hall theory, coprime actions, the Fitting subgroup, character theory, …)
under `OddOrder/Mathlib/`, followed by the Bender–Glauberman local analysis
and the Peterfalvi character-theoretic chapters.

The source being ported is [math-comp/odd-order](https://github.com/math-comp/odd-order)
(Gonthier et al.), distributed under the CeCILL-B license. This repository
is licensed under Apache 2.0 (see `LICENSE`).

**Status:** the target theorem is stated (and is the repo's single
permitted `sorry`, enforced by CI); the solvable-group infrastructure layer
is done — P. Hall's theorems, Schur–Zassenhaus conjugacy, π-cores, the
coprime-action suite, the Fitting subgroup with `C_G(F(G)) ≤ F(G)`, class
functions with `#Irr G = #ConjClasses G` and the second orthogonality
relation — plus the first slice of arithmetic character theory (the ring of
class functions, the character predicate `IsChar`, degrees, and
`∑ χ(1)² = |G|`). None of the 34 Coq theory files is ported yet. Live progress:
[`docs/superpowers/plans/STATUS.md`](docs/superpowers/plans/STATUS.md).

## Setup

```bash
# 1. Lean toolchain manager (skip if you have elan)
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y

# 2. This repo
git clone https://github.com/ianklatzco/odd-order-lean
cd odd-order-lean

# 3. Prebuilt Mathlib oleans (several GB download; avoids hours of compiling)
lake exe cache get

# 4. Build — should finish in about a minute and report exactly one
#    `sorry` warning (OddOrder/Basic.lean: the theorem we're here to prove)
lake build
bash scripts/count_sorries.sh   # prints 1
```

Optional but recommended for porting work — the Coq source being ported,
as a sibling checkout:

```bash
cd .. && git clone https://github.com/math-comp/odd-order
```

(You don't need Coq installed; the `.v` files are read as reference text.
Condensed per-file summaries live in `docs/audit/survey-digest.md` if you'd
rather not read ssreflect.)

## Punchlist

What's open, roughly in dependency order. Detailed task specs live in the
linked plans — read
[`docs/superpowers/plans/STATUS.md`](docs/superpowers/plans/STATUS.md)
first; it has the conventions and a ready-made dispatch prompt for
throwing coding agents at any of these.

**M2 — arithmetic character theory** (plan:
[`2026-07-07-m2-character-theory.md`](docs/superpowers/plans/2026-07-07-m2-character-theory.md)):

- [x] Induced characters: the explicit induction formula and Frobenius
      reciprocity as an inner-product identity on class functions
- [x] Integrality: `χ(g)` is an algebraic integer; central character values
      `ω_χ`; `χ(1) ∣ |G|`
- [ ] **Burnside's `p^a q^b` theorem** — the milestone headline; believed
      unformalized in Lean
- [x] Virtual characters: the lattice `ℤ[S, A]` with norm lemmas (isometry-
      extension constructors deferred to the PF1 plan, per M2 plan scope)
- [ ] Galois action on characters (`cfAut`)

**M1 remainder / pre-BG gates:**

- [ ] `AbelemRepr` bridge: G-stable elementary abelian sections as
      `ZMod p`-modules with G-action (plan decision D9)
- [ ] Internal-action transfer layer: identify `FixedPoints.subgroup A H`
      with centralizer intersections and `actionCommutator` with `⁅H,A⁆`
      for conjugation actions — required before BGsection1

**M3 — Frobenius groups + Wielandt** (needs the induction formula):

- [ ] Frobenius group predicate; Frobenius' kernel theorem
      (character-theoretic); complement structure facts; solvable-kernel
      nilpotency
- [ ] Wielandt fixpoint order formula (`wielandt_fixpoint.v`)

**Then the port proper:** BGsection1 skeleton — the first of the 34 Coq
files (master plan §7, milestone M4).

**Housekeeping (good first tasks):**

- [ ] Helper consolidation + file split, per the deferred list in
      [`STATUS.md`](docs/superpowers/plans/STATUS.md)
- [ ] Upstream PRs to Mathlib: the Hall theorems, SZ conjugacy, `fitting`,
      π-cores are PR-ready modulo review polish (ordering in STATUS.md)

## Contributing (humans and agents)

1. Read [`STATUS.md`](docs/superpowers/plans/STATUS.md) — state,
   conventions, and the verbatim dispatch recipe for agents.
2. Ground rules that CI enforces or review will: statements mirror the Coq
   development (follow the Coq file, not the book, where they differ); no
   new `sorry` (budget in `.sorry-budget`); Mathlib style linters on;
   every public declaration documents its MathComp counterpart and gets a
   row in `docs/NAME_MAP.md`.
3. Grep the pinned Mathlib (`.lake/packages/mathlib/`) for lemma names
   before trusting recall — `docs/audit/coverage-present.md` lists
   audit-verified declarations with file:line.

Master roadmap: [`docs/superpowers/plans/2026-07-06-odd-order-port.md`](docs/superpowers/plans/2026-07-06-odd-order-port.md).
