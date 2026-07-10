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

A collaboration of **Ian Klatzco** and **Rado Kirov** (human direction);
the formalization itself is agent-produced — see
[`formalization.yaml`](formalization.yaml) for full provenance, sources,
automation setup, and review status.

**Status:** the target theorem is stated (and is the repo's single
permitted `sorry`, enforced by CI). None of the 34 Coq theory files is
ported yet — current work is the infrastructure layer. Live progress:
[`docs/superpowers/plans/STATUS.md`](docs/superpowers/plans/STATUS.md).

## Main results so far

All proved **sorry-free**; headline results kernel-audited: `#print axioms`
shows only `[propext, Classical.choice, Quot.sound]`.

| theorem | location | statement |
|---|---|---|
| **Burnside `p^a q^b`** | `burnside_solvable` (`OddOrder/Mathlib/RepresentationTheory/Burnside.lean`) | a finite group of order `p^a·q^b` is solvable (no `p ≠ q` needed); believed first in Lean |
| **P. Hall's theorems** | `Subgroup.exists_isHall`, `isHall_conj`, `IsPiGroup.le_isHall_conj` (`…/GroupTheory/Hall.lean`) | Hall π-subgroups of finite solvable groups exist, are conjugate, and cover π-subgroups; believed first in Lean |
| **Schur–Zassenhaus, conjugacy half** | `IsComplement'.exists_conj_of_coprime` (`…/GroupTheory/SchurZassenhaus.lean`) | complements of a normal solvable Hall subgroup are conjugate (Mathlib has existence only) |
| **Fitting subgroup** | `fitting_isNilpotent`, `fitting_centralizer_le` (`…/GroupTheory/Fitting.lean`) | Fitting's theorem and `C_G(F(G)) ≤ F(G)` for solvable `G` (B&G 1.3) |
| **Character completeness** | `Irr.card_eq_card_conjClasses` (`…/RepresentationTheory/ClassFunction.lean`) | `#Irr G = #ConjClasses G` over ℂ; believed first in Lean |
| **Second orthogonality** | `Irr.second_orthogonality` (same file) | `∑ χ, χ(g)·conj(χ(h)) = if IsConj g h then |C_G(g)| else 0` |
| **Frobenius reciprocity** | `cfInner_ind_eq_cfInner_res` (`…/RepresentationTheory/Induced.lean`) | `⟪Ind φ, ψ⟫_G = ⟪φ, Res ψ⟫_H` at the class-function level |
| **Character integrality** | `Irr.isIntegral_apply`, `Irr.exists_degree_dvd_card` (`…/RepresentationTheory/CharacterArith.lean`) | `χ(g)` is an algebraic integer; `χ(1) ∣ |G|` |
| **Virtual characters** | `IsVirtualChar.exists_sub_of_cfInner_self_eq_two` (`…/RepresentationTheory/VirtualChar.lean`) | norm-2 virtual characters vanishing at 1 are differences of two irreducibles (MathComp `vchar_norm2`, in the shape Peterfalvi consumes) |
| Coprime action suite, π-cores, minimal-normal ⇒ elementary abelian | `…/GroupTheory/{CoprimeAction,PiGroup,ChiefFactor}.lean` | the MathComp `hall.v`/`pgroup.v` layer |

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
- [x] **Burnside's `p^a q^b` theorem** — the milestone headline; believed
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

## lean-eval submissions

[`leaneval/`](leaneval/) contains self-contained lake workspaces packaging
results from this repo as submissions to the lean-eval benchmark. Each
subdirectory is its own lake project (own `lakefile.toml`, `lean-toolchain`,
and vendored dependencies under `Submission/`) so it can be pointed at
independently — the benchmark's CI walks any pointed-at content for
matching lakefile names, rather than requiring this repo's own build.
Currently:

- [`finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow`](leaneval/finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow)
  — Burnside's `p^a q^b` theorem, proved from `burnside_solvable`
  (`OddOrder/Mathlib/RepresentationTheory/Burnside.lean`).

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
