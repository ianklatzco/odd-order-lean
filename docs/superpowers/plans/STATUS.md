# Port Status & Continuation Guide

> **This is the resume point.** Any fresh session or subagent continuing the port reads this file first, then the plan it points to. Update this file (and commit) whenever a task completes.

## Current state (as of 2026-07-07, commit `72346a5`)

**Phase 1 is complete** — all 9 tasks of the [master plan](2026-07-06-odd-order-port.md)'s Phase 1, each implemented by a fresh subagent, adversarially reviewed (spec + quality), fix rounds applied, and closed by a whole-phase final review. ~4,000 lines of new Lean in `OddOrder/Mathlib/`, sorry count = 1 (the target theorem `odd_order_solvable` in `OddOrder/Basic.lean` — the only sorry the budget allows).

| Plan task | Result | Commits |
|---|---|---|
| 1. Repo skeleton + sorry gate | done | `16d72c6` |
| 2. π-groups + `IsHall` API | done | `d785d57` |
| 6. Minimal normal ⇒ elementary abelian | done | `170daba` |
| 3. **P. Hall existence** (solvable) | done | `c696e2e` |
| 4. **Hall conjugacy + covering, SZ conjugacy** | done | `8b747c1` |
| 5. π-core `Subgroup.pcore` (+ scoped `𝑶_[π]`) | done | `877d9a0`, `0a031c8` |
| 7. **Coprime action suite** (full, incl. invariant Hall) | done | `fb3a30e`..`c9066cd`, fix `0a031c8` |
| 8. **Fitting subgroup + Fitting's thm + B&G 1.3** | done | `247b7fd`, `0a90f84`, fix `168f460` |
| 9. **Class functions, #Irr = #classes, 2nd orthogonality** | done | `4b9eedd`..`573a6aa`, fix `fc70f80` |
| Phase-1 polish (final review fixes) | done | `72346a5` |

Milestone progress: M0 ✅ · M1 ~85% · M2 ~20% · M3–M8 not started. None of the 34 Coq theory files is ported yet — everything so far is Layer-0 prerequisites, per plan sequencing.

## What to work on next (in order)

1. **M2 continuation** — follow [2026-07-07-m2-character-theory.md](2026-07-07-m2-character-theory.md) task by task (induced characters + Frobenius reciprocity → integrality → **Burnside p^aq^b** → virtual characters → cfAut). Headline target: Burnside.
2. **M1 remainder** — the D9 bridge (`AbelemRepr.lean`: G-stable elementary abelian section ⇝ `ZMod p`-module with G-action); remaining p-group material lands with M4 per plan.
3. **Internal-action transfer layer** (final review, rec 4) — lemmas identifying `FixedPoints.subgroup A H` with centralizer intersections and `actionCommutator` with `⁅H,A⁆` for internal (conjugation) actions. **Do this before starting BG1**; it is the first M4-adjacent task.
4. **M3** (Frobenius groups + Wielandt) — needs M2's induced-character formula for the kernel theorem.

## Deferred items (fix on first touch of the relevant file — do not sprint)

- Helper consolidation: promote `commutator_lt_of_isSolvable` (private in CoprimeAction.lean, inlined in SchurZassenhaus.lean) to one public copy; extract `isMulCommutative_of_commutator_eq_bot`; move generic card helpers (`card_subgroupOf`, `card_lt_card_of_ne_top`, `card_quotient_lt_card_of_ne_bot`, `card_comap_mk'`, `card_map_of_disjoint_ker`) from SchurZassenhaus.lean down to PiGroup.lean; dedupe the ~40-line elementary-abelian argument (ChiefFactor.lean vs CoprimeAction.lean) via a predicate-parameterized core lemma.
- `CoprimeAction.lean` (1,229 lines) wants splitting into SMulInvariant / actionCommutator / semidirect-bridge / suite files before it grows.
- `IsHall`'s second component could be restated as `Nat.IsPiNumber πᶜ H.index` (defeq today; would remove recurring `show`-bridges).
- Verify the `FittingEgen` NAME_MAP row against a real MathComp checkout.
- Monitor the two priority-100 global instances in CoprimeAction.lean; scope them if elaboration slows.
- Upstreaming order (final review, rec 3): PiGroup+Hall predicate → SZ conjugacy (into Mathlib's own file) → Hall theorems → fitting → ChiefFactor → CoprimeAction → ClassFunction last.

## Standing conventions (bind every future task; see master plan §Global Constraints for the full list)

- Coq statements mirrored at statement granularity for FT-specific parts; **follow the Coq file, not the book**, where they differ.
- ℂ is the character coefficient field. Sums over elements use `[Fintype G]`; exported counting statements use `Nat.card` (policy paragraph in the M2 plan).
- Conjugation spelling: `H.map (MulAut.conj g).toMonoidHom` everywhere. Coprime actions: external `[MulDistribMulAction A G]` + explicit coprimality (see CoprimeAction.lean module docstring).
- Every new `.lean` file: standard 2026 Ian Klatzco / Apache 2.0 header; Mathlib style linters must pass; docstrings cite MathComp counterparts; update `docs/NAME_MAP.md`.
- Sorry budget: `.sorry-budget` (currently 1). Never weaken a statement to close a sorry; use the DONE_WITH_CONCERNS protocol (bump budget + `-- TODO(task-N):` + NAME_MAP "(stated)") only as documented in the plan.
- Commit trailers: `Co-Authored-By: Claude ...` per session harness; do not push unless the driving session says to.

## How to throw this at a subagent (dispatch recipe)

Give an implementer subagent, verbatim plus the task specifics:

> Work from /home/user/feit-thompson/odd-order-lean (branch main; commit, do NOT push). `lake` is on PATH; iterate with `lake build <Module.Name>`; full `lake build` must end clean except the one budgeted sorry in OddOrder/Basic.lean, and `bash scripts/count_sorries.sh` must print the value in `.sorry-budget`.
> Read first: docs/superpowers/plans/STATUS.md (state + conventions), then your task's section in [the relevant plan file]. GREP `.lake/packages/mathlib/Mathlib/` for exact lemma names — never trust recall; `docs/audit/coverage-present.md` lists audit-verified declarations. Existing project API: grep `OddOrder/Mathlib/` before re-proving anything.
> Escalate (BLOCKED, with the precise stuck point and what you tried) instead of weakening statements. Write a full report; return a short status.

Review every task's diff before building on it (spec fidelity + a named-risk check that cited Mathlib lemmas exist as used). The driving session should follow superpowers:subagent-driven-development; per-task briefs/reports go in `.superpowers/sdd/` (gitignored scratch — durable state belongs HERE, committed).

## Key artifacts

- Master roadmap: [2026-07-06-odd-order-port.md](2026-07-06-odd-order-port.md) (Phase 1 tasks now historical; §1–§7 still govern)
- M2 plan: [2026-07-07-m2-character-theory.md](2026-07-07-m2-character-theory.md)
- Audit evidence: `docs/audit/` (survey of all 33 Coq files + verified Mathlib coverage)
- Name mapping: `docs/NAME_MAP.md`
- Coq source being ported: `~/feit-thompson/odd-order/theories/`
