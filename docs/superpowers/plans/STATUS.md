# Port Status & Continuation Guide

> **This is the resume point.** Any fresh session or subagent continuing the port reads this file first, then the plan it points to. Update this file (and commit) whenever a task completes.
>
> Newcomer-facing setup instructions and the top-level punchlist live in the repo [README](../../../README.md) — keep the two in sync: README carries the what/checkboxes, this file carries the how/conventions/detail.

## Current state (as of 2026-07-19 — **M3 COMPLETE: the infrastructure layer is done**)

**M3 closed same-day** ([M3 plan](2026-07-19-m3-frobenius-wielandt.md), 5 tasks, each Fable implementer + adversarial review + fix rounds; all approved):

| M3 task | Result | Commits |
|---|---|---|
| 1. Internal-action transfer layer (pre-BG dictionary) | done | `091d178`, fix `bbcca8c` |
| 2. AbelemRepr (D9 bridge, `Vec` design) + sanctioned consolidation | done, zero findings | `31f53dd` |
| 3. Frobenius predicates (`IsSemiregular`/`IsSemiprime`/`IsFrobenius` w/ bundled Normal) + counting | done, zero findings | `6afff07` |
| 4. **Frobenius' kernel theorem** (internal + action forms; TI-induction isometry = future PFsection2 Dade seed) | done, zero findings | `9833ebd`..`3018963` |
| 5. **Wielandt fixpoint order formula** (`wielandt_fixpoint.v`, clause-faithful; homocyclic middle third replaced by Maschke+idempotent-lifting route, bypass documented) | done, zero findings | `73384a7`..`e9152ab` |

Milestone tally: **M0 ✅ M1 ✅ M2 ✅ M3 ✅** — Layer 0 is finished (~11.7k lines). **The port proper begins**: next is the BGsection1 skeleton + M4 plan (design doc required before BG10 per master plan), and the PF track (M6: PF1 toolkit → Dade isometry) is now unblocked to run IN PARALLEL — PF1–7 need zero BG files. Deferred-consolidation status: `commutator_lt_of_isSolvable` promotion + elementary-abelian dedup DONE (Task 2); card-helpers relayer, `isMulCommutative_of_commutator_eq_bot` extraction, SchurZassenhaus inline copy, CoprimeAction file split REMAIN (fix on first touch).

## M2 state (as of 2026-07-19 — complete)

**M2 is closed.** Task 7 (`cfAut`, commit `aefedd9`, Fable implementer + adversarial review, approved) delivered `ClassFunction.conjC` + `Irr.conj`/`conjEquiv` + the real-valuedness fixed-point lemma, and the coprime power twist `Irr.powTwist` (coprime-to-exponent), via a general σ-twisting engine on simple `MonoidAlgebra` submodules (MathComp's `map_repr` route — the dispatch's inner-product route was refuted, see `.superpowers/sdd/m2-task7-report.md`). All five earlier-reviewed M2 files plus CharAut.lean have now passed the adversarial gate (2026-07-13 review round + fixes in `e1044cf`).

Milestone progress: M0 ✅ · M1 ~85% · **M2 ✅** · M3–M8 not started. Next up, in order: pre-BG gates (internal-action transfer layer, AbelemRepr D9 bridge, deferred consolidations), then the M3 plan (Frobenius groups + Wielandt — note: Frobenius' kernel theorem carries no novelty claim, six lean-eval systems have solved the eval statement; we build it as reusable port API). After M3, the two tracks (BG local analysis / PF character theory) run in parallel. Also on the record: `burnside_solvable`'s lean-eval submission comparator-passed 2026-07-14 (first Claude entry on that problem); the `feit_thompson` eval problem remains unsolved by all automated systems.

## M2 state (as of 2026-07-10, Tasks 1–6)

Tasks 1–6 of the [M2 plan](2026-07-07-m2-character-theory.md), each by a Sonnet implementer + driving-session review, subsequently all adversarially gate-reviewed (per-task reports in `.superpowers/sdd/`):

| M2 task | Result | Commits |
|---|---|---|
| 1. Ring of class functions, `Irr.one`, `IsChar`, degrees, `∑ χ(1)² = |G|` | done (deferred per plan clauses: `IsChar.mul`, module-equivalence converse) | `3cbd2ae`, docs `69e8395` |
| 2. `ClassFunction.res`/`ind`, **Frobenius reciprocity**, `IsChar.res`/`ind` | done (skipped per clause: `supportedOn` calculus) | `99dc285` |
| 3. `classSum`, center basis, **integer structure constants** (`classMulCoeff`, `classSum_mul`) | done, in `ClassSum.lean` (file split for parallel work) | `9c58dfa` |
| Polish: `⟪·,·⟫_[·]` notation fixed for non-`G` groups (was G-literal-only); new-file headers → Rado Kirov | done | `12f4b5c` |
| 4. Integrality: `Irr.isIntegral_apply`, `Irr.omega` (+`omega_eq`/`omega_mul`/`isIntegral_omega`), `Irr.exists_degree_dvd_card` (+ sanctioned refactor: `Module.End.trace_eq_sum_zeta_pow_mul_natCast` in ClassFunction.lean) | done, no omissions | `deb6900` |
| 6. Virtual characters: `Z[S, A]` lattice, `IsVirtualChar`, ℤ-coefficient extraction, `vchar_norm1`/`vchar_norm2` (honest four-pattern conclusion — see plan annotation), char↔vchar interaction + sign split | done | `dc7bdc1` |
| **5. Burnside's `p^a q^b` theorem** (`burnside_solvable`) — nonvanishing dichotomy (`Irr.eq_zero_or_norm_eq`, via **Kronecker's theorem** rather than the plan's norm-product sketch — shorter, audited fresh), character kernels + class-size lemma (`Irr.ker`, `not_isSimpleGroup_of_conjClasses_card_eq_prime_pow`), strong induction + Sylow-center pigeonhole | done, no omissions | `0ebe5b6` |

Read `.superpowers/sdd/m2-task5-report.md` before touching `Burnside.lean` or attempting a similar analytic-number-theory argument elsewhere: it documents the Kronecker-vs-norm-product route choice, a `set`-on-`Type`-hides-instance-search gotcha, an `Algebra ℤ K` diamond on `CyclotomicField`, and the deliberate local duplication of the eigen-projection kit (kept out of `ClassFunction.lean` this round to keep the commit scoped).

Task 7 (`cfAut`) closed 2026-07-19 — see Current state above.

Environment note (this machine, `/home/rado/odd-order-lean`): disk is tight; the Mathlib olean cache was fetched **targeted** (`lake exe cache get .lake/packages/mathlib/Mathlib/<file>.lean …` for the project's transitive imports) rather than in full. If a new import pulls uncached Mathlib files, extend the fetch the same way instead of running a bare `lake exe cache get` (full cache + archives may not fit). The Coq checkout is *not* present here; use `docs/audit/survey-digest.md` for MathComp reference.

## Phase-1 state (as of 2026-07-07, commit `72346a5`)

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

None of the 34 Coq theory files is ported yet — everything so far is Layer-0 prerequisites, per plan sequencing. (Milestone tally lives in Current state at the top.)

## What to work on next (in order)

1. **Pre-BG gates** — internal-action transfer layer (`FixedPoints.subgroup`/`actionCommutator` ↔ centralizers/commutators for conjugation actions; Phase-1 final review rec 4), the `AbelemRepr.lean` D9 bridge, and the deferred consolidation list below. Then write the **M3 plan** (Frobenius groups + Wielandt) and execute it. Lean-proof friction notes from M2 (still apply to all future tasks: `rfl`-bridge `restrictScalars`-ed equivs; `Representation.trivial_apply` and `Module.finrank_prod` need explicit `ℂ`; keep `[Fintype G]` scoped tightly or the unused-Fintype linter fires; prefer `MonoidAlgebra`-namespaced lemmas over `Finsupp` ones to dodge type-synonym `rw` failures; use `change` not `show` for definitional steps; `refine LinearMap.ext fun x => ?_` instead of bare `ext` near `Finsupp`-backed types; `set` on a `Type` hides it from typeclass search — don't alias cyclotomic-field-style types with `set`; dot notation can fail on `def`-unfolded Pi/Exists types, use prefix form like `IsPGroup.isNilpotent h` instead of `h.isNilpotent`).
2. **M1 remainder** — the D9 bridge (`AbelemRepr.lean`: G-stable elementary abelian section ⇝ `ZMod p`-module with G-action); remaining p-group material lands with M4 per plan.
3. **Internal-action transfer layer** (final review, rec 4) — lemmas identifying `FixedPoints.subgroup A H` with centralizer intersections and `actionCommutator` with `⁅H,A⁆` for internal (conjugation) actions. **Do this before starting BG1**; it is the first M4-adjacent task.
4. **M3** (Frobenius groups + Wielandt) — needs M2's induced-character formula for the kernel theorem.

## Deferred items (fix on first touch of the relevant file — do not sprint)

- Helper consolidation: promote `commutator_lt_of_isSolvable` (private in CoprimeAction.lean, inlined in SchurZassenhaus.lean) to one public copy; extract `isMulCommutative_of_commutator_eq_bot`; move generic card helpers (`card_subgroupOf`, `card_lt_card_of_ne_top`, `card_quotient_lt_card_of_ne_bot`, `card_comap_mk'`, `card_map_of_disjoint_ker`) from SchurZassenhaus.lean down to PiGroup.lean; dedupe the ~40-line elementary-abelian argument (ChiefFactor.lean vs CoprimeAction.lean) via a predicate-parameterized core lemma.
- `CoprimeAction.lean` (1,229 lines) wants splitting into SMulInvariant / actionCommutator / semidirect-bridge / suite files before it grows.
- `IsHall`'s second component could be restated as `Nat.IsPiNumber πᶜ H.index` (defeq today; would remove recurring `show`-bridges).
- Verify the `FittingEgen` NAME_MAP row against a real MathComp checkout.
- `VirtualChar.lean`: the support-restricted `Z[irr G, A]` bridge (MathComp `zcharD1E`-analogue: `φ ∈ Z[image Irr, G^#] ↔ φ.IsVirtualChar ∧ φ 1 = 0`) is not stated yet — the two sides exist separately; land the bundled iff with the PF1 task plan, which fixes the `G^#` spelling (see the future-work note in `docs/NAME_MAP.md`).
- Monitor the two priority-100 global instances in CoprimeAction.lean; scope them if elaboration slows.
- `Representation.isIrreducible_comp_iff` (AbelemRepr.lean) and its `MulEquiv` restatement `Representation.IsIrreducible.compMulEquiv` + `Subrepresentation.orderIsoCompMulEquiv` (Inertia.lean, M6 Task 1) duplicate a 10-line surjective-precomposition transport; consolidate into a shared low-level RepresentationTheory home on first touch (kept separate to avoid importing the CoprimeAction chain into the PF lane).
- Upstreaming order (final review, rec 3): PiGroup+Hall predicate → SZ conjugacy (into Mathlib's own file) → Hall theorems → fitting → ChiefFactor → CoprimeAction → ClassFunction last.

## Standing conventions (bind every future task; see master plan §Global Constraints for the full list)

- Coq statements mirrored at statement granularity for FT-specific parts; **follow the Coq file, not the book**, where they differ.
- ℂ is the character coefficient field. Sums over elements use `[Fintype G]`; exported counting statements use `Nat.card` (policy paragraph in the M2 plan).
- Conjugation spelling: `H.map (MulAut.conj g).toMonoidHom` everywhere. Coprime actions: external `[MulDistribMulAction A G]` + explicit coprimality (see CoprimeAction.lean module docstring).
- Every new `.lean` file: standard 2026 / Apache 2.0 header carrying **the driving collaborator's name** (Ian Klatzco or Rado Kirov — whoever's session created the file; amended 2026-07-19 to resolve the Ian-vs-Rado header conflict flagged in the Task-7 review; existing files keep their headers); Mathlib style linters must pass; docstrings cite MathComp counterparts; update `docs/NAME_MAP.md`.
- Sorry budget: `.sorry-budget` (currently 1). Never weaken a statement to close a sorry; use the DONE_WITH_CONCERNS protocol (bump budget + `-- TODO(task-N):` + NAME_MAP "(stated)") only as documented in the plan.
- Commit trailers: `Co-Authored-By: Claude ...` per session harness; do not push unless the driving session says to.

## How to throw this at a subagent (dispatch recipe)

Give an implementer subagent, verbatim plus the task specifics:

> Work from the repo root (this machine: /home/rado/odd-order-lean; branch main; commit, do NOT push). `lake` is on PATH; iterate with `lake build <Module.Name>`; full `lake build` must end clean except the one budgeted sorry in OddOrder/Basic.lean, and `bash scripts/count_sorries.sh` must print the value in `.sorry-budget`.
> Read first: docs/superpowers/plans/STATUS.md (state + conventions), then your task's section in [the relevant plan file]. GREP `.lake/packages/mathlib/Mathlib/` for exact lemma names — never trust recall; `docs/audit/coverage-present.md` lists audit-verified declarations. Existing project API: grep `OddOrder/Mathlib/` before re-proving anything.
> Escalate (BLOCKED, with the precise stuck point and what you tried) instead of weakening statements. Write a full report; return a short status.

Review every task's diff before building on it (spec fidelity + a named-risk check that cited Mathlib lemmas exist as used). The driving session should follow superpowers:subagent-driven-development; per-task briefs/reports go in `.superpowers/sdd/` (gitignored scratch — durable state belongs HERE, committed).

## Key artifacts

- Master roadmap: [2026-07-06-odd-order-port.md](2026-07-06-odd-order-port.md) (Phase 1 tasks now historical; §1–§7 still govern)
- M2 plan: [2026-07-07-m2-character-theory.md](2026-07-07-m2-character-theory.md)
- Audit evidence: `docs/audit/` (survey of all 33 Coq files + verified Mathlib coverage)
- Name mapping: `docs/NAME_MAP.md`
- Coq source being ported: [math-comp/odd-order](https://github.com/math-comp/odd-order) (sibling checkout when available — as of the M2 review round it IS present at `../odd-order/theories/` (PFsection*.v, BGsection*.v); check there before claiming a name is unverifiable. MathComp *proper* (e.g. `character/vcharacter.v`, `character/integral_char.v`) is still absent — for those, use `docs/audit/survey-digest.md` plus usage sites in the odd-order sources)
