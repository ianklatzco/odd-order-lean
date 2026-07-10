# M2 — Arithmetic Character Theory Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking. TDD analogue throughout: *state theorem with
> `sorry` → `lake build` (expect sorry warning) → prove → `lake build` clean → commit*.

**Goal:** the arithmetic character theory layer (master plan M2): induced characters +
Frobenius reciprocity, algebraic integrality, **Burnside's p^a q^b theorem** (acceptance
test, standalone Mathlib-first value), virtual characters `'Z[S, A]`, and the `cfAut`
action — everything PF1–7 and the BG character references need that is not
representation-*construction* theory.

**Foundation (Task 9, done):** `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean`
provides `ClassFunction G` (ℂ-valued, bundled, `⟪φ, ψ⟫_[G]` linear in the first argument),
`Irr G` (structure over an existential on simple `ℂ[G]`-submodules, `FunLike`,
noncomputable `Fintype`), first orthogonality (`Irr.cfInner_eq`), completeness
(`Irr.card_eq_card_conjClasses`), `Irr.basis` + expansion
(`ClassFunction.eq_sum_cfInner_smul`), `Representation.char_inv`/`FDRep.char_inv`,
`MonoidAlgebra.mem_center_iff`/`centerEquivClassFunction`, and
`Irr.second_orthogonality`.

**Interface lessons from Task 9 (binding for M2):**

- Work at the `Representation`/`MonoidAlgebra`-module level, **not** `FDRep`, whenever
  semisimplicity or Schur is needed: Mathlib's `Representation.IsIrreducible` ↔
  `IsSimpleModule ℂ[G]` bridge is complete and category-free. `FDRep` is for *restating*
  results, not proving them.
- Avoid `Representation.ofModule`/`RestrictScalars` in statements: typeclass resolution on
  the synonym is broken in this snapshot (see task-9-report §D9.3). Use
  `Representation.ofModule'` (`MonoidAlgebra.moduleCharacter` is definitionally its
  character).
- Counting statements use `Nat.card`; summation statements use `[Fintype G]` + `∑ g : G`.
- `Irr G` elements are consumed via `FunLike` (`χ g`) and `χ.toClassFunction`; new
  membership facts should be stated as `∃ χ : Irr G, χ.toClassFunction = …` (pattern:
  `Representation.exists_irr_classFunction_eq`).

**Fintype/Nat.card seam policy:** sums over group elements use `[Fintype G]` and
`∑ g : G` (following `Mathlib.RepresentationTheory.Character`), while all *exported*
counting statements are `Nat.card`-phrased (instance-free; convert at the seam with
`Nat.card_eq_fintype_card`). Subgroup/quotient character statements (restriction,
induction, Clifford) will need `Fintype ↥H` alongside `[Finite G]`, since their defining
formulas sum over `H` (or over coset representatives) and `[Finite G]` alone does not
provide the `Fintype ↥H` instance a `∑ h : H` requires — take it as a hypothesis rather
than manufacturing it with `Fintype.ofFinite` inside statements.

**Coercion convention:** `Irr G` now coerces to `ClassFunction G` (via
`Irr.toClassFunction`, with simp lemma `Irr.coe_apply`); new M2 statements should use the
coercion (`↑χ`, e.g. `⟪φ, (χ : ClassFunction G)⟫_[G]`) instead of spelling out
`χ.toClassFunction`. Existing Task-9 statements keep the explicit `.toClassFunction`
form.

**Files:** continue in `OddOrder/Mathlib/RepresentationTheory/` — new files
`CharacterArith.lean` (Tasks 1, 3, 4), `Induced.lean` (Task 2), `Burnside.lean` (Task 5),
`VirtualChar.lean` (Task 6), `CFAut.lean` (Task 7). Split further if any exceeds ~1200
lines. All imported from `OddOrder.lean`; NAME_MAP rows per task.

---

### Task 1: character predicate, degrees, and the ring of class functions

**Interfaces:** `ClassFunction.IsChar φ` (MathComp `character`): `φ` is an ℕ-combination
of `Irr G` — define as `∃ c : Irr G → ℕ, φ = ∑ χ, (c χ : ℂ) • χ.toClassFunction` and prove
equivalent to "character of some finite-dimensional `ℂ[G]`-module" (via semisimple
decomposition of modules, `IsSemisimpleModule` + isotypic machinery already in Mathlib).
Degrees; the trivial character; pointwise ring structure.

- [x] `CommRing (ClassFunction G)` + `Algebra ℂ (ClassFunction G)` (pointwise mul, one);
      `mul_apply`, `one_apply` simp lemmas. (MathComp: `cfun_ring`.)
- [x] `Irr.one : Irr G` — the trivial character (witness: the submodule
      `span ℂ[G] {∑ g, single g 1}`… or via `Representation.exists_irr_classFunction_eq`
      applied to the trivial representation; check `Representation.trivial` +
      `IsIrreducible` instance in Mathlib first). `Irr.one_apply : Irr.one g = 1`.
- [x] `ClassFunction.IsChar`, closure under `+`, `*` (tensor — via module tensor product;
      *defer `*` if painful*, PF needs `+` and `Ind` first — **`*` deferred** per this clause, see task report), `IsChar.cfInner_mem_nat`:
      `⟪φ, χ.toClassFunction⟫_[G] ∈ ℕ` for `IsChar φ`, `χ : Irr G`.
- [x] Degree: `Irr.degree χ := χ 1` with `Irr.degree_eq_finrank` (trace of identity),
      `0 < χ 1` as a real/rational cast statement, and `χ 1 ∈ ℕ` in the form
      `∃ d : ℕ, 0 < d ∧ χ 1 = d`. (MathComp `irr1_deg`, `irr1_gt0`.)
      *Delivered as `Irr.exists_degree` (the `∃ d`-form, covering both MathComp names); no
      named `Irr.degree` def yet — add when Task 4 wants it.*
- [x] Sum-of-squares of degrees = |G| (evaluate second orthogonality at `g = h = 1`) —
      cheap, good sanity theorem. (MathComp `sum_irr1_sq`? — check name at port time.)
- [ ] Optional bridge if PF planning wants it: `Simple (FDRep ℂ G) → IsChar V.classFunction`
      and `V.classFunction ∈ Irr` (needs FDRep-simple → module-simple; assess cost, skip if
      > 100 lines). *Skipped in the Task-1 pass per the assess-cost clause; still open for
      PF planning.*

### Task 2: restriction, induction, Frobenius reciprocity

**Interfaces:** `ClassFunction.res` (MathComp `cfRes`, `'Res[H] φ`),
`ClassFunction.ind` (MathComp `cfInd`, `'Ind[G] φ`) for `H : Subgroup G` — both by
*formula*, no induced-representation construction (MathComp does the same):
`ind φ g = (Nat.card H : ℂ)⁻¹ * ∑ x : G, φ' (x⁻¹ * g * x)` where `φ'` extends `φ` by zero.

- [x] `ClassFunction.res (H : Subgroup G) : ClassFunction G →ₗ[ℂ] ClassFunction H`
      (restriction of a class function on `G` is a class function on `H`: conjugation in
      `H` is conjugation in `G`). `res_apply` simp.
- [x] `ClassFunction.ind (H : Subgroup G) : ClassFunction H →ₗ[ℂ] ClassFunction G` —
      well-definedness: the formula is conjugation-invariant in `g` (reindex `x ↦ …`);
      `ind_apply`; `ind_apply_one : ind φ 1 = (H.index : ℂ) * φ 1`.
- [x] **Frobenius reciprocity** `⟪ind H φ, ψ⟫_[G] = ⟪φ, res H ψ⟫_[H]` (MathComp
      `cfdot_ind` / `Frobenius_reciprocity`) — double-sum interchange; the Task 9
      `cfInnerₗ` + reindexing lemmas carry it.
- [x] `IsChar.ind : IsChar φ → IsChar (ind H φ)` — **via reciprocity, not representations**:
      expand `ind φ` in `Irr.basis`; coefficients `⟪ind φ, χ⟫ = ⟪φ, res χ⟫ ∈ ℕ` since
      `res χ` is a character of `H` (needs `IsChar.res`, which *does* need "restriction of
      a character is a character": restrict the module along `MonoidAlgebra.mapDomainAlgHom`
      of `H.subtype` — check Mathlib for `MonoidAlgebra` functoriality; fallback: restrict
      the `Representation` and use `moduleCharacter` on the asModule).
- [ ] (deliberately skipped in the Task-2 pass per the do-not-gold-plate clause) `res` and `ind` interaction with `supportedOn` (`'CF(G, A)` calculus): minimal now —
      only `ind_supportedOn : φ ∈ supportedOn H A → ind H φ ∈ supportedOn G (⋃ x, x • A • x⁻¹-ish)`
      shaped lemma *when PF1 planning fixes the exact form*; do not gold-plate.

### Task 3: class sums and the center, explicitly

**Interfaces:** the explicit class-sum elements deferred from Task 9(d); needed for the
central-character integrality argument.

- [x] `MonoidAlgebra.classSum (c : ConjClasses G) : MonoidAlgebra ℂ G`
      (`∑ x ∈ carrier, single x 1`; use `Finsupp.equivFunOnFinite`-style indicator like
      Task 9's `centralOfClassFunction` to dodge Finsupp-sum-application pain).
- [x] `classSum_mem_center`; `classSum` is the `centerEquivClassFunction`-preimage of the
      indicator; the class sums are a **basis** of the center (transport `Irr.basis`-style
      argument through `centerEquivClassFunction`).
- [x] Structure constants: `classSum c * classSum d = ∑ e, (a c d e : ℕ) • classSum e`
      with **natural-number** coefficients (count solutions `x * y = z`) — this is the
      integrality workhorse. (MathComp: `gring` structure constants.)

*Done in `ClassSum.lean` (standalone file, not `CharacterArith.lean` — parallel-work isolation + the plan's split clause). Structure constants: `classMulCoeff` (Nat.card of the solution set for the canonical rep `e.out`), `classMulCoeff_eq` (rep-independence), `classSum_mul`. Bonus: `classSum_mk_one`.*

### Task 4: algebraic integrality

**Interfaces:** all statements with `IsIntegral ℤ`; Mathlib's cyclotomic/`IsIntegral` API
is strong (verified in audit).

- [x] `Irr.isIntegral_apply : IsIntegral ℤ (χ g)` — χ(g) is a sum of `orderOf g`-th roots
      of unity. Route: reuse Task 9's eigenprojection decomposition
      (`trace f = ∑ j, ζ^j * trace (Q j)` with `trace (Q j) ∈ ℕ`) — the identity is
      already proved inside `Module.End.trace_pow_pred_eq_star_trace`; **refactor it out**
      as `Module.End.trace_eq_sum_zeta_pow_mul_natCast` (statement:
      `f ^ n = 1 → ∃ m : ℕ → ℕ, trace ℂ V f = ∑ j < n, ζ^j * m j`) rather than reproving.
- [x] Central character `Irr.omega χ (c : ConjClasses G) := |carrier c| * χ (rep) / χ 1`
      — stated via `classSum` action: `z_c` acts on the simple module of `χ` by the scalar
      `ω_χ(c)` (Schur, same pattern as Task 9 completeness); `IsIntegral ℤ (ω_χ c)` from
      Task 3 structure constants (`ω_χ` spans a finitely generated ℤ-module).
- [x] `Irr.degree_dvd_card : (χ 1 : ℂ) ∣ (Nat.card G : ℂ)`-form — actual statement
      `∃ d : ℕ, χ 1 = d ∧ d ∣ Nat.card G` (from `|G|/χ(1) = ∑_c ω_χ(c) * conj (χ c)`
      integral + rational ⇒ integer). (MathComp `dvd_irr1_cardG`.)

### Task 5: Burnside p^a q^b (acceptance test)

- [x] Nonvanishing dichotomy: `Irr.eq_zero_or_norm_eq`. Delivered via **Kronecker's theorem**
      (`NumberField.Embeddings.pow_eq_one_of_norm_le_one`) rather than the norm-product sketch
      above — a fresh Mathlib audit at task-start time found it needs only a weak (`≤ 1`)
      per-embedding bound and skips separability/norm-integrality/rational-descent entirely.
- [x] Class-size lemma: `not_isSimpleGroup_of_conjClasses_card_eq_prime_pow` (a conjugacy class
      of size `p ^ k`, `k > 0`, forces `G` non-simple or abelian — stated as `[IsSimpleGroup G] →
      ¬IsMulCommutative G → ... → False`, the form Stage 3 actually consumes). `Irr.ker` is a
      genuine `MonoidHom.ker`, normal for free; `Irr.mem_ker_iff`/`Irr.eq_one_of_ker_eq_top` as
      planned.
- [x] **`theorem burnside_solvable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {a b : ℕ} {G} [Group G]
      [Finite G] (h : Nat.card G = p ^ a * q ^ b) : IsSolvable G`** — strong induction on
      `Nat.card G` + the class-size lemma + Sylow-center pigeonhole. NAME_MAP: no single
      confirmed Coq identifier for the whole-group headline theorem (MathComp proves it in
      `BGsection1.v`/`PFsection1.v`-adjacent material per the audit); recorded as "stated" in
      `docs/NAME_MAP.md`.

*Done in `OddOrder/Mathlib/RepresentationTheory/Burnside.lean` (commit `0ebe5b6`); full report
`.superpowers/sdd/m2-task5-report.md`. No omissions; the eigen-projection kit behind the
equality-case arguments is duplicated locally (not added to `ClassFunction.lean`) per the
task's commit-scoping instruction — flagged there as a future consolidation candidate.*

### Task 6: virtual characters `'Z[S, A]`

**Interfaces:** MathComp `'Z[S, A]` = ℤ-combinations of a family `S` of characters,
supported on `A`. This is the vocabulary of PF2–7 (Dade isometry, coherence); get the
*definitions and norm lemmas* right, defer the isometry-extension constructors to the PF1
task plan (they need the PF context to state well).

- [x] `VirtualChar S A : AddSubgroup (ClassFunction G)` (ℤ-span of `S` intersected with
      `supportedOn A`); notation scoped `'Z[S, A]`, `'Z[S] := 'Z[S, univ]`; membership
      lemmas; `Irr`-indexed special case with coefficient extraction
      `⟪φ, χ⟫_[G] ∈ ℤ`-form (`∃ n : ℤ, …`).
- [x] Norm lemmas: `vchar_norm1` (φ ∈ 'Z[Irr G], ⟪φ,φ⟫ = 1 → φ = ±χ for some χ ∈ Irr) and
      `vchar_norm2` (norm 2, orthogonal to 1 → χ₁ - χ₂ form) — pure `Finsupp`-support
      arithmetic over the orthonormal basis; the Task 9 `cfInnerₗ`/`Irr.basis` API is
      exactly what these need.
- [x] `IsChar`/`VirtualChar` interaction: a virtual character with `⟪φ, χ⟫ ≥ 0` for all χ
      is a character; difference presentation `φ = φ⁺ - φ⁻`.

*Done in `VirtualChar.lean`. Notation `Z[S, A]` (Lean rejects leading-apostrophe atoms). `vchar_norm2` proved with the honest conclusion (four sign patterns: the stated hypotheses provably do not exclude `±(χ₁+χ₂)`); verify MathComp's exact extra hypothesis on first Coq access. Isometry-extension constructors deferred to PF1 per plan.*

### Task 7: `cfAut` (Galois action on class functions)

- [ ] `ClassFunction.cfAut (σ : ℂ ≃+* ℂ)`-shaped action — MathComp uses ring
      automorphisms of the *algebraics*; decision: act by `σ : ℂ →+* ℂ` with the
      restriction that it fixes… **resolve at task start**: PF usage is `φ^*` (complex
      conjugation) and `(φ^u)` for cyclotomic Galois elements. Minimal honest version:
      (i) conjugation `ClassFunction.conj` (uses `char_inv` to show it permutes Irr), and
      (ii) the `ZMod`-power twist `φ^(u) g := φ (g ^ u)` for `u` coprime to the exponent,
      with "permutes Irr" via integrality (Task 4). State only what PF1 consumes.
- [ ] `Irr.conj : Irr G ≃ Irr G` (the permutation) + fixed-point lemma
      (`χ = χ.conj ↔ ∀ g, χ g ∈ ℝ`-form).

---

## Risks

1. **Integrality analytics (Task 5 dichotomy)** — ~~audit Mathlib before starting Task 5~~
   **AUDITED 2026-07-10, defused; RESOLVED at task-5 implementation time (2026-07-10) via a
   shorter route than originally planned**: `NumberField.Embeddings.pow_eq_one_of_norm_le_one`
   (Kronecker's theorem) needs only a *weak* (`≤ 1`) per-embedding bound and gives the dichotomy
   directly, without `Algebra.norm_eq_prod_embeddings` or the rational-algebraic-integer-descent
   chain the norm-product sketch anticipated. See `.superpowers/sdd/m2-task5-report.md` for the
   full route and the re-audit that found this.
2. **`IsChar.res` module restriction** — `MonoidAlgebra` functoriality along subgroup
   inclusion needs checking (`MonoidAlgebra.mapDomainRingHom`?); fallback via
   `Representation.res`-style composition with `Subgroup.subtype` is always available.
3. **Scope creep in Tasks 6–7** — the PF-facing API (coherence, isometry extension) must
   be co-designed with PF1; this plan deliberately stops at norm lemmas + `cfAut` basics
   and defers the rest to the PF1 task plan (master-plan risk 2: API lock-in).
4. **Task 9 deferred items** — `Irr`'s structural `[Fintype G]`; the `RestrictScalars`
   instance bug (report upstream); `FDRep`-simple bridge — all tracked in
   task-9-report.md self-review, none block M2 Tasks 1–7.

## Self-review

- Spec coverage vs master plan M2 line: class functions + inner product ✓ (Task 9), second
  orthogonality ✓ (Task 9), induced characters + Frobenius reciprocity → Task 2,
  integrality triple (χ(g), ω_χ, χ(1) ∣ |G|) → Task 4, Burnside → Task 5, virtual
  characters + norm lemmas → Task 6, isometry-extension constructors → deferred to PF1
  plan (documented), Clifford/inertia → deferred to PF1 plan (documented — PF-facing form
  unknown until PF1 survey), cfAut → Task 7.
- Dependencies: Task 1 ← Task 9; Task 2 ← Task 1; Task 3 independent of 1–2; Task 4 ← 1,3;
  Task 5 ← 2(light),4; Task 6 ← 1; Task 7 ← 4 (for the twist), conj-part ← 1 only.
  Parallelizable pairs: (2,3), (6,7-conj).
- Placeholder scan: two deliberate deferrals (isometry constructors, Clifford/inertia) are
  named with their destination plan; no silent gaps.
