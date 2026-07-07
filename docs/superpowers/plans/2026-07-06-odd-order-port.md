# Feit–Thompson Odd Order Theorem — Lean 4 Port Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.
>
> **Adaptation note:** this is a multi-year formalization roadmap, not a single-feature plan. Phase 1 is specified at bite-sized task granularity per the writing-plans skill. Phases 2+ are specified at milestone granularity with exact deliverable statement lists; each milestone gets its own detailed task plan written when it starts (using the evidence in `docs/audit/`). Proof bodies cannot be pre-scripted the way application code can; the TDD analogue used throughout is: *state theorem with `sorry` → `lake build` (expect sorry warning) → prove → `lake build` clean → commit*.

**Goal:** Prove `theorem odd_order_solvable (G : Type*) [Group G] [Finite G] (hodd : Odd (Nat.card G)) : IsSolvable G` in Lean 4/Mathlib, by porting the Coq/MathComp formalization `math-comp/odd-order` (Gonthier et al. 2012; local checkout at `~/feit-thompson/odd-order/theories`, 34 files, 40,531 lines).

**Architecture:** Three-layer port. Layer 0 rebuilds the MathComp prerequisites Mathlib lacks (Hall theory, Fitting subgroup, p-group structure, Frobenius groups, virtual-character theory). Layers 1–2 port the two halves of the proof — Bender–Glauberman local analysis (BGsection1–16 + appendices) and Peterfalvi character theory (PFsection1–14) — mirroring the Coq decomposition at *statement* granularity while proving in idiomatic Mathlib style.

**Tech Stack:** Lean 4 (pinned by `lean-toolchain`, currently v4.32.0-rc1), Mathlib (tag matching toolchain), Lake, GitHub Actions CI (already scaffolded), `lake exe cache` for Mathlib oleans.

## Global Constraints

- Toolchain/Mathlib pinned via `lean-toolchain` + `lakefile.toml` `rev`; bump only via the template's `update.yml` workflow or deliberately, never mid-task.
- Mathlib style linters stay on (`weak.linter.mathlibStandardSet = true` in `lakefile.toml`); every file carries the standard copyright header.
- Character-theory coefficient field is **ℂ** (decision D5 below).
- Port the **Coq statements, not the book statements** where they differ (decision D1 below) — the Coq files repair documented gaps in B&G/Peterfalvi (13.6–13.8, 12.18, 15.2/15.5/15.7, generalized 12.12) and later files depend on the exact repaired forms.
- Every ported theorem records its Coq name in a docstring: `/-- ... (Coq: `BGsection1.critical_odd`) -/`. Maintain `docs/NAME_MAP.md` (Coq identifier → Lean name).
- `sorry` is allowed only as deliberate skeleton (statement-first discipline); CI runs `scripts/count_sorries.sh` and a PR/commit must not increase the count except when explicitly adding new skeleton statements.
- General-purpose Layer-0 material lives under `OddOrder/Mathlib/` (staging namespace mirroring Mathlib's tree) so it can be upstreamed file-by-file; FT-specific material lives under `OddOrder/BG/` and `OddOrder/PF/`.

---

## 0. Evidence base

A 112-agent audit (2026-07-06) produced, with every claim adversarially verified against the local Mathlib checkout (`.lake/packages/mathlib`, commit 360da6fa66, 2026-06-18):

- `docs/audit/survey-digest.md` — per-file survey of all 33 Coq theory files: purpose, book correspondence, main results, machinery, porting hazards.
- `docs/audit/coverage-present.md` — verified Mathlib coverage with exact declarations and line numbers.
- `docs/audit/coverage-missing.md` — verified gaps with the search evidence.

Consult these before starting any file; do not re-derive.

## 1. The target and the source

The Coq development has two halves plus a capstone:

| Part | Files | Lines | Content |
|---|---|---|---|
| Local analysis | BGsection1–16, BGappendixAB, BGappendixC | ~19k | Bender–Glauberman *Local Analysis for the Odd Order Theorem* |
| Character theory | PFsection1–14 | ~20k | Peterfalvi *Character Theory for the Odd Order Theorem* |
| Prereq + capstone | wielandt_fixpoint.v; final theorem in PFsection14 | ~1.9k | Wielandt fixpoint formula; `Feit_Thompson` |

`stripped_odd_order_theorem.v` is the skeptic-proof restatement; its Lean analogue is already stated (sorried) in `OddOrder/Basic.lean`.

## 2. Verified Mathlib coverage (summary of docs/audit/)

**Present, usable as-is** (cite these, don't rebuild): Sylow theory (`Mathlib/GroupTheory/Sylow.lean`); Schur–Zassenhaus *existence* (`Subgroup.exists_right_complement'_of_coprime`); transfer homomorphism + **Burnside normal p-complement** (`MonoidHom.ker_transferSylow_isComplement'`, Transfer.lean); **focal subgroup theorem** (`Subgroup.commutator_inf_eq_focalSubgroup`, Focal.lean, 2026); `IsSolvable` API; Frattini subgroup + Frattini argument (`frattini`, `Sylow.normalizer_sup_eq_top`); p-group basics (center nontrivial, nilpotent); **Z-groups** (`IsZGroup`: solvable, metacyclic classification — matches MathComp's Zgroup needs); semidirect products/`IsComplement'`; three subgroups lemma + Hall–Witt (`Commutator/Basic.lean`); nilpotency series API; representation theory (`Rep`/`FDRep`, Maschke incl. finite fields, Schur, characters + **first** orthogonality over alg. closed fields, `Representation.ind` with Ind⊣Res adjunction); algebraic integers (`integralClosure`, rational-integral ⇒ integer, Kronecker), cyclotomic fields, finite-field Galois theory (`GaloisField`, cyclic Galois group, Hilbert 90 available); `DihedralGroup`, `QuaternionGroup` (defs only); `MonoidHom.FixedPointFree` (involution case only).

**Missing, must be built** (all confirmed by exhaustive search): **Hall π-subgroups** (any notion of π-group/π-core/π-separability — P. Hall existence+conjugacy in solvable groups); SZ *conjugacy*; **coprime action suite** (invariant Sylow/Hall, `C_{G/N}(A) = C_G(A)N/N`, `[G,A,A]=[G,A]`, `G=[G,A]·C_G(A)`, A×B lemma); **Fitting subgroup** (+ Fitting's theorem, self-centralizing in solvable); minimal-normal-subgroup/chief-series API (min normal of solvable is elem. abelian); Frobenius normal p-complement; Thompson J(P)/critical subgroups/Glauberman ZJ (note: the Coq proof substitutes the **Puig subgroup ZL-theorem**, BGappendixAB — port that instead of ZJ); Ω_i/℧^i; p-rank & the `E_p^n`/`E*_p` lattice; SCN subgroups; special/extraspecial p-groups; p-groups with cyclic maximal subgroup (semidihedral/modular groups undefined); **Frobenius groups** (definition, kernel theorem, complement structure, Thompson-nilpotency solvable case); Wielandt fixpoint formula; Clifford theory (module and character levels); faithful-irreducible ⇒ abelian normal subgroups cyclic; **the entire arithmetic character-theory layer**: bundled class functions with inner product, second orthogonality, induced-character *formula* + Frobenius reciprocity as inner-product identity, χ(1) ∣ |G|, character values are algebraic integers, central characters ω_χ, **virtual characters ℤ[Irr G, A]**, inertia/character-level Clifford, **Burnside p^aq^b**, isometries/Dade isometry, coherence/exceptional characters, Galois action on characters.

## 3. Repository layout

```
OddOrder/
  Basic.lean                -- final theorem statement (exists)
  Mathlib/                  -- Layer 0: general infrastructure, Mathlib-style, upstreamable
    GroupTheory/
      PiGroup.lean          -- π-numbers, π-groups, π-cores O_π(G)
      Hall.lean             -- Hall subgroups, P. Hall theorems
      SchurZassenhaus.lean  -- conjugacy half
      CoprimeAction.lean    -- coprime action suite
      Fitting.lean          -- Fitting subgroup
      ChiefFactor.lean      -- minimal normal subgroups, chief series
      PGroup/               -- Omega/agemo, rank, SCN, extraspecial, extremal
      Frobenius.lean        -- Frobenius groups
      PLength.lean          -- p-series, p-length
    RepresentationTheory/
      ClassFunction.lean    -- CF(G), inner product, CF(G, A) support calculus
      CharacterTheory/      -- orthogonality-2, induction formula, integrality,
                            -- degrees, inertia, Clifford, Galois action
      VirtualCharacter.lean -- ℤ[Irr G, A], norm lemmas, isometry extension
      Burnside.lean         -- p^a q^b (milestone theorem)
  BG/                       -- Layer 1: BGsection1–16 + appendices, one dir per file
  PF/                       -- Layer 2: PFsection1–14
  Wielandt.lean             -- wielandt_fixpoint.v
docs/
  audit/                    -- evidence base (committed)
  NAME_MAP.md               -- Coq ↔ Lean names
  superpowers/plans/        -- this plan + per-milestone plans
```

## 4. Dependency structure and porting order

From the survey, the Coq `Require` graph gives two long parallel tracks after Layer 0:

**Track A (pure group theory):** wielandt_fixpoint → BG1 → BG2 → {BG3, BG4, BGappendixAB} → BG5 → BG6 → BG7 → BG8 → BG9 → BG10 → BG11 → BG12 → BG13 → BG14 → BG15 → BG16. BGappendixC is a near-leaf (only consumer: PF14) and can be done any time after the character-formula layer exists.

**Track B (character theory):** PF1 → PF2 → PF3 → PF4 → PF5 → PF6 → PF7. **PF1–7 depend on zero BG files** (PF3/PF7 use only MathComp frobenius facts + BG3's `Frobenius_Wielandt_fixpoint`) — so Track B can run in parallel with Track A up to PF7.

**Merge:** PF8 (needs BG14–16 + PF1–5) → PF9 → PF10 → PF11 → PF12 → PF13 → PF14 → `Feit_Thompson`.

## 5. Design decisions (locked in now; revisit only with written justification)

- **D1 — Statement fidelity:** mirror Coq statements one-to-one (same hypotheses/conclusions, possibly restructured as Lean structures), because downstream files consume the exact repaired/strengthened forms. Giant Coq conjunctions (`[/\ ... & ...]`, e.g. BG14.2/14.7, BGsummaryA–E) become Lean `structure`s with named fields, one field per clause.
- **D2 — Context bundling:** Coq `Section`s with 20–60 `Let`s/`Hypothesis`es (BG10–16, PF9–14) become Prop-valued structures + a namespace of derived-fact lemmas taking the structure as an instance-implicit or explicit argument (e.g. `structure ExceptionalFTMaximal`, `structure PtypeContext`). Prototype this pattern early (BG11 is the smallest case; see M4).
- **D3 — minSimpleOddGroupType:** a class `class MinSimpleOdd (G : Type*) [Group G] [Finite G] : Prop` bundling odd, simple, not solvable, all proper subgroups solvable. The reduction `minSimpleOdd_ind` becomes strong induction on `Nat.card G` using `Subgroup` (no MathComp `subg_of` repackaging needed).
- **D4 — Subgroup calculus:** MathComp `{group gT}` set calculus maps to `Subgroup G` lattice; internal `K ><| H = G` becomes `N.Normal ∧ IsComplement' N H` (+ `SemidirectProduct.mulEquivSubgroup` when the external view is needed); build a small `Subgroup.mul` product-set API early (needed everywhere, thin in Mathlib).
- **D5 — Coefficient field ℂ:** MathComp's `algC` becomes `ℂ`. Mathlib's character API is field-generic with `[IsAlgClosed]`+invertibility instances that ℂ satisfies; ℂ gives conjugation, norms, and `sqrt` needed from PF1 on. Cyclotomic/Galois arguments use `IsCyclotomicExtension ℚ ℚ(ζ) ⊆ ℂ` and `integralClosure ℤ ℂ`.
- **D6 — Irr indexing:** irreducible characters indexed by the characters themselves (`FDRep.character`-level objects or a bespoke `Irr G` type with a `Fintype` instance), not MathComp ordinals `Iirr`. Where PF files do ordinal arithmetic (`inord`, `#1`, `dprod_Iirr` pairing), use the `Irr W1 × Irr W2 ≃ Irr (W1 × W2)` equivalence directly.
- **D7 — PF3's reflection engine:** the 770-line `CyclicTIisoReflexion` boolean-SAT module does NOT get transliterated. Replace with either a small `decide`-friendly finite case analysis (the book does ≤4×2 arrays by hand) or a metaprogrammed decision procedure — decide when reaching M6; budget it as the single largest bespoke-engineering item in Track B.
- **D8 — MatrixGenField / group_closure_field:** MathComp's splitting-field tricks are replaced by: pass to `AlgebraicClosure` (for `group_closure_field`), and use endomorphism-algebra/Schur arguments or Mathlib's Wedderburn little theorem (for `MatrixGenField`, used in BGappendixAB/BG2/PF12; survey confirms PF9's field construction can be simplified via Wedderburn, ~270 lines saved).
- **D9 — Matrix vs module representations:** MathComp `mxrepresentation` statements are restated as statements about `Module (ZMod p) V` with `DistribMulAction`/`Representation (ZMod p) G V`. The `abelem_repr` bridge (G-stable elementary abelian section ⇝ F_p[G]-module) is a named Layer-0 deliverable (`OddOrder/Mathlib/RepresentationTheory/AbelemRepr.lean`), since BG1/2/3/4, BGappendixAB, wielandt_fixpoint, and PF9/12 all consume it.

## 6. Process

**Per-file loop** (applies to every BG*/PF* file):
1. Read the Coq file + survey entry + relevant book section.
2. Write the Lean *statement skeleton*: all exported results as `sorry`-ed theorems with docstrings citing Coq names + book numbers. Section-local (`Let`-bound, non-exported) lemmas are NOT part of the interface — restructure freely.
3. `lake build` (skeleton compiles; sorry count recorded in commit message).
4. Prove, in dependency order within the file, extracting reusable lemmas to `OddOrder/Mathlib/` when they are FT-agnostic.
5. `lake build` clean of new sorries → update `docs/NAME_MAP.md` → commit (one commit per theorem or coherent theorem-group).

**CI/quality gates:** existing `lean_action_ci.yml` builds every push; add `scripts/count_sorries.sh` gate; `#lint` per file. Optionally adopt `leanblueprint` at M3+ for dependency-graph visualization — valuable for a project of this size but not blocking.

**Upstreaming:** anything under `OddOrder/Mathlib/` is written to Mathlib standards; PR to Mathlib opportunistically (Hall theory, Fitting, Frobenius groups, Burnside p^aq^b, second orthogonality are all obvious Mathlib-wanted contributions). Upstreaming reduces our maintenance surface but never blocks the critical path — the local copy is authoritative until a PR merges, then the local file becomes a re-export shim.

## 7. Milestones

Each milestone ends with: `lake build` clean, no new sorries outside declared skeletons, NAME_MAP updated, and a short retro noting interface changes. Estimated sizes are Lean-lines produced (rough, from Coq loc × observed 1.5–2.5× expansion for ssreflect→Lean4).

- **M0 (done 2026-07-06):** project scaffold, target statement, CI, audit evidence committed.
- **M1 — Solvable-group infrastructure (Layer 0a, ~4–6k lines):** π-groups/π-cores; Hall subgroups with P. Hall existence+conjugacy+`Hall_superset`; SZ conjugacy (solvable case); coprime action suite; Fitting subgroup + Fitting's theorem + `C_G(F(G)) ≤ F(G)`; minimal-normal ⇒ elementary abelian; chief-series basics; `Subgroup.mul` API; elementary-abelian ⇝ `ZMod p`-module bridge (`AbelemRepr.lean`, D9). *Standalone value: P. Hall's theorems in Lean for the first time.* Phase-1 tasks below cover the start of M1.
- **M2 — Arithmetic character theory (Layer 0b, ~5–8k lines, parallel with M1):** bundled class functions `CF(G)`/`CF(G,A)` over ℂ with inner product; second orthogonality; induced-character formula + Frobenius reciprocity (inner-product form); integrality (χ(g) ∈ 𝓞, ω_χ ∈ 𝓞, χ(1) ∣ |G|); **Burnside p^aq^b** as acceptance test; virtual characters `ℤ[S, A]` with `vchar_norm1/2`-style lemmas and isometry-extension constructors; character-level Clifford/inertia; `cfAut` Galois action. *Standalone value: Burnside's theorem in Lean for the first time.*
- **M3 — Frobenius groups + Wielandt (Layer 0c, ~2–3k lines, needs M2 for the kernel theorem):** Frobenius group predicate (both action and abstract forms), Frobenius kernel theorem (character-theoretic), semiregular/semiprime predicates, complement structure facts used by BG (Zgroup complements etc. — check `IsZGroup` coverage first), solvable-kernel nilpotency (BG3 needs only the solvable case), `wielandt_fixpoint.v` port (homocyclic decomposition + lifting + order formula).
- **M4 — BG part 1 (BG1–6 + appendices AB, C; ~12–18k lines):** p-length, p-stability/p-constraint definitions, Puig series + ZL-theorem (AppendixAB), GL₂ theorems (BG2 via D9), BG3 Frobenius/representation workhorses, rank-2 structure (BG4), narrow p-groups (BG5), factorizations (BG6). Requires new Layer-0 p-group material as encountered: Ω/℧, critical subgroups (`critical_odd`), SCN, extraspecial/extremal classification, p-rank + `E_p^n` lattice — build these under `OddOrder/Mathlib/GroupTheory/PGroup/` as they arise, since BG4/5 are their only early consumers but BG10+ reuse them heavily.
- **M5 — BG part 2 (BG7–16; ~15–25k lines):** `MinSimpleOdd` framework + maximal-subgroup/uniqueness calculus (BG7), uniqueness theorems (BG8–9), σ/α/β machinery (BG10), τ/kappa classification and the type F/P/P1/P2 → I–V interface (BG11–16). The definitional layer of BG10/BG12/BG14/BG16 is the highest-stakes API design of the whole port (D1/D2 apply with full force); write a dedicated design doc before starting BG10.
- **M6 — PF part 1 (PF1–7; ~10–15k lines, parallel with M4/M5 after M2/M3):** Peterfalvi toolkit (PF1), **Dade isometry** (PF2 — early, load-bearing, only needs PF1), cyclic-TI isometry (PF3 incl. D7 decision), prime-TI (PF4), **coherence framework** (PF5 — API constrains PF6–14), Sibley coherence (PF6, one 770-line proof), invDade + Frobenius-partition non-existence (PF7).
- **M7 — PF part 2 (PF8–14 + BGappendixC; ~15–20k lines):** the merge of both tracks: FT-Dade instances (PF8), type II–IV core analysis (PF9), non-coherence + type V exclusion (PF10), types III/IV structure (PF11), type I Frobenius structure (PF12), the S/T pair (PF13), Appendix C arithmetic, and the final contradiction (PF14).
- **M8 — Capstone:** `Feit_Thompson`, `simple_odd_group_prime`, replace the sorry in `OddOrder/Basic.lean`, optional stripped-statement file mirroring `stripped_odd_order_theorem.v`, announce.

Honest scale statement: the Coq development was ~170k lines (odd-order + the mathcomp layers it drove) built by a professional team over six years. Mathlib's existing coverage and modern automation shrink Layer 0 substantially, but M1–M8 is still an estimated **60–100k lines of new Lean** — a multi-year effort at sustained part-time pace, though every milestone M1–M3, M6 has standalone publication/Mathlib value even if the project stops early.

---

## Phase 1 tasks (start of M1 — fully specified)

### Task 1: Repo layout + directory skeleton

**Files:**
- Create: `OddOrder/Mathlib/GroupTheory/PiGroup.lean`, `docs/NAME_MAP.md`, `scripts/count_sorries.sh`
- Modify: `OddOrder.lean` (imports), `.github/workflows/lean_action_ci.yml` (sorry gate)

**Interfaces:**
- Produces: the directory convention of §3 and the sorry-count gate all later tasks rely on.

- [ ] **Step 1:** Create `scripts/count_sorries.sh`:
```bash
#!/usr/bin/env bash
# Counts sorries in OddOrder/. CI compares against .sorry-budget.
grep -rc --include='*.lean' -E '\bsorry\b' OddOrder/ | awk -F: '{s+=$2} END {print s}'
```
- [ ] **Step 2:** Create `docs/NAME_MAP.md` with a table header (`| Coq | Lean | File |`) and one row for `stripped_Odd_Order → odd_order_solvable`.
- [ ] **Step 3:** Create `OddOrder/Mathlib/GroupTheory/PiGroup.lean` with header + `import Mathlib.GroupTheory.Sylow` + empty namespace; add `import OddOrder.Mathlib.GroupTheory.PiGroup` to `OddOrder.lean`.
- [ ] **Step 4:** `lake build` — expect success. Commit: `chore: layer-0 directory skeleton and sorry gate`.

### Task 2: π-numbers, π-groups, Hall subgroups (definitions + basic API)

**Files:**
- Modify: `OddOrder/Mathlib/GroupTheory/PiGroup.lean`
- Create: `OddOrder/Mathlib/GroupTheory/Hall.lean`

**Interfaces:**
- Produces (later tasks and all of BG consume these exact names):
```lean
def Nat.IsPiNumber (π : Set ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ∈ π
def Subgroup.IsPiGroup (π : Set ℕ) (H : Subgroup G) : Prop := Nat.IsPiNumber π (Nat.card H)
/-- H is a Hall π-subgroup: a π-group whose index is a π'-number. -/
def Subgroup.IsHall (π : Set ℕ) (H : Subgroup G) : Prop :=
  Nat.IsPiNumber π (Nat.card H) ∧ ∀ p ∈ H.index.primeFactors, p ∉ π
```
- Consumes: `Nat.primeFactors`, `Subgroup.index`, `Sylow` API.

- [ ] **Step 1:** Write the three definitions plus basic lemmas as sorried statements: `IsHall.coprime : (Nat.card H).Coprime H.index`, `Sylow.isHall : (P : Subgroup G).IsHall {p}` (for `P : Sylow p G`, `[Finite G]`), monotonicity/conjugation-invariance (`IsHall.map` under `MulEquiv`), `IsHall_top_iff`, and `IsPiGroup` closure under subgroups/quotients.
- [ ] **Step 2:** `lake build` — expect sorry warnings only.
- [ ] **Step 3:** Prove them. Key ingredients (verified present): `Sylow.card_coprime_index` (Sylow.lean:719-ish), `Nat.Coprime` factor lemmas, `Subgroup.index_map`. All are one-to-five-liners.
- [ ] **Step 4:** `lake build` clean; `#lint`. Commit: `feat: pi-groups and Hall subgroup predicate`.

### Task 3: P. Hall existence theorem for solvable groups

**Files:**
- Modify: `OddOrder/Mathlib/GroupTheory/Hall.lean`

**Interfaces:**
- Produces:
```lean
theorem Subgroup.exists_isHall [Finite G] [IsSolvable G] (π : Set ℕ) :
    ∃ H : Subgroup G, H.IsHall π
```
- Consumes: `Subgroup.exists_right_complement'_of_coprime` (SchurZassenhaus.lean:275, verified), minimal-normal-subgroup material from Task 6 (see ordering note).

- [ ] **Step 1:** State with `sorry`; build.
- [ ] **Step 2:** Prove by strong induction on `Nat.card G` (standard Hall argument): take `N` a minimal normal subgroup (elementary abelian `p`-group by Task 6). Case `p ∈ π`: pull back a Hall π-subgroup of `G/N`. Case `p ∉ π`: pull back to `K/N` Hall of `G/N`, then split `K` over `N` by Schur–Zassenhaus existence. The quotient-pullback steps use `Subgroup.comap (QuotientGroup.mk' N)` + index/card arithmetic (`Subgroup.card_eq_card_quotient_mul_card_subgroup`).
- [ ] **Step 3:** `lake build` clean. Commit: `feat: P. Hall existence in solvable groups`.
- **Ordering note:** Tasks 3 and 6 interlock — do Task 6 first if executing sequentially; they are listed in interface-priority order.

### Task 4: Hall conjugacy + Hall_superset (solvable)

**Files:**
- Modify: `OddOrder/Mathlib/GroupTheory/Hall.lean`
- Create: `OddOrder/Mathlib/GroupTheory/SchurZassenhaus.lean` (conjugacy half)

**Interfaces:**
- Produces:
```lean
theorem Subgroup.IsComplement'.conj_of_coprime ... -- SZ conjugacy, solvable case
theorem Subgroup.isHall_conj [Finite G] [IsSolvable G] {H K : Subgroup G}
    (hH : H.IsHall π) (hK : K.IsHall π) : ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom
theorem Subgroup.IsPiGroup.le_isHall_conj [Finite G] [IsSolvable G] {H K : Subgroup G}
    (hH : H.IsPiGroup π) (hK : K.IsHall π) : ∃ g : G, H ≤ K.map (MulAut.conj g).toMonoidHom
```
(MathComp: `Hall_trans`, `Hall_superset`, `SchurZassenhaus_trans_sol`.)

- [ ] **Step 1:** State all three sorried; build. The SZ-conjugacy statement should mirror `exists_right_complement'_of_coprime`'s hypotheses plus `[IsSolvable N]`.
- [ ] **Step 2:** Prove SZ conjugacy (induction on `Nat.card N` through `N` abelian base case — Mathlib's internal `isComplement'_stabilizer_of_coprime`, SchurZassenhaus.lean:112, handles the abelian step).
- [ ] **Step 3:** Prove Hall conjugacy/superset by the same minimal-normal induction as Task 3.
- [ ] **Step 4:** `lake build` clean; commit: `feat: Hall conjugacy and Schur-Zassenhaus conjugacy (solvable)`.

### Task 5: π-core `O_π(G)` and p-core

**Files:**
- Modify: `OddOrder/Mathlib/GroupTheory/PiGroup.lean`

**Interfaces:**
- Produces:
```lean
/-- O_π(G): the largest normal π-subgroup. -/
def Subgroup.pcore (π : Set ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨆ (N : Subgroup G) (_ : N.Normal) (_ : N.IsPiGroup π), N
notation "𝑶_[" π "]" G => Subgroup.pcore π G
theorem pcore_isPiGroup [Finite G] : (𝑶_[π] G).IsPiGroup π    -- needs: normal π ⊔ normal π is π
instance pcore_normal : (𝑶_[π] G).Normal
instance pcore_characteristic : (𝑶_[π] G).Characteristic
theorem pcore_max {N : Subgroup G} [N.Normal] (h : N.IsPiGroup π) : N ≤ 𝑶_[π] G
```
- [ ] **Step 1:** State; the load-bearing lemma is `Normal.isPiGroup_sup` (product of two normal π-subgroups is π) via `Nat.card (N ⊔ M) ∣ Nat.card N * Nat.card M` (from `Subgroup.mul` cardinality — add the needed `Subgroup.mul` API here, D4).
- [ ] **Step 2–4:** build → prove → build clean → commit `feat: pi-core`.

### Task 6: Minimal normal subgroups are elementary abelian (solvable case)

**Files:**
- Create: `OddOrder/Mathlib/GroupTheory/ChiefFactor.lean`

**Interfaces:**
- Produces:
```lean
/-- A minimal normal subgroup: an atom in the lattice of normal subgroups. -/
def Subgroup.IsMinNormal (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup G, M.Normal → M ≤ N → M ≠ ⊥ → M = N
theorem exists_isMinNormal [Finite G] [Nontrivial G] : ∃ N : Subgroup G, N.IsMinNormal
theorem IsMinNormal.elementaryAbelian [Finite G] [IsSolvable G] {N : Subgroup G}
    (hN : N.IsMinNormal) : ∃ p, p.Prime ∧ IsElementaryAbelian p N   -- def below
def IsElementaryAbelian (p : ℕ) (G : Type*) [Group G] : Prop := ... -- comm ∧ ∀ g, g ^ p = 1
```
- [ ] **Step 1:** Define `IsElementaryAbelian` (+ the `Module (ZMod p)` bridge lemma via `AddCommGroup.zmodModule`, Mathlib/Algebra/Module/ZMod.lean:44 — verified) and state the theorems.
- [ ] **Step 2:** Prove: minimal normal `N` of solvable `G` — `N' = ⁅N,N⁆` is characteristic in `N`, normal in `G`, proper (solvability), hence trivial ⇒ `N` abelian; then the `p`-primary component (`CommGroup.primaryComponent`, verified present) is characteristic ⇒ `N` is a `p`-group; then `⟨g^p⟩`-generated subgroup argument via `Ω₁`-style generation.
- [ ] **Step 3–4:** build clean → commit `feat: minimal normal subgroups of solvable groups are elementary abelian`.

### Task 7: Coprime action suite (skeleton, then proofs)

**Files:**
- Create: `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean`

**Interfaces:**
- Produces exact statements (MathComp names in comments) for: `coprime_hall_exists` (A-invariant Hall subgroup exists when coprime solvable A acts), `coprime_hall_trans`, `coprime_quotient_cent` (`C_{G/N}(A) = C_G(A)N/N`), `coprime_cent_prod` (`G = [G,A] * C_G(A)`, G solvable), `coprime_commGid` (`[G,A,A] = [G,A]`), `coprime_abelian_cent_dprod`, `coprime_abelian_gen_cent1` (B&G 1.16). Action formalized as `A : Subgroup (MulAut G)` or a `[Group A] [MulDistribMulAction A G]` parameter — **decide at task start and record in NAME_MAP; this choice propagates through all of BG.**
- [ ] **Step 1:** Skeleton file, all sorried, with the action-encoding decision documented in the module docstring. Build; commit skeleton (`feat(skeleton): coprime action API`).
- [ ] **Step 2+:** Prove in order: quotient-cent (SZ-existence based), cent_prod, commGid, then the Hall variants (need Tasks 3–4). One commit each.

### Task 8: Fitting subgroup

**Files:**
- Create: `OddOrder/Mathlib/GroupTheory/Fitting.lean`

**Interfaces:**
- Produces:
```lean
def Fitting (G : Type*) [Group G] : Subgroup G :=
  ⨆ (N : Subgroup G) (_ : N.Normal) (_ : Group.IsNilpotent N), N
theorem Fitting.isNilpotent [Finite G] : Group.IsNilpotent (Fitting G)   -- Fitting's theorem
instance : (Fitting G).Characteristic
theorem Fitting.max {N} [N.Normal] (h : Group.IsNilpotent N) : N ≤ Fitting G
theorem Fitting.centralizer_le [Finite G] [IsSolvable G] :
    Subgroup.centralizer (Fitting G) ≤ Fitting G                          -- B&G 1.3
theorem Fitting_eq_pcore_prod [Finite G] : ...                            -- F(G) = ∏_p O_p(G)
```
- [ ] **Step 1:** State all; build.
- [ ] **Step 2:** Fitting's theorem: for finite groups prove via `Fitting_eq_pcore_prod` route (join of normal nilpotent subgroups: reduce to two, `N ⊔ M` nilpotent via `[N,M] ≤ N ⊓ M` + `isNilpotent_of_finite_tfae`'s all-Sylows-normal characterization — verified present, Nilpotent.lean:1237).
- [ ] **Step 3:** `centralizer_le` by chief-series stabilizer argument (B&G 1.2/1.3; needs Task 6 chief series — this is the first genuinely hard proof of the port, ~150–300 lines; budget accordingly).
- [ ] **Step 4:** build clean → commit `feat: Fitting subgroup and Fitting's theorem`.

### Task 9: M2 kickoff — class functions and second orthogonality (parallel track)

**Files:**
- Create: `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean`

**Interfaces:**
- Produces: `ClassFunction G` (ℂ-valued, bundled), inner product `⟪φ, ψ⟫ := (Nat.card G)⁻¹ * ∑ g, φ g * star (ψ g)`, `CF(G, A)` as the subspace supported on `A`, restatement of Mathlib's `char_orthonormal` in this language, and the **second orthogonality relation** (new: `∑_{χ ∈ Irr G} χ g * star (χ h) = if conj then |C_G(g)| else 0`).
- [ ] **Step 1:** Design note in module docstring: relation to `FDRep.character` (build on it, don't fork); `Irr G` as a `Finset (ClassFunction G)` or subtype with `Fintype` — decide, record.
- [ ] **Step 2+:** skeleton → orthonormality transfer → completeness (#Irr = #conjClasses — *missing in Mathlib, real work*: via center of group algebra / `IsSemisimpleRing k[G]` Wedderburn pieces, `exists_algEquiv_pi_matrix_of_isAlgClosed` verified present) → second orthogonality as corollary. Commit per result.

**After Task 9,** write `docs/superpowers/plans/<date>-m2-character-theory.md` (full M2 task breakdown: induction formula, integrality, Burnside) using the same format, informed by what Task 9 revealed about the `FDRep` interface.

---

## Risks

1. **Scale/attrition** — mitigated by milestone ordering: M1 (Hall), M2 (Burnside p^aq^b), M3 (Frobenius kernel theorem), M6 (Dade isometry/coherence) each have standalone value as Mathlib contributions even if the port never finishes.
2. **API lock-in at BG10/BG16 and PF5** — the σ/τ/type-I–V vocabulary and the coherence framework constrain everything downstream; mitigation: dedicated design docs + a review pass over downstream consumers (survey lists them per file) *before* proving anything in those files.
3. **Mathlib churn** — pinned toolchain; template's `update.yml` does scheduled bumps; `OddOrder/Mathlib/` shims isolate upstreamed material.
4. **PF3 reflection engine (D7)** and **BG14.7's ~600-line proof** — known single-item schedule risks; both flagged in survey with mitigation options (decision procedure / decomposition into named lemmas).
5. **Coq-idiom impedance** (set-based subgroup calculus, `gFunctor` automation, `Iirr` ordinals) — mitigated by D4/D6 conventions and by building the `Subgroup.mul` and quotient-transport lemma kits in M1 rather than ad hoc.
6. **Audit staleness** — Mathlib moves; re-run the coverage audit (workflow script is saved) before starting each milestone; the 2026-06 checkout already contained surprises (Focal.lean, IsZGroup) that older knowledge would have missed.

## Self-review

- Spec coverage: every Coq file appears in exactly one milestone (M3: wielandt; M4: BG1–6+AB+C skeleton, C proved in M7 context; M5: BG7–16; M6: PF1–7; M7: PF8–14); Layer-0 gaps from the verified audit each map to a Phase-1 task or a named milestone deliverable.
- Placeholder scan: Phases 2+ are declared milestone-level by design (see adaptation note); Phase-1 tasks carry concrete code and named Mathlib lemmas verified to exist by the audit.
- Type consistency: `IsHall`/`IsPiGroup`/`pcore`/`Fitting`/`IsMinNormal`/`IsElementaryAbelian` names used consistently across Tasks 2–8; Task 7's action-encoding decision is deliberately deferred and flagged.
