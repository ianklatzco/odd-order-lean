/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import OddOrder.Mathlib.RepresentationTheory.Induced

/-!
# Virtual characters: the `ℤ`-span lattice `Z[S, A]`

This file is Task 6 of the M2 character-theory plan: MathComp's virtual-character lattice
`'Z[S, A]` (`vcharacter.v`), the coefficient-extraction lemmas for the `Irr G`-indexed special
case, the norm-1/norm-2 classification lemmas, and the interaction between `IsChar`
(`CharacterArith.lean`) and virtual characters (sign-split into a difference of two
characters). Per the M2 plan, the isometry-extension constructors needed by the PF-section
coherence machinery are *deliberately deferred* to the PF1 task plan; this file only supplies
the definitions and the norm lemmas.

## Notation: `Z[S, A]`, not `'Z[S, A]`

MathComp spells this `'Z[S, A]` (a leading apostrophe). Lean 4's `notation` elaborator
rejects atoms whose first character is a single unescaped `'` (`Lean.Elab.Syntax.isValidAtom`:
an atom may only *start* with `'` if it starts with the doubled `''`), so a literal
`'Z[S, A]` notation cannot be declared. This file uses `Z[S, A]` (no leading quote) as the
closest available spelling; every docstring below cites the MathComp form `'Z[S, A]`
alongside it.

## MathComp correspondence

MathComp's `vcharacter.v` phrases everything through the predicate `zchar S A phi` ("`phi` is
an integer combination of `S` supported on `A`"), not a bundled substructure; this file bundles
the same data as an `AddSubgroup (ClassFunction G)` instead (Lean-idiomatic, and it comes for
free once the two ingredients — a `ℤ`-span submodule and the `ℂ`-submodule `supportedOn` — are
each already `AddSubgroup`s). The membership lemma `ClassFunction.mem_virtualChar_iff` recovers
the `zchar`-shaped predicate. MathComp's `vcharacter.v` itself is not on this machine, but the
odd-order Peterfalvi/Bender–Glauberman sources *are* (sibling checkout,
`odd-order/theories/`), so `vcharacter.v` identifiers are confirmed **by usage** there: the
predicate is spelled `zchar` (used via `mem_zchar`, `zchar_split`, `zcharD1E`, e.g.
PFsection1.v:208, PFsection4.v:305), the difference-of-two-characters characterization is
`vcharP` (PFsection1.v:639), and every actual call of `vchar_norm2`
(PFsection1.v:152–153, 217, 233; PFsection5.v:1597) passes a virtual character lying in
`'Z[irr G, G^#]` — i.e. *vanishing at `1`* — of norm `2`, and consumes a pure difference
`'chi_i - 'chi_j`. Statements internal to `vcharacter.v` that never surface at a PF call
site (e.g. `zchar_expansion`'s exact shape, cited from `docs/audit/survey-digest.md`)
remain flagged "(exact statement unconfirmed)".

## Main definitions

* `ClassFunction.VirtualChar (S : Finset (ClassFunction G)) (A : Set G) : AddSubgroup
  (ClassFunction G)`: the `ℤ`-span of `S`, intersected with the class functions supported on
  `A`. Scoped notation `Z[S, A]`; `Z[S]` abbreviates `Z[S, Set.univ]`. MathComp: `zchar S A`
  (name unconfirmed), notation `'Z[S, A]` / `'Z[S]`.
* `ClassFunction.virtualCharIrr (G) [Fintype G] : AddSubgroup (ClassFunction G)`: the
  `Irr G`-indexed special case (spelled as a plain definition rather than overloading the
  `Z[S, A]` bracket notation with a `S := Irr G` reading — see the design note below for why).
  MathComp: `'Z[irr G]`.
* `ClassFunction.IsVirtualChar (φ : ClassFunction G) : Prop`: `φ` is a `ℤ`-combination of
  `Irr G`, the direct analogue of `CharacterArith.lean`'s `ClassFunction.IsChar` with `ℤ`
  coefficients instead of `ℕ`. Proved equivalent to membership in `virtualCharIrr G`
  (`ClassFunction.isVirtualChar_iff_mem_virtualCharIrr`).

## Main results

* `ClassFunction.mem_virtualChar_iff`: membership in `Z[S, A]` unfolds to an explicit
  `ℤ`-linear combination of `S` plus the support condition. MathComp: `zchar_split` (the
  span/support split of `'Z[S, A]`; usage PFsection1.v:208).
* `ClassFunction.IsVirtualChar.add`/`.neg`/`.sub`: closure of virtual characters under the
  additive group operations. MathComp: the generic `rpredD`/`rpredN`/`rpredB` lemmas applied
  to `zchar` (usage e.g. PFsection1.v:208).
* `ClassFunction.IsVirtualChar.cfInner_mem_intCast`: for `φ ∈ virtualCharIrr G` and
  `χ : Irr G`, `⟪φ, χ⟫_[G] ∈ ℤ`. MathComp: (the integrality half of `zchar_expansion`, exact
  statement unconfirmed).
* `ClassFunction.IsVirtualChar.exists_eq_or_eq_neg_of_cfInner_self_eq_one` (**`vchar_norm1`
  shape**): if `φ.IsVirtualChar` and `⟪φ, φ⟫_[G] = 1` then `φ = χ` or `φ = -χ` for some
  `χ : Irr G`. MathComp: `vchar_norm1P`.
* `ClassFunction.IsVirtualChar.exists_sign_smul_add_of_cfInner_self_eq_two`: the norm-2
  decomposition engine — `⟪φ, φ⟫_[G] = 2` forces `φ = ε₁ • χ₁ + ε₂ • χ₂` with `χ₁ ≠ χ₂` and
  integer signs `ε₁, ε₂ ∈ {1, -1}`. Both `vchar_norm2` shapes below are read off from this.
* `ClassFunction.IsVirtualChar.exists_sub_of_cfInner_self_eq_two` (**`vchar_norm2`, PF
  call-site shape**): if `φ.IsVirtualChar`, `⟪φ, φ⟫_[G] = 2`, and `φ 1 = 0` (vanishing at
  the identity, as for members of `'Z[irr G, G^#]`), then `φ = χ₁ - χ₂` for two distinct
  irreducible characters — the exact shape consumed at every Peterfalvi call site of
  `vchar_norm2` (PFsection1.v:152–153, 217, 233; PFsection5.v:1597). MathComp: `vchar_norm2`.
* `ClassFunction.IsVirtualChar.exists_sub_or_add_of_cfInner_self_eq_two` (four-pattern
  variant): under the *weaker* hypothesis `⟪φ, 1⟫_[G] = 0` (orthogonal to the trivial
  character) the two constituents are *nonprincipal* but the relative sign is not fixed:
  `φ` is one of `χ₁ - χ₂`, `χ₂ - χ₁`, `χ₁ + χ₂`, `-(χ₁ + χ₂)`. See the design note below.
* `ClassFunction.IsChar.isVirtualChar`, `ClassFunction.IsChar.mem_virtualCharIrr`: a character
  is a virtual character. MathComp: (the "characters are virtual characters" direction of
  `char_vchar`, exact statement unconfirmed).
* `ClassFunction.IsVirtualChar.isChar_of_forall_cfInner_nonneg`: a virtual character all of
  whose `Irr`-basis coefficients `⟪φ, χ⟫_[G]` (integers, by `cfInner_mem_intCast`) have
  nonnegative real part is a character.
* `ClassFunction.IsVirtualChar.exists_isChar_sub`: every virtual character `φ` splits as a
  difference of two characters (split the integer coefficients by sign); iff form
  `ClassFunction.isVirtualChar_iff_exists_isChar_sub`. MathComp: `vcharP` (usage
  PFsection1.v:639).

## Design notes

* **Bundling as an `AddSubgroup`.** The plan's own hint is followed literally: `VirtualChar`
  is `(Submodule.span ℤ (S : Set _)).toAddSubgroup ⊓ (supportedOn G A).toAddSubgroup`, using
  the *canonical* `ℤ`-module structure every `AddCommGroup` carries (`zsmul`), not a bespoke
  one. The bridge between this canonical `ℤ`-smul and the `ℂ`-smul spelling used everywhere
  else in the file (`(n : ℂ) • φ`, matching `IsChar`'s `(c χ : ℂ) • χ` convention) is
  `Int.cast_smul_eq_zsmul` (`(n : R) • b = n • b` for any `Ring R` acting via `Module R M`);
  this is exactly the "two different-looking `SMul ℤ` instances actually coincide" fact one
  has to invoke once and then never worry about again.
* **No `Z[Irr G]` bracket notation.** The natural reading of a hypothetical `Z[Irr G]` inside
  the `Z[S]` bracket-notation family would require `S := Irr G`, but `Irr G` is a *type*, not
  a `Finset (ClassFunction G)` — so a dedicated literal-token notation would have to coexist
  with the generic single-argument notation `Z[S]` at the same leading token `Z[`, risking
  parser ambiguity for no real benefit. The plain definition `ClassFunction.virtualCharIrr G`
  is used instead, and is what all the norm lemmas and the `IsChar` interaction lemmas are
  stated in terms of (via the `IsVirtualChar` predicate, proved equivalent to membership).
* **`vchar_norm2`, two shapes.** Writing `φ = ∑ χ, (c χ : ℂ) • χ` with `c : Irr G → ℤ`,
  orthonormality gives `⟪φ, φ⟫ = ∑ χ, (c χ)^2` (a real, in fact integer, quantity);
  `⟪φ, φ⟫ = 2` forces exactly two indices `χ₁ ≠ χ₂` with `c χ₁, c χ₂ ∈ {1, -1}` and all
  other coefficients `0` (`card_filter_ne_zero_eq_of_sum_sq_eq`, the shared counting
  argument behind both norm lemmas), i.e. `φ = ε₁ • χ₁ + ε₂ • χ₂` with signs `ε₁, ε₂ = ±1`
  (`exists_sign_smul_add_of_cfInner_self_eq_two`). Which extra hypothesis is added on top
  determines which conclusion is honest:
  - `⟪φ, 1⟫ = 0` (orthogonality to the trivial character) pins down only that neither `χ₁`
    nor `χ₂` is trivial (that inner product is the coefficient of `1` in the basis
    expansion) — it does *not* exclude the same-sign patterns `φ = ±(χ₁ + χ₂)`
    (e.g. `φ = χ₁ + χ₂` for two distinct nonprincipal irreducibles satisfies both
    hypotheses), so `exists_sub_or_add_of_cfInner_self_eq_two` lists all four patterns.
  - `φ 1 = 0` (vanishing at the identity — the `'Z[irr G, G^#]` support condition every
    actual Peterfalvi call site supplies: PFsection1.v:152–153, 217, 233;
    PFsection5.v:1597) *does* kill the same-sign patterns, because evaluating at `1` gives
    `±(χ₁ 1 + χ₂ 1)` there and irreducible degrees are positive naturals
    (`Irr.exists_degree`). This is `exists_sub_of_cfInner_self_eq_two`, concluding the pure
    difference `φ = χ₁ - χ₂` that MathComp's `vchar_norm2` produces and the PF sections
    consume.
-/

noncomputable section

open Finset LinearMap Module
open scoped ClassFunction

universe u

variable {G : Type u} [Group G]

/-! ### The virtual-character lattice `Z[S, A]` (MathComp: `'Z[S, A]`) -/

namespace ClassFunction

/-- Membership in the `ℤ`-span of a finite set `S`, spelled with the `ℂ`-smul convention used
throughout this file (`(c ψ : ℂ) • ψ`) rather than the canonical `ℤ`-smul that
`Submodule.span ℤ` itself uses — bridged by `Int.cast_smul_eq_zsmul`. Kept private: only the
bundled `VirtualChar`/`mem_virtualChar_iff` API is exported. -/
private theorem mem_span_iff {S : Finset (ClassFunction G)} {φ : ClassFunction G} :
    φ ∈ Submodule.span ℤ (S : Set (ClassFunction G)) ↔
      ∃ c : ClassFunction G → ℤ, φ = ∑ ψ ∈ S, (c ψ : ℂ) • ψ := by
  constructor
  · intro h
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp h
    refine ⟨f, hf.symm.trans (Finset.sum_congr rfl fun ψ _ => ?_)⟩
    exact (Int.cast_smul_eq_zsmul ℂ (f ψ) ψ).symm
  · rintro ⟨c, rfl⟩
    refine Submodule.sum_mem _ fun ψ hψ => ?_
    rw [Int.cast_smul_eq_zsmul ℂ (c ψ) ψ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hψ)

/-- The **virtual-character lattice** `Z[S, A]` (MathComp: `'Z[S, A]`): the `ℤ`-linear
combinations of the finite family `S` of class functions that are supported on `A`. Bundled
as an `AddSubgroup` (the meet of the `ℤ`-span of `S`, viewed as an `AddSubgroup` via the
canonical `ℤ`-module structure every `AddCommGroup` carries, with the `ℂ`-submodule
`supportedOn G A`, also viewed as an `AddSubgroup`). MathComp: `zchar S A` (name confirmed by
usage in the PF sections, e.g. `mem_zchar`/`zchar_split` at PFsection1.v:208), notation
`'Z[S, A]`. -/
def VirtualChar (S : Finset (ClassFunction G)) (A : Set G) : AddSubgroup (ClassFunction G) :=
  (Submodule.span ℤ (S : Set (ClassFunction G))).toAddSubgroup ⊓
    (ClassFunction.supportedOn G A).toAddSubgroup

@[inherit_doc]
scoped notation "Z[" S ", " A "]" => ClassFunction.VirtualChar S A

@[inherit_doc]
scoped notation "Z[" S "]" => ClassFunction.VirtualChar S Set.univ

/-- Membership in `Z[S, A]` (MathComp: `'Z[S, A]`): an explicit `ℤ`-linear combination of `S`,
supported on `A`. MathComp: `zchar_split` (the span/support split of `'Z[S, A]`; usage
PFsection1.v:208). -/
theorem mem_virtualChar_iff {S : Finset (ClassFunction G)} {A : Set G} {φ : ClassFunction G} :
    φ ∈ Z[S, A] ↔
      (∃ c : ClassFunction G → ℤ, φ = ∑ ψ ∈ S, (c ψ : ℂ) • ψ) ∧ ∀ g ∉ A, φ g = 0 := by
  rw [VirtualChar, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup,
    mem_span_iff, ClassFunction.mem_supportedOn]

theorem mem_virtualChar_univ_iff {S : Finset (ClassFunction G)} {φ : ClassFunction G} :
    φ ∈ Z[S] ↔ ∃ c : ClassFunction G → ℤ, φ = ∑ ψ ∈ S, (c ψ : ℂ) • ψ := by
  rw [show (Z[S] : AddSubgroup (ClassFunction G)) = Z[S, Set.univ] from rfl,
    mem_virtualChar_iff]
  simp

end ClassFunction

/-! ### The `Irr`-indexed special case (MathComp: `'Z[irr G]`) -/

section VirtualCharIrr

variable {G : Type u} [Group G] [Fintype G]

open scoped Classical in
variable (G) in
/-- The `Irr G`-indexed virtual-character lattice, spelled as a plain definition (see the
module design note for why no bracket notation is introduced for it): the `VirtualChar` of the
image of `Irr G` under its coercion to `ClassFunction G`, unrestricted in support. MathComp:
`'Z[irr G]`. -/
noncomputable def ClassFunction.virtualCharIrr : AddSubgroup (ClassFunction G) :=
  ClassFunction.VirtualChar (Finset.univ.image fun χ : Irr G => (χ : ClassFunction G)) Set.univ

/-- A class function is a **virtual character** if it is a `ℤ`-combination of the irreducible
characters — the `ℤ`-coefficient analogue of `ClassFunction.IsChar`. Proved equivalent to
membership in `ClassFunction.virtualCharIrr G`
(`ClassFunction.isVirtualChar_iff_mem_virtualCharIrr`). -/
def ClassFunction.IsVirtualChar (φ : ClassFunction G) : Prop :=
  ∃ c : Irr G → ℤ, φ = ∑ χ : Irr G, (c χ : ℂ) • (χ : ClassFunction G)

open scoped Classical in
theorem ClassFunction.isVirtualChar_iff_mem_virtualCharIrr {φ : ClassFunction G} :
    φ.IsVirtualChar ↔ φ ∈ ClassFunction.virtualCharIrr G := by
  have hinj : Set.InjOn (fun χ : Irr G => (χ : ClassFunction G)) (Finset.univ : Finset (Irr G)) :=
    Irr.toClassFunction_injective.injOn
  simp only [ClassFunction.virtualCharIrr, ClassFunction.mem_virtualChar_univ_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun ψ => if h : ∃ χ : Irr G, (χ : ClassFunction G) = ψ then c h.choose else 0, ?_⟩
    rw [Finset.sum_image hinj, hc]
    refine Finset.sum_congr rfl fun χ _ => ?_
    dsimp only
    have hex : ∃ ψ : Irr G, (ψ : ClassFunction G) = (χ : ClassFunction G) := ⟨χ, rfl⟩
    rw [dif_pos hex, Irr.toClassFunction_injective hex.choose_spec]
  · rintro ⟨c, hc⟩
    rw [Finset.sum_image hinj] at hc
    exact ⟨fun χ => c (χ : ClassFunction G), hc⟩

/-- Virtual characters are closed under addition (one line through the bundled
`AddSubgroup`). MathComp: the generic `rpredD` applied to `zchar`. -/
theorem ClassFunction.IsVirtualChar.add {φ ψ : ClassFunction G} (hφ : φ.IsVirtualChar)
    (hψ : ψ.IsVirtualChar) : (φ + ψ).IsVirtualChar :=
  ClassFunction.isVirtualChar_iff_mem_virtualCharIrr.mpr
    (add_mem (ClassFunction.isVirtualChar_iff_mem_virtualCharIrr.mp hφ)
      (ClassFunction.isVirtualChar_iff_mem_virtualCharIrr.mp hψ))

/-- Virtual characters are closed under negation. MathComp: `rpredN` applied to `zchar`. -/
theorem ClassFunction.IsVirtualChar.neg {φ : ClassFunction G} (hφ : φ.IsVirtualChar) :
    (-φ).IsVirtualChar :=
  ClassFunction.isVirtualChar_iff_mem_virtualCharIrr.mpr
    (neg_mem (ClassFunction.isVirtualChar_iff_mem_virtualCharIrr.mp hφ))

/-- Virtual characters are closed under subtraction. MathComp: `rpredB` applied to `zchar`
(usage e.g. PFsection1.v:208). -/
theorem ClassFunction.IsVirtualChar.sub {φ ψ : ClassFunction G} (hφ : φ.IsVirtualChar)
    (hψ : ψ.IsVirtualChar) : (φ - ψ).IsVirtualChar :=
  ClassFunction.isVirtualChar_iff_mem_virtualCharIrr.mpr
    (sub_mem (ClassFunction.isVirtualChar_iff_mem_virtualCharIrr.mp hφ)
      (ClassFunction.isVirtualChar_iff_mem_virtualCharIrr.mp hψ))

/-- The coefficient of `χ` in a virtual character `φ` (as computed from a fixed witness
`c` of `φ.IsVirtualChar`) agrees with the inner product `⟪φ, χ⟫_[G]`: the direct analogue of
`CharacterArith.lean`'s coefficient computation for `IsChar`, with `ℤ` in place of `ℕ`. -/
theorem ClassFunction.cfInner_eq_of_eq_sum_intCast_smul {φ : ClassFunction G} {c : Irr G → ℤ}
    (hc : φ = ∑ χ : Irr G, (c χ : ℂ) • (χ : ClassFunction G)) (ψ : Irr G) :
    ⟪φ, (ψ : ClassFunction G)⟫_[G] = (c ψ : ℂ) := by
  classical
  rw [hc, ClassFunction.cfInner_sum_left]
  have hterm : ∀ χ : Irr G,
      ⟪(c χ : ℂ) • (χ : ClassFunction G), (ψ : ClassFunction G)⟫_[G] =
        if χ = ψ then (c χ : ℂ) else 0 := by
    intro χ
    rw [ClassFunction.cfInner_smul_left, Irr.cfInner_eq, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl fun χ _ => hterm χ,
    Finset.sum_ite_eq' Finset.univ ψ fun χ => (c χ : ℂ)]
  simp

/-- The multiplicity of an irreducible character `ψ` in a virtual character `φ` is an integer
(realized as the inner product `⟪φ, ψ⟫`). MathComp: the integrality half of `zchar_expansion`
(exact statement unconfirmed). -/
theorem ClassFunction.IsVirtualChar.cfInner_mem_intCast {φ : ClassFunction G}
    (hφ : φ.IsVirtualChar) (ψ : Irr G) : ∃ n : ℤ, ⟪φ, (ψ : ClassFunction G)⟫_[G] = (n : ℂ) := by
  obtain ⟨c, hc⟩ := hφ
  exact ⟨c ψ, ClassFunction.cfInner_eq_of_eq_sum_intCast_smul hc ψ⟩

end VirtualCharIrr

/-! ### `IsChar` implies `IsVirtualChar` -/

section IsCharToVirtual

variable {G : Type u} [Group G] [Fintype G]

theorem ClassFunction.IsChar.isVirtualChar {φ : ClassFunction G} (hφ : φ.IsChar) :
    φ.IsVirtualChar := by
  obtain ⟨c, hc⟩ := hφ
  refine ⟨fun χ => (c χ : ℤ), ?_⟩
  rw [hc]
  refine Finset.sum_congr rfl fun χ _ => ?_
  norm_cast

theorem ClassFunction.IsChar.mem_virtualCharIrr {φ : ClassFunction G} (hφ : φ.IsChar) :
    φ ∈ ClassFunction.virtualCharIrr G :=
  ClassFunction.isVirtualChar_iff_mem_virtualCharIrr.mp hφ.isVirtualChar

end IsCharToVirtual

/-! ### The norm lemmas

The shared engine: if the integer coefficients `c : Irr G → ℤ` of a virtual character satisfy
`∑ χ, (c χ)^2 = n` for a small literal `n ≤ 2`, then every nonzero `c χ` is `±1`, and there are
exactly `n` nonzero coefficients. Applying this with `n = 1` gives `vchar_norm1`; with `n = 2`,
`vchar_norm2`. -/

section NormLemmas

variable {G : Type u} [Group G] [Fintype G]

open scoped Classical in
/-- If the integer coefficients `c : Irr G → ℤ` satisfy `∑ χ, (c χ)^2 = n` for a small literal
`n ≤ 2`, then every nonzero coefficient is `±1`, and there are exactly `n` nonzero ones. The
shared combinatorial core of the norm-1 and norm-2 classification lemmas; public so that
future PF-section work (small-norm decompositions, isometry bases à la
`vchar_isometry_base3`, PFsection1.v:144) can reuse it directly. -/
theorem ClassFunction.card_filter_ne_zero_eq_of_sum_sq_eq (c : Irr G → ℤ) (n : ℕ) (hn : n ≤ 2)
    (hsum : ∑ χ : Irr G, (c χ) ^ 2 = (n : ℤ)) :
    (Finset.univ.filter fun χ : Irr G => c χ ≠ 0).card = n ∧
      ∀ χ : Irr G, c χ ≠ 0 → c χ = 1 ∨ c χ = -1 := by
  have hbound : ∀ χ : Irr G, (c χ) ^ 2 ≤ (n : ℤ) := fun χ =>
    (Finset.single_le_sum (fun χ _ => sq_nonneg (c χ)) (Finset.mem_univ χ)).trans_eq hsum
  have hn2 : (n : ℤ) ≤ 2 := by exact_mod_cast hn
  have hsign : ∀ χ : Irr G, c χ ≠ 0 → c χ = 1 ∨ c χ = -1 := by
    intro χ hχ
    have hb2 : (c χ) ^ 2 ≤ 2 := (hbound χ).trans hn2
    have h1 : 4 * c χ ≤ 6 := by nlinarith [sq_nonneg (c χ - 2)]
    have h2 : -6 ≤ 4 * c χ := by nlinarith [sq_nonneg (c χ + 2)]
    omega
  refine ⟨?_, hsign⟩
  have hval : ∀ χ : Irr G, (c χ) ^ 2 = if c χ ≠ 0 then (1 : ℤ) else 0 := by
    intro χ
    by_cases hχ : c χ = 0
    · simp [hχ]
    · rw [if_pos hχ]
      rcases hsign χ hχ with h | h <;> rw [h] <;> ring
  have hsum2 : ∑ χ : Irr G, (if c χ ≠ 0 then (1 : ℤ) else 0) = (n : ℤ) := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun χ _ => (hval χ).symm
  rw [Finset.sum_boole] at hsum2
  exact_mod_cast hsum2

/-- The `Irr`-basis coefficients of a virtual character `φ` satisfy `∑ χ, (c χ)^2 = ⟪φ, φ⟫`
(as an integer cast into `ℂ`), via orthonormality of `Irr G`. The bridge feeding a norm
hypothesis `⟪φ, φ⟫ = n` into `card_filter_ne_zero_eq_of_sum_sq_eq`; public for the same
future PF-section reuse. -/
theorem ClassFunction.sum_sq_coeff_eq_cfInner_self {φ : ClassFunction G} {c : Irr G → ℤ}
    (hc : φ = ∑ χ : Irr G, (c χ : ℂ) • (χ : ClassFunction G)) :
    ((∑ χ : Irr G, (c χ) ^ 2 : ℤ) : ℂ) = ⟪φ, φ⟫_[G] := by
  have hexpand : ⟪φ, φ⟫_[G] = ∑ χ : Irr G, (c χ : ℂ) ^ 2 := by
    nth_rewrite 2 [hc]
    rw [ClassFunction.cfInner_sum_right]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [ClassFunction.cfInner_smul_right, map_intCast,
      ClassFunction.cfInner_eq_of_eq_sum_intCast_smul hc χ]
    ring
  rw [hexpand]
  push_cast
  ring

open scoped Classical in
/-- **`vchar_norm1`**: a virtual character of norm `1` is `±` an irreducible character.
MathComp: `vchar_norm1P`. -/
theorem ClassFunction.IsVirtualChar.exists_eq_or_eq_neg_of_cfInner_self_eq_one
    {φ : ClassFunction G} (hφ : φ.IsVirtualChar) (hnorm : ⟪φ, φ⟫_[G] = 1) :
    (∃ χ : Irr G, φ = (χ : ClassFunction G)) ∨ (∃ χ : Irr G, φ = -(χ : ClassFunction G)) := by
  obtain ⟨c, hc⟩ := hφ
  have hsumZ : ∑ χ : Irr G, (c χ) ^ 2 = (1 : ℤ) := by
    have h := ClassFunction.sum_sq_coeff_eq_cfInner_self hc
    rw [hnorm] at h
    exact_mod_cast h
  obtain ⟨hcard, hsign⟩ :=
    ClassFunction.card_filter_ne_zero_eq_of_sum_sq_eq c 1 (by norm_num) hsumZ
  obtain ⟨χ₀, hχ₀⟩ := Finset.card_eq_one.mp hcard
  have hc0 : c χ₀ ≠ 0 :=
    (Finset.mem_filter.mp (hχ₀ ▸ Finset.mem_singleton_self χ₀ :
      χ₀ ∈ Finset.univ.filter fun χ : Irr G => c χ ≠ 0)).2
  have hrest : ∀ χ : Irr G, χ ≠ χ₀ → c χ = 0 := by
    intro χ hχ
    by_contra hcne
    have hmem : χ ∈ Finset.univ.filter fun χ : Irr G => c χ ≠ 0 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcne⟩
    rw [hχ₀] at hmem
    exact hχ (Finset.mem_singleton.mp hmem)
  have hphi : φ = (c χ₀ : ℂ) • (χ₀ : ClassFunction G) := by
    rw [hc]
    refine Finset.sum_eq_single χ₀ (fun χ _ hχ => ?_) (fun h => absurd (Finset.mem_univ χ₀) h)
    rw [hrest χ hχ]
    simp
  rcases hsign χ₀ hc0 with h1 | h1
  · exact Or.inl ⟨χ₀, by rw [hphi, h1]; simp⟩
  · exact Or.inr ⟨χ₀, by rw [hphi, h1]; simp⟩

open scoped Classical in
/-- **Norm-2 decomposition engine**: a virtual character of norm `2` is `ε₁ • χ₁ + ε₂ • χ₂`
for two *distinct* irreducible characters `χ₁ ≠ χ₂` and integer signs `ε₁, ε₂ ∈ {1, -1}`.
Both `vchar_norm2` shapes — the four-pattern variant under `⟪φ, 1⟫ = 0` and the PF-shaped
difference variant under `φ 1 = 0` — are read off from this. -/
theorem ClassFunction.IsVirtualChar.exists_sign_smul_add_of_cfInner_self_eq_two
    {φ : ClassFunction G} (hφ : φ.IsVirtualChar) (hnorm : ⟪φ, φ⟫_[G] = 2) :
    ∃ χ₁ χ₂ : Irr G, χ₁ ≠ χ₂ ∧ ∃ ε₁ ε₂ : ℤ, (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧
      φ = (ε₁ : ℂ) • (χ₁ : ClassFunction G) + (ε₂ : ℂ) • (χ₂ : ClassFunction G) := by
  obtain ⟨c, hc⟩ := hφ
  have hsumZ : ∑ χ : Irr G, (c χ) ^ 2 = (2 : ℤ) := by
    have h := ClassFunction.sum_sq_coeff_eq_cfInner_self hc
    rw [hnorm] at h
    exact_mod_cast h
  obtain ⟨hcard, hsign⟩ :=
    ClassFunction.card_filter_ne_zero_eq_of_sum_sq_eq c 2 (by norm_num) hsumZ
  obtain ⟨χ₁, χ₂, hne, hpair⟩ := Finset.card_eq_two.mp hcard
  have hmem : ∀ χ : Irr G, χ ∈ ({χ₁, χ₂} : Finset (Irr G)) ↔ χ = χ₁ ∨ χ = χ₂ := by
    intro χ; simp
  have hc1 : c χ₁ ≠ 0 :=
    (Finset.mem_filter.mp (hpair ▸ (hmem χ₁).mpr (Or.inl rfl) :
      χ₁ ∈ Finset.univ.filter fun χ : Irr G => c χ ≠ 0)).2
  have hc2 : c χ₂ ≠ 0 :=
    (Finset.mem_filter.mp (hpair ▸ (hmem χ₂).mpr (Or.inr rfl) :
      χ₂ ∈ Finset.univ.filter fun χ : Irr G => c χ ≠ 0)).2
  have hrest : ∀ χ : Irr G, χ ≠ χ₁ → χ ≠ χ₂ → c χ = 0 := by
    intro χ h1 h2
    by_contra hcne
    have hm : χ ∈ Finset.univ.filter fun χ : Irr G => c χ ≠ 0 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcne⟩
    rw [hpair, hmem] at hm
    rcases hm with h | h
    · exact h1 h
    · exact h2 h
  have hphi : φ = (c χ₁ : ℂ) • (χ₁ : ClassFunction G) + (c χ₂ : ℂ) • (χ₂ : ClassFunction G) := by
    rw [hc]
    have hsub :
        ∑ χ ∈ ({χ₁, χ₂} : Finset (Irr G)), (c χ : ℂ) • (χ : ClassFunction G) =
          ∑ χ : Irr G, (c χ : ℂ) • (χ : ClassFunction G) := by
      refine Finset.sum_subset (Finset.subset_univ _) fun χ _ hχ => ?_
      have : c χ = 0 := by
        by_cases hx1 : χ = χ₁
        · exact absurd ((hmem χ).mpr (Or.inl hx1)) hχ
        by_cases hx2 : χ = χ₂
        · exact absurd ((hmem χ).mpr (Or.inr hx2)) hχ
        exact hrest χ hx1 hx2
      rw [this]; simp
    rw [← hsub, Finset.sum_pair hne]
  exact ⟨χ₁, χ₂, hne, c χ₁, c χ₂, hsign χ₁ hc1, hsign χ₂ hc2, hphi⟩

/-- **`vchar_norm2`, four-pattern variant**: a virtual character of norm `2`, orthogonal to
the trivial character, is one of `χ₁ - χ₂`, `χ₂ - χ₁`, `χ₁ + χ₂`, `-(χ₁ + χ₂)` for two
distinct nonprincipal irreducible characters `χ₁, χ₂`. See the module design note for why all
four sign patterns are honestly needed under these hypotheses (the orthogonality-to-`1`
hypothesis only excludes `1` from being one of the two constituents; it does not fix the
relative sign — for that, use the PF-shaped `exists_sub_of_cfInner_self_eq_two`). -/
theorem ClassFunction.IsVirtualChar.exists_sub_or_add_of_cfInner_self_eq_two
    {φ : ClassFunction G} (hφ : φ.IsVirtualChar) (hnorm : ⟪φ, φ⟫_[G] = 2)
    (horth : ⟪φ, ((Irr.one : Irr G) : ClassFunction G)⟫_[G] = 0) :
    ∃ χ₁ χ₂ : Irr G, χ₁ ≠ χ₂ ∧ χ₁ ≠ (Irr.one : Irr G) ∧ χ₂ ≠ (Irr.one : Irr G) ∧
      (φ = (χ₁ : ClassFunction G) - (χ₂ : ClassFunction G) ∨
        φ = (χ₂ : ClassFunction G) - (χ₁ : ClassFunction G) ∨
        φ = (χ₁ : ClassFunction G) + (χ₂ : ClassFunction G) ∨
        φ = -((χ₁ : ClassFunction G) + (χ₂ : ClassFunction G))) := by
  classical
  obtain ⟨χ₁, χ₂, hne, ε₁, ε₂, hε₁, hε₂, hphi⟩ :=
    hφ.exists_sign_smul_add_of_cfInner_self_eq_two hnorm
  have hcoeff : ∀ ψ : Irr G, ⟪φ, (ψ : ClassFunction G)⟫_[G]
      = (ε₁ : ℂ) * (if χ₁ = ψ then 1 else 0) + (ε₂ : ℂ) * (if χ₂ = ψ then 1 else 0) := by
    intro ψ
    rw [hphi, ClassFunction.cfInner_add_left, ClassFunction.cfInner_smul_left,
      ClassFunction.cfInner_smul_left, Irr.cfInner_eq, Irr.cfInner_eq]
  have hε₁0 : (ε₁ : ℂ) ≠ 0 := by rcases hε₁ with h | h <;> rw [h] <;> norm_num
  have hε₂0 : (ε₂ : ℂ) ≠ 0 := by rcases hε₂ with h | h <;> rw [h] <;> norm_num
  have hχ1ne : χ₁ ≠ (Irr.one : Irr G) := by
    rintro rfl
    have h := hcoeff (Irr.one : Irr G)
    rw [horth, if_pos rfl, if_neg hne.symm, mul_one, mul_zero, add_zero] at h
    exact hε₁0 h.symm
  have hχ2ne : χ₂ ≠ (Irr.one : Irr G) := by
    rintro rfl
    have h := hcoeff (Irr.one : Irr G)
    rw [horth, if_neg hne, if_pos rfl, mul_zero, mul_one, zero_add] at h
    exact hε₂0 h.symm
  refine ⟨χ₁, χ₂, hne, hχ1ne, hχ2ne, ?_⟩
  rcases hε₁ with h1 | h1 <;> rcases hε₂ with h2 | h2
  · exact Or.inr (Or.inr (Or.inl (by rw [hphi, h1, h2]; simp)))
  · exact Or.inl (by rw [hphi, h1, h2]; simp; ring)
  · exact Or.inr (Or.inl (by rw [hphi, h1, h2]; simp; ring))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [hphi, h1, h2]
    simp
    ring

/-- **`vchar_norm2`, PF call-site shape**: a virtual character of norm `2` *vanishing at `1`*
is a pure difference `χ₁ - χ₂` of two distinct irreducible characters. This is the exact
shape consumed at every Peterfalvi call site of MathComp's `vchar_norm2` (PFsection1.v:152–153,
217, 233; PFsection5.v:1597 — the argument is always in `'Z[irr G, G^#]`, i.e. supported off
`1`): evaluating the sign decomposition at `1` kills the same-sign patterns, because
irreducible degrees are positive naturals (`Irr.exists_degree`). MathComp: `vchar_norm2`. -/
theorem ClassFunction.IsVirtualChar.exists_sub_of_cfInner_self_eq_two
    {φ : ClassFunction G} (hφ : φ.IsVirtualChar) (hnorm : ⟪φ, φ⟫_[G] = 2)
    (hone : φ 1 = 0) :
    ∃ χ₁ χ₂ : Irr G, χ₁ ≠ χ₂ ∧ φ = (χ₁ : ClassFunction G) - (χ₂ : ClassFunction G) := by
  obtain ⟨χ₁, χ₂, hne, ε₁, ε₂, hε₁, hε₂, hphi⟩ :=
    hφ.exists_sign_smul_add_of_cfInner_self_eq_two hnorm
  obtain ⟨d₁, hd₁pos, hd₁⟩ := χ₁.exists_degree
  obtain ⟨d₂, -, hd₂⟩ := χ₂.exists_degree
  have happ : (ε₁ : ℂ) * (d₁ : ℂ) + (ε₂ : ℂ) * (d₂ : ℂ) = 0 := by
    have h := congrArg (fun ψ : ClassFunction G => ψ 1) hphi
    simp only [ClassFunction.add_apply, ClassFunction.smul_apply, smul_eq_mul,
      Irr.coe_apply] at h
    rw [hone, hd₁, hd₂] at h
    exact h.symm
  rcases hε₁ with h1 | h1 <;> rcases hε₂ with h2 | h2 <;> rw [h1, h2] at happ
  · -- both signs `+1`: impossible, the degrees would sum to zero
    exfalso
    have hnat : ((d₁ + d₂ : ℕ) : ℂ) = 0 := by push_cast; linear_combination happ
    have : d₁ + d₂ = 0 := by exact_mod_cast hnat
    omega
  · exact ⟨χ₁, χ₂, hne, by rw [hphi, h1, h2]; simp; ring⟩
  · exact ⟨χ₂, χ₁, hne.symm, by rw [hphi, h1, h2]; simp; ring⟩
  · -- both signs `-1`: impossible, the degrees would sum to zero
    exfalso
    have hnat : ((d₁ + d₂ : ℕ) : ℂ) = 0 := by push_cast; linear_combination -happ
    have : d₁ + d₂ = 0 := by exact_mod_cast hnat
    omega

end NormLemmas

/-! ### `IsChar`/`IsVirtualChar` interaction: nonnegativity and the sign split -/

section IsCharInteraction

variable {G : Type u} [Group G] [Fintype G]

/-- **Nonnegativity criterion**: a virtual character all of whose `Irr`-basis coefficients
`⟪φ, χ⟫_[G]` have nonnegative real part is a character. The coefficients are *integers* by
virtue of `φ.IsVirtualChar` (`cfInner_eq_of_eq_sum_intCast_smul`), so nonnegativity of the
real part upgrades them to natural numbers, which is exactly an `IsChar` witness. -/
theorem ClassFunction.IsVirtualChar.isChar_of_forall_cfInner_nonneg {φ : ClassFunction G}
    (hφ : φ.IsVirtualChar)
    (hpos : ∀ χ : Irr G, 0 ≤ (⟪φ, (χ : ClassFunction G)⟫_[G]).re) : φ.IsChar := by
  obtain ⟨c, hc⟩ := hφ
  have hnn : ∀ χ : Irr G, 0 ≤ c χ := by
    intro χ
    have h := hpos χ
    rw [ClassFunction.cfInner_eq_of_eq_sum_intCast_smul hc χ] at h
    exact_mod_cast (by simpa using h : (0 : ℝ) ≤ (c χ : ℝ))
  refine ⟨fun χ => (c χ).toNat, ?_⟩
  rw [hc]
  refine Finset.sum_congr rfl fun χ _ => ?_
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg (hnn χ)).symm

/-- Every virtual character splits as a difference of two characters: split the integer
coefficients `c χ` into their positive part `n⁺ χ := (c χ).toNat` and negative part
`n⁻ χ := (-c χ).toNat`, both natural numbers, with `c χ = n⁺ χ - n⁻ χ`. MathComp: the
forward direction of `vcharP` (usage PFsection1.v:639). -/
theorem ClassFunction.IsVirtualChar.exists_isChar_sub {φ : ClassFunction G}
    (hφ : φ.IsVirtualChar) :
    ∃ φ₁ φ₂ : ClassFunction G, φ₁.IsChar ∧ φ₂.IsChar ∧ φ = φ₁ - φ₂ := by
  obtain ⟨c, hc⟩ := hφ
  refine ⟨∑ χ : Irr G, ((c χ).toNat : ℂ) • (χ : ClassFunction G),
    ∑ χ : Irr G, (((-c χ)).toNat : ℂ) • (χ : ClassFunction G),
    ⟨fun χ => (c χ).toNat, rfl⟩, ⟨fun χ => (-c χ).toNat, rfl⟩, ?_⟩
  rw [hc, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun χ _ => ?_
  have hz : (c χ : ℤ) = ((c χ).toNat : ℤ) - (((-c χ).toNat : ℤ)) := by omega
  have : (c χ : ℂ) = ((c χ).toNat : ℂ) - (((-c χ).toNat : ℂ)) := by exact_mod_cast hz
  rw [this, sub_smul]

/-- A difference of two characters is a virtual character: the (trivial) converse of
`exists_isChar_sub`. MathComp: the easy direction of `vcharP`. -/
theorem ClassFunction.IsChar.sub_isVirtualChar {φ₁ φ₂ : ClassFunction G}
    (h₁ : φ₁.IsChar) (h₂ : φ₂.IsChar) : (φ₁ - φ₂).IsVirtualChar :=
  h₁.isVirtualChar.sub h₂.isVirtualChar

/-- **`vcharP` shape** (MathComp `vcharP`, usage verified at PFsection1.v:639): a class
function is a virtual character iff it is a difference of two characters. -/
theorem ClassFunction.isVirtualChar_iff_exists_isChar_sub {φ : ClassFunction G} :
    φ.IsVirtualChar ↔
      ∃ φ₁ φ₂ : ClassFunction G, φ₁.IsChar ∧ φ₂.IsChar ∧ φ = φ₁ - φ₂ := by
  refine ⟨fun hφ => hφ.exists_isChar_sub, ?_⟩
  rintro ⟨φ₁, φ₂, h₁, h₂, rfl⟩
  exact h₁.sub_isVirtualChar h₂

open scoped Classical in
/-- **`zcharD1E` bridge**: membership in `'Z[irr G, G^#]` (the virtual characters supported
off the identity) is exactly being a virtual character that vanishes at `1`.  MathComp:
`zcharD1E` (`vcharacter.v`). -/
theorem ClassFunction.mem_virtualChar_irr_compl_one_iff {φ : ClassFunction G} :
    φ ∈ Z[Finset.univ.image (fun χ : Irr G => (χ : ClassFunction G)), ({1}ᶜ : Set G)] ↔
      φ.IsVirtualChar ∧ φ 1 = 0 := by
  rw [ClassFunction.mem_virtualChar_iff]
  refine and_congr ?_ ?_
  · rw [ClassFunction.isVirtualChar_iff_mem_virtualCharIrr]
    simp only [ClassFunction.virtualCharIrr, ClassFunction.mem_virtualChar_univ_iff]
  · rw [← ClassFunction.mem_supportedOn (A := ({1}ᶜ : Set G)),
      ClassFunction.mem_supportedOn_compl_one]

end IsCharInteraction
