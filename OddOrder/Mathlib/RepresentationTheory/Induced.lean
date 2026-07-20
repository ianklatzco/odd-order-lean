/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import OddOrder.Mathlib.RepresentationTheory.CharacterArith

/-!
# Restriction, induction, and Frobenius reciprocity for class functions

This file is Task 2 of the M2 character-theory plan: restriction of a class function on `G`
to a subgroup `H` (MathComp `cfRes`, `'Res[H] φ`), induction of a class function on `H` up to
`G` by the averaging formula (MathComp `cfInd`, `'Ind[G] φ`), and Frobenius reciprocity
(MathComp `cfdot_cfInd` / `Frobenius_reciprocity`). It also proves that restriction and
induction preserve the character predicate `ClassFunction.IsChar` from
`CharacterArith.lean`.

## Main definitions

* `ClassFunction.res (H : Subgroup G) : ClassFunction G →ₗ[ℂ] ClassFunction H`: restriction.
  MathComp: `cfRes`.
* `ClassFunction.ind (H : Subgroup G) : ClassFunction H →ₗ[ℂ] ClassFunction G`: induction, by
  the averaging formula `ind H φ g = (#H)⁻¹ * ∑ x : G, φ' (x⁻¹ * g * x)`, where `φ'` extends
  `φ` by zero off `H`. MathComp: `cfInd`.

## Main results

* `ClassFunction.ind_apply_one : ind H φ 1 = (H.index : ℂ) * φ 1`. MathComp: (evaluated from
  `cfInd1`-shaped facts).
* `ClassFunction.cfInner_ind_eq_cfInner_res`: **Frobenius reciprocity**,
  `⟪ind H φ, ψ⟫_[G] = ⟪φ, res H ψ⟫_[H]`. MathComp: `cfdot_cfInd` / `Frobenius_reciprocity`.
* `ClassFunction.IsChar.res`: restriction of a character is a character. MathComp-shaped
  `cfRes_char`.
* `ClassFunction.IsChar.ind`: induction of a character is a character, proved *via*
  Frobenius reciprocity (not via representation constructions), following the plan's route.
  MathComp-shaped `cfInd_char`.

## Design notes

* **Not a duplicate of Mathlib's categorical induction.** Mathlib's
  `Mathlib/RepresentationTheory/Induced.lean` constructs induction of *representations*
  (`Representation.ind` along a group hom, with the `ind ⊣ res` adjunction
  `Rep.indResAdjunction`); it has no class-function-level induction formula, no induced
  *character* identity, and no `cfdot`-style Frobenius reciprocity for inner products of
  class functions — which are exactly what this file provides (and what the PF sections
  consume), so the two developments do not overlap.
* **Fintype seam.** Following the M2 plan's Fintype/`Nat.card` policy, statements summing over
  `G` take `[Fintype G]`, and statements involving the inner product on `H` (which sums over
  `↥H`) take `[Fintype H]` as an explicit hypothesis rather than manufacturing it internally.
* **`IsChar.res` route.** Restriction is implemented at the `Representation` level: for
  `χ : Irr G` witnessed by a simple `ℂ[G]`-submodule `N` of the regular module, restrict the
  representation `Representation.ofModule' N` along `H.subtype : H →* G` (plain `MonoidHom`
  composition, since `Representation` is a `MonoidHom`), then transport its character back to
  a `ℂ[H]`-module character via `Representation.asModule` (undoing `ofModule'`), landing back
  in `CharacterArith.lean`'s `isChar_moduleCharacter'`. This is the fallback route flagged in
  the plan's Risk 2 (avoiding `MonoidAlgebra` functoriality along `Subgroup.subtype`, whose
  exact Mathlib name for the induced ring/algebra hom was not needed after all).
* **`IsChar.ind` route.** Exactly the plan's route: expand `ind H φ` in the basis `Irr.basis`
  (`ClassFunction.eq_sum_cfInner_smul`); each coefficient `⟪ind H φ, χ⟫_[G]` rewrites via
  Frobenius reciprocity to `⟪φ, res H χ⟫_[H]`, which is a natural number because both `φ` and
  `res H χ` are characters of `H` (`ClassFunction.IsChar.cfInner_mem_nat'`, a two-sided version
  of `CharacterArith.lean`'s `IsChar.cfInner_mem_nat` proved here since Task 2 is the first
  consumer).
-/

noncomputable section

open Finset LinearMap Module
open scoped ClassFunction

universe u

variable {G : Type u} [Group G]

/-! ### Restriction -/

namespace ClassFunction

variable (H : Subgroup G)

/-- Restriction of a class function on `G` to a subgroup `H`: conjugation in `H` is
conjugation in `G`, so a class function on `G` restricts to one on `H`. MathComp: `cfRes`,
`'Res[H] φ`. -/
def res : ClassFunction G →ₗ[ℂ] ClassFunction H where
  toFun φ := ⟨fun h => φ (h : G), fun g h => by
    have hco : ((h * g * h⁻¹ : H) : G) = (h : G) * (g : G) * (h : G)⁻¹ := by
      simp [Subgroup.coe_mul]
    rw [hco, φ.conj_apply]⟩
  map_add' φ ψ := by ext h; simp
  map_smul' c φ := by ext h; simp

@[simp]
theorem res_apply (φ : ClassFunction G) (h : H) : res H φ h = φ (h : G) :=
  rfl

/-- Restriction sends the constant function `1` on `G` to the constant function `1` on `H`
(the `One` of `CharacterArith.lean`'s ring structure). -/
@[simp]
theorem res_one : res H (1 : ClassFunction G) = 1 :=
  rfl

end ClassFunction

/-! ### The zero-extension of a class function on `H` to `G` -/

namespace ClassFunction

variable {H : Subgroup G}

open scoped Classical in
/-- The zero-extension of a class function on `H` to a plain function on `G`: agrees with `φ`
on `H`, vanishes elsewhere. Used only to state the averaging formula for `ind`. -/
noncomputable def extendZero (φ : ClassFunction H) : G → ℂ :=
  fun g => if h : g ∈ H then φ ⟨g, h⟩ else 0

open scoped Classical in
theorem extendZero_apply_of_mem (φ : ClassFunction H) {g : G} (hg : g ∈ H) :
    extendZero φ g = φ ⟨g, hg⟩ :=
  dif_pos hg

open scoped Classical in
theorem extendZero_apply_of_not_mem (φ : ClassFunction H) {g : G} (hg : g ∉ H) :
    extendZero φ g = 0 :=
  dif_neg hg

theorem extendZero_add_apply (φ ψ : ClassFunction H) (g : G) :
    extendZero (φ + ψ) g = extendZero φ g + extendZero ψ g := by
  by_cases hg : g ∈ H
  · rw [extendZero_apply_of_mem _ hg, extendZero_apply_of_mem _ hg, extendZero_apply_of_mem _ hg,
      ClassFunction.add_apply]
  · rw [extendZero_apply_of_not_mem _ hg, extendZero_apply_of_not_mem _ hg,
      extendZero_apply_of_not_mem _ hg, add_zero]

theorem extendZero_smul_apply (c : ℂ) (φ : ClassFunction H) (g : G) :
    extendZero (c • φ) g = c * extendZero φ g := by
  by_cases hg : g ∈ H
  · rw [extendZero_apply_of_mem _ hg, extendZero_apply_of_mem _ hg, ClassFunction.smul_apply,
      smul_eq_mul]
  · rw [extendZero_apply_of_not_mem _ hg, extendZero_apply_of_not_mem _ hg, mul_zero]

end ClassFunction

/-! ### Induction -/

namespace ClassFunction

variable [Fintype G] (H : Subgroup G)

/-- Induction of a class function on `H` up to `G`, by the averaging formula
`ind H φ g = (#H)⁻¹ * ∑ x : G, φ' (x⁻¹ * g * x)`, where `φ'` extends `φ` by zero off `H`.
Well-definedness (conjugation-invariance in `g`) is a reindexing of the sum by left
multiplication; linearity in `φ` is immediate from `extendZero`'s linearity. MathComp: `cfInd`,
`'Ind[G] φ`. -/
def ind : ClassFunction H →ₗ[ℂ] ClassFunction G where
  toFun φ := ⟨fun g => (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendZero φ (x⁻¹ * g * x), by
    intro a b
    show (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendZero φ (x⁻¹ * (b * a * b⁻¹) * x)
        = (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendZero φ (x⁻¹ * a * x)
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft b⁻¹) _ _ fun x => ?_
    simp only [Equiv.coe_mulLeft]
    congr 1
    group⟩
  map_add' φ ψ := by
    ext g
    change (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendZero (φ + ψ) (x⁻¹ * g * x)
        = (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendZero φ (x⁻¹ * g * x)
          + (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendZero ψ (x⁻¹ * g * x)
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun x _ => extendZero_add_apply φ ψ _
  map_smul' c φ := by
    ext g
    change (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendZero (c • φ) (x⁻¹ * g * x)
        = c * ((Nat.card H : ℂ)⁻¹ * ∑ x : G, extendZero φ (x⁻¹ * g * x))
    rw [Finset.sum_congr rfl fun x _ => extendZero_smul_apply c φ (x⁻¹ * g * x), ← Finset.mul_sum]
    ring

theorem ind_apply (φ : ClassFunction H) (g : G) :
    ind H φ g = (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendZero φ (x⁻¹ * g * x) :=
  rfl

theorem ind_apply_one (φ : ClassFunction H) : ind H φ 1 = (H.index : ℂ) * φ 1 := by
  have h1 : ∀ x : G, extendZero φ (x⁻¹ * (1 : G) * x) = φ 1 := by
    intro x
    have hx1 : x⁻¹ * (1 : G) * x = 1 := by group
    rw [hx1, extendZero_apply_of_mem φ H.one_mem]
    exact congrArg φ (Subtype.ext rfl)
  rw [ind_apply, Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_const, card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul]
  have hidx : (H.index : ℂ) * (Nat.card H : ℂ) = (Nat.card G : ℂ) := by
    exact_mod_cast H.index_mul_card
  have hH0 : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcard : (Nat.card H : ℂ)⁻¹ * (Nat.card G : ℂ) = (H.index : ℂ) := by
    rw [← hidx, mul_comm (H.index : ℂ) (Nat.card H : ℂ), ← mul_assoc, inv_mul_cancel₀ hH0, one_mul]
  rw [← mul_assoc, hcard]

end ClassFunction

/-! ### Frobenius reciprocity -/

namespace ClassFunction

variable [Fintype G] {H : Subgroup G} [Fintype H]

/-- **Frobenius reciprocity**: `⟪ind H φ, ψ⟫_[G] = ⟪φ, res H ψ⟫_[H]`. The proof swaps the
order of a double sum over `G × G`, reindexes the inner sum by left multiplication (showing
it is independent of the outer variable, using that `ψ` is a class function), and then
restricts the resulting single sum over `G` to a sum over `↥H` (the extension-by-zero killing
the rest). MathComp: `cfdot_cfInd` / `Frobenius_reciprocity`. -/
theorem cfInner_ind_eq_cfInner_res (φ : ClassFunction H) (ψ : ClassFunction G) :
    ⟪ind H φ, ψ⟫_[G] = ⟪φ, res H ψ⟫_[H] := by
  classical
  have hG0 : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- Step 1: unfold `cfInner` and `ind`, and swap the order of summation.
  have hunfold : ⟪ind H φ, ψ⟫_[G]
      = (Fintype.card G : ℂ)⁻¹ * (Nat.card H : ℂ)⁻¹ *
          ∑ x : G, ∑ g : G, extendZero φ (x⁻¹ * g * x) * starRingEnd ℂ (ψ g) := by
    rw [cfInner_def]
    have hstep : ∀ g : G, ind H φ g * starRingEnd ℂ (ψ g)
        = (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendZero φ (x⁻¹ * g * x) * starRingEnd ℂ (ψ g) := by
      intro g
      rw [ind_apply, mul_assoc, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun g _ => hstep g, ← Finset.mul_sum, Finset.sum_comm]
    ring
  -- Step 2: for each `x`, the inner sum over `g` is independent of `x`.
  have hindep : ∀ x : G, ∑ g : G, extendZero φ (x⁻¹ * g * x) * starRingEnd ℂ (ψ g)
      = ∑ h : G, extendZero φ h * starRingEnd ℂ (ψ h) := by
    intro x
    refine Fintype.sum_equiv ((Equiv.mulLeft x⁻¹).trans (Equiv.mulRight x)) _ _ fun g => ?_
    have harg : ((Equiv.mulLeft x⁻¹).trans (Equiv.mulRight x)) g = x⁻¹ * g * x := by
      simp [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight]
    rw [harg]
    have hψ : ψ (x⁻¹ * g * x) = ψ g := by
      have := ψ.conj_apply g x⁻¹
      rwa [inv_inv] at this
    rw [hψ]
  -- Step 3: the constant sum over `x` collapses to `#G` copies.
  have hconst : ∑ x : G, ∑ g : G, extendZero φ (x⁻¹ * g * x) * starRingEnd ℂ (ψ g)
      = (Fintype.card G : ℂ) * ∑ h : G, extendZero φ h * starRingEnd ℂ (ψ h) := by
    rw [Finset.sum_congr rfl fun x _ => hindep x, Finset.sum_const, card_univ, nsmul_eq_mul]
  -- Step 4: restrict the remaining sum over `G` to a sum over `↥H`.
  have hrestrict : ∑ h : G, extendZero φ h * starRingEnd ℂ (ψ h)
      = ∑ h : H, φ h * starRingEnd ℂ (res H ψ h) := by
    have hsub : ∑ h ∈ Finset.univ.filter (· ∈ H),
          extendZero φ h * starRingEnd ℂ (ψ h) = ∑ h : G, extendZero φ h * starRingEnd ℂ (ψ h) :=
      Finset.sum_subset (Finset.filter_subset _ _) fun x _ hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [extendZero_apply_of_not_mem φ hx, zero_mul]
    have hbridge : ∑ h ∈ Finset.univ.filter (· ∈ H), extendZero φ h * starRingEnd ℂ (ψ h)
        = ∑ h : H, extendZero φ (h : G) * starRingEnd ℂ (ψ (h : G)) :=
      Finset.sum_subtype (p := fun x => x ∈ H) (Finset.univ.filter (· ∈ H)) (by simp)
        (fun h => extendZero φ h * starRingEnd ℂ (ψ h))
    rw [← hsub, hbridge]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [extendZero_apply_of_mem φ h.2, res_apply]
  have hH0' : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [hunfold, hconst, hrestrict, ClassFunction.cfInner_def, Nat.card_eq_fintype_card (α := H)]
  field_simp

/-- The flipped form of Frobenius reciprocity (`ind` in the right slot, `res` in the left),
via conjugate-symmetry of `cfInner`. -/
theorem cfInner_ind_right_eq_cfInner_res_left (ψ : ClassFunction G) (φ : ClassFunction H) :
    ⟪ψ, ind H φ⟫_[G] = ⟪res H ψ, φ⟫_[H] := by
  have h1 : ⟪ψ, ind H φ⟫_[G]
      = starRingEnd ℂ ⟪ind H φ, ψ⟫_[G] := cfInner_conj_symm (ind H φ) ψ
  have h2 : ⟪res H ψ, φ⟫_[H]
      = starRingEnd ℂ ⟪φ, res H ψ⟫_[H] := cfInner_conj_symm φ (res H ψ)
  rw [h1, h2, cfInner_ind_eq_cfInner_res]

end ClassFunction

/-! ### Restriction of a character is a character -/

section IsCharRes

variable {G : Type u} [Group G] [Fintype G]

/-- The character of `ρ.asModule` (the `MonoidAlgebra k Γ`-module associated to a
representation `ρ`) recovers `ρ`'s character. The generic bridge undoing
`Representation.ofModule'`, needed to transport `IsChar` across restriction of
representations. -/
theorem MonoidAlgebra.moduleCharacter_asModule {Γ : Type*} [Group Γ] {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V) :
    MonoidAlgebra.moduleCharacter Γ ρ.asModule = ρ.classFunction := by
  ext g
  have h2 : ρ.asModuleEquiv.conj (MonoidAlgebra.actionEnd ρ.asModule g) = ρ g := by
    refine LinearMap.ext fun v => ?_
    change ρ.asModuleEquiv (MonoidAlgebra.single g (1 : ℂ) • ρ.asModuleEquiv.symm v) = ρ g v
    rw [Representation.single_smul, one_smul, LinearEquiv.apply_symm_apply]
    rfl
  calc MonoidAlgebra.moduleCharacter Γ ρ.asModule g
      = trace ℂ ρ.asModule (MonoidAlgebra.actionEnd ρ.asModule g) := rfl
    _ = trace ℂ V (ρ g) := by rw [← h2, LinearMap.trace_conj']
    _ = ρ.classFunction g := rfl

/-- Every irreducible character of `G` is a character (trivially: the ℕ-combination with a
single coefficient `1`). -/
theorem Irr.isChar (χ : Irr G) : (χ : ClassFunction G).IsChar := by
  classical
  refine ⟨fun ψ => if ψ = χ then 1 else 0, ?_⟩
  have hone : (χ : ClassFunction G)
      = ∑ ψ : Irr G, if ψ = χ then (1 : ℂ) • (ψ : ClassFunction G) else (0 : ClassFunction G) := by
    rw [Finset.sum_ite_eq' Finset.univ χ fun ψ => (1 : ℂ) • (ψ : ClassFunction G)]
    simp
  rw [hone]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  by_cases h : ψ = χ <;> simp [h]

/-- A finite sum of characters is a character. -/
theorem ClassFunction.isChar_sum {ι : Type*} (s : Finset ι) (f : ι → ClassFunction G)
    (hf : ∀ i ∈ s, (f i).IsChar) : (∑ i ∈ s, f i).IsChar := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Restriction of a character to a subgroup is a character (of the subgroup). Route: restrict
the representation witnessing a simple submodule along `H.subtype`, then transport the
character back to a `ℂ[H]`-module character via `asModule` and apply `isChar_moduleCharacter'`;
extend to arbitrary characters by linearity of `res`. MathComp-shaped: `cfRes_char`. -/
theorem ClassFunction.IsChar.res {H : Subgroup G} [Fintype H] {ψ : ClassFunction G}
    (hψ : ψ.IsChar) : (ClassFunction.res H ψ).IsChar := by
  classical
  have hstep : ∀ χ : Irr G, (ClassFunction.res H (χ : ClassFunction G)).IsChar := by
    intro χ
    obtain ⟨N, hN, hχ⟩ := χ.exists_simple'
    haveI := hN
    set ρ := Representation.ofModule' (k := ℂ) (G := G) N with hρdef
    have hχ' : (χ : ClassFunction G) = ρ.classFunction := by
      rw [show (χ : ClassFunction G) = χ.toClassFunction from rfl, hχ]
      ext g
      rw [MonoidAlgebra.moduleCharacter_eq_ofModule'_character, Representation.classFunction_apply]
    set ρ' : Representation ℂ H N := ρ.comp H.subtype with hρ'def
    have hres : ClassFunction.res H (χ : ClassFunction G) = ρ'.classFunction := by
      ext h
      have hg := congrArg (fun φ : ClassFunction G => φ (h : G)) hχ'
      simp only [ClassFunction.res_apply, Representation.classFunction_apply] at hg ⊢
      rw [hg]
      rfl
    rw [hres, ← MonoidAlgebra.moduleCharacter_asModule ρ']
    exact ClassFunction.isChar_moduleCharacter' (G := H)
  obtain ⟨c, hc⟩ := hψ
  rw [hc, map_sum]
  have hterm : ∀ χ : Irr G, ClassFunction.res H ((c χ : ℂ) • (χ : ClassFunction G))
      = (c χ : ℂ) • ClassFunction.res H (χ : ClassFunction G) := fun χ => map_smul _ _ _
  rw [Finset.sum_congr rfl fun χ _ => hterm χ]
  -- a `ℕ`-combination of characters (of `H`) is a character
  refine ClassFunction.isChar_sum Finset.univ _ fun χ _ => ?_
  obtain ⟨d, hd⟩ := hstep χ
  refine ⟨fun ψ => c χ * d ψ, ?_⟩
  rw [hd, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [smul_smul, Nat.cast_mul]

end IsCharRes

/-! ### Induction of a character is a character -/

section IsCharInd

variable {G : Type u} [Group G] [Fintype G]

/-- Two characters (in the `IsChar` sense) have a natural-number inner product: expand both in
the basis `Irr.basis`, and use first orthogonality to collapse the double sum to the diagonal.
A two-sided strengthening of `CharacterArith.lean`'s `IsChar.cfInner_mem_nat`, needed by
`IsChar.ind`. -/
theorem ClassFunction.IsChar.cfInner_mem_nat' {φ ψ : ClassFunction G} (hφ : φ.IsChar)
    (hψ : ψ.IsChar) : ∃ n : ℕ, ⟪φ, ψ⟫_[G] = n := by
  classical
  obtain ⟨b, hb⟩ := hψ
  choose n hn using fun χ : Irr G => hφ.cfInner_mem_nat χ
  refine ⟨∑ χ : Irr G, b χ * n χ, ?_⟩
  rw [hb, ClassFunction.cfInner_sum_right]
  have hterm : ∀ χ : Irr G, ⟪φ, (b χ : ℂ) • (χ : ClassFunction G)⟫_[G] = ((b χ * n χ : ℕ) : ℂ) := by
    intro χ
    rw [ClassFunction.cfInner_smul_right, map_natCast, hn χ]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun χ _ => hterm χ, ← Nat.cast_sum]

/-- Induction of a character is a character: expand `ind H φ` in the basis `Irr.basis`; by
Frobenius reciprocity each coefficient `⟪ind H φ, χ⟫_[G]` equals `⟪φ, res H χ⟫_[H]`, a natural
number since `φ` and `res H χ` are both characters of `H` (`IsChar.res`, `Irr.isChar`).
MathComp-shaped: `cfInd_char`. -/
theorem ClassFunction.IsChar.ind {H : Subgroup G} [Fintype H] {φ : ClassFunction H}
    (hφ : φ.IsChar) : (ClassFunction.ind H φ).IsChar := by
  classical
  choose n hn using fun χ : Irr G =>
    hφ.cfInner_mem_nat' (ClassFunction.IsChar.res (Irr.isChar χ))
  refine ⟨n, ?_⟩
  conv_lhs => rw [ClassFunction.eq_sum_cfInner_smul (ClassFunction.ind H φ)]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [ClassFunction.cfInner_ind_eq_cfInner_res, hn χ]

end IsCharInd
