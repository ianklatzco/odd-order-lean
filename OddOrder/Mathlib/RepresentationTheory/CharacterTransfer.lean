/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import OddOrder.Mathlib.RepresentationTheory.Inertia

/-!
# Transport of characters: isomorphisms, quotients, nested subgroups, linear characters

This file is part of M6 Task 2 (the port of `PFsection1.v`): the `classfun.v`/`character.v`
transport layer that Peterfalvi §1 assumes from MathComp and that the M2 files deferred.

## Main definitions

* `ClassFunction.congr e : ClassFunction G ≃ₗ[ℂ] ClassFunction G'` (for `e : G ≃* G'`):
  transport of class functions along a group isomorphism, `(congr e φ) g' = φ (e.symm g')`.
  MathComp: `cfIsom` (`classfun.v`).
* `Irr.congr e : Irr G → Irr G'`: the same transport on irreducible characters.
  MathComp: `isom_Iirr` (`inertia.v`).
* `ClassFunction.resNested` / `ClassFunction.indNested`: restriction and induction between
  *nested* subgroups `K ≤ H` of an ambient group `G`, obtained from `res`/`ind` for
  `K.subgroupOf H` by transporting along `Subgroup.subgroupOfEquivOfLe`.  MathComp: `'Res[K]`
  and `'Ind[H]` applied between subgroups of `gT` (`classfun.v`).
* `ClassFunction.cfMod N : ClassFunction (G ⧸ N) →ₗ[ℂ] ClassFunction G`: inflation of a
  class function of a quotient.  MathComp: `cfMod`, `(phi %% H)%CF` (`classfun.v`).
* `Irr.mod N : Irr (G ⧸ N) → Irr G` and `Irr.exists_quo`/`Irr.quotientKerEquiv`: the
  bijection between irreducible characters of `G ⧸ N` and irreducible characters of `G`
  whose kernel contains `N`.  MathComp: `mod_Iirr`, `quo_Iirr`, `cfQuo` (`classfun.v`,
  `character.v`).
* `Irr.IsLinear`: linear (degree-one) characters, with multiplicativity
  (`Irr.IsLinear.map_mul`), the fact that all irreducible characters of a commutative group
  are linear (`Irr.isLinear_of_comm`), and multiplication of an irreducible character by a
  linear character (`Irr.IsLinear.mulIrr`).  MathComp: `lin_char`, `char_abelianP`,
  `mul_lin_irr` (`character.v`).

## Main results

* `Irr.IsLinear.map_mul` / `Irr.IsLinear.map_pow`: a linear character is multiplicative
  (its witnessing module is one-dimensional, so the action is by scalars).
* `Irr.isLinear_of_comm`: every irreducible character of a commutative group is linear
  (`#Irr = #classes = |G|` together with `∑ χ(1)² = |G|` forces every degree to be `1`).
  MathComp: `char_abelianP` (`character.v`).
* `Irr.IsLinear.apply_pow_orderOf_eq_one`: a linear character sends an element to a root of
  unity of its order.
* `ClassFunction.ind_indNested` / `ClassFunction.resNested_res`: transitivity of induction
  and restriction along `K ≤ H ≤ G`.  MathComp: `cfIndInd`, `cfResRes` (`classfun.v`).

## Design notes

* Following the M6 Task 1 layering, precomposition-preserves-irreducibility engines live
  next to their consumers: `Subrepresentation.orderIsoCompSurjective` (the surjective-hom
  version of Inertia.lean's `orderIsoCompMulEquiv`; one more entry for the deferred
  consolidation of these 10-line order isomorphisms).
* `Irr (G ⧸ N)` requires a `Fintype (G ⧸ N)` instance; lemmas take it as an instance
  argument (call sites can supply `Fintype.ofFinite`) rather than manufacturing a
  noncomputable global instance.
* `Irr.isLinear_of_comm` is proved by counting (`#Irr = #classes = |G|` together with
  `∑ χ(1)² = |G|` forces all degrees to be `1`), avoiding any further module theory.
-/

noncomputable section

open Finset LinearMap Module
open scoped ClassFunction

universe u v

/-! ### Precomposition with a surjective monoid homomorphism preserves irreducibility -/

section CompSurjective

variable {A W : Type*} [Semiring A] [AddCommMonoid W] [Module A W]
variable {G₁ G₂ : Type*} [Monoid G₁] [Monoid G₂]

/-- Precomposing a representation with a *surjective* monoid homomorphism leaves its lattice
of subrepresentations unchanged.  The surjective-homomorphism version of
`Subrepresentation.orderIsoCompMulEquiv` (`Inertia.lean`); the engine behind the
quotient-lift `Irr.mod`. -/
def Subrepresentation.orderIsoCompSurjective (ρ : Representation A G₂ W) (f : G₁ →* G₂)
    (hf : Function.Surjective f) :
    Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ where
  toFun σ := ⟨σ.toSubmodule, fun g v hv => by
    obtain ⟨g₁, rfl⟩ := hf g
    exact σ.apply_mem_toSubmodule g₁ hv⟩
  invFun σ := ⟨σ.toSubmodule, fun g v hv => σ.apply_mem_toSubmodule (f g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Precomposition with a surjective monoid homomorphism preserves irreducibility. -/
theorem Representation.IsIrreducible.compSurjective {ρ : Representation k G₂ V}
    (hρ : ρ.IsIrreducible) (f : G₁ →* G₂) (hf : Function.Surjective f) :
    Representation.IsIrreducible (ρ.comp f) :=
  (Subrepresentation.orderIsoCompSurjective ρ f hf).isSimpleOrder_iff.mpr hρ

/-- Irreducibility descends along precomposition with a surjective monoid homomorphism. -/
theorem Representation.IsIrreducible.of_compSurjective {ρ : Representation k G₂ V}
    (f : G₁ →* G₂) (hf : Function.Surjective f)
    (hρf : Representation.IsIrreducible (ρ.comp f)) : ρ.IsIrreducible :=
  (Subrepresentation.orderIsoCompSurjective ρ f hf).isSimpleOrder_iff.mp hρf

end CompSurjective

/-! ### Transport of class functions along a group isomorphism (`cfIsom`) -/

namespace ClassFunction

variable {G : Type u} {G' : Type v} [Group G] [Group G']

/-- Transport of class functions along a group isomorphism `e : G ≃* G'`:
`(congr e φ) g' = φ (e.symm g')`.  MathComp: `cfIsom` (`classfun.v`). -/
def congr (e : G ≃* G') : ClassFunction G ≃ₗ[ℂ] ClassFunction G' where
  toFun φ :=
    ⟨fun g' => φ (e.symm g'), fun g' h' => by
      have harg : e.symm (h' * g' * h'⁻¹) = e.symm h' * e.symm g' * (e.symm h')⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [harg, conj_apply]⟩
  invFun φ' :=
    ⟨fun g => φ' (e g), fun g h => by
      have harg : e (h * g * h⁻¹) = e h * e g * (e h)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [harg, conj_apply]⟩
  map_add' φ ψ := ext fun g' => rfl
  map_smul' c φ := ext fun g' => rfl
  left_inv φ := ext fun g => by simp only [coe_mk, MulEquiv.symm_apply_apply]
  right_inv φ' := ext fun g' => by simp only [coe_mk, MulEquiv.apply_symm_apply]

@[simp]
theorem congr_apply (e : G ≃* G') (φ : ClassFunction G) (g' : G') :
    congr e φ g' = φ (e.symm g') :=
  rfl

@[simp]
theorem congr_symm_apply (e : G ≃* G') (φ' : ClassFunction G') (g : G) :
    (congr e).symm φ' g = φ' (e g) :=
  rfl

/-- `congr` is an isometry for the hermitian inner products. -/
theorem cfInner_congr [Fintype G] [Fintype G'] (e : G ≃* G') (φ ψ : ClassFunction G) :
    ⟪congr e φ, congr e ψ⟫_[G'] = ⟪φ, ψ⟫_[G] := by
  rw [cfInner_def, cfInner_def, Fintype.card_congr e.toEquiv.symm]
  congr 1
  exact Fintype.sum_equiv e.toEquiv.symm _ _ fun g' => rfl

end ClassFunction

/-! ### Transport of irreducible characters along a group isomorphism -/

namespace Irr

variable {G : Type u} {G' : Type v} [Group G] [Group G'] [Fintype G] [Fintype G']

/-- Transport of an irreducible character along a group isomorphism `e : G ≃* G'`.
MathComp: `isom_Iirr` (`inertia.v`). -/
def congr (e : G ≃* G') (χ : Irr G) : Irr G' where
  toClassFunction := ClassFunction.congr e (χ : ClassFunction G)
  exists_simple' := by
    obtain ⟨N, hN, hval⟩ := χ.exists_simple'
    haveI hirr : (Representation.ofModule' (k := ℂ) (G := G) N).IsIrreducible :=
      MonoidAlgebra.isIrreducible_ofModule' N hN
    haveI hirr' : Representation.IsIrreducible
        ((Representation.ofModule' (k := ℂ) (G := G) N).comp
          (e.symm : G' ≃* G).toMonoidHom) :=
      Representation.IsIrreducible.compMulEquiv hirr _
    obtain ⟨χ', hχ'⟩ := Representation.exists_irr_classFunction_eq
      ((Representation.ofModule' (k := ℂ) (G := G) N).comp (e.symm : G' ≃* G).toMonoidHom)
    obtain ⟨N', hN', hval'⟩ := χ'.exists_simple'
    refine ⟨N', hN', ?_⟩
    rw [← hval', hχ']
    ext g'
    rw [ClassFunction.congr_apply, Representation.classFunction_apply, hval]
    rfl

@[simp]
theorem coe_congr (e : G ≃* G') (χ : Irr G) :
    ((χ.congr e : Irr G') : ClassFunction G') = ClassFunction.congr e (χ : ClassFunction G) :=
  rfl

@[simp]
theorem congr_apply (e : G ≃* G') (χ : Irr G) (g' : G') : χ.congr e g' = χ (e.symm g') :=
  rfl

@[simp]
theorem congr_symm_congr (e : G ≃* G') (χ : Irr G) : (χ.congr e).congr e.symm = χ :=
  ext fun g => by rw [congr_apply, congr_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]

@[simp]
theorem congr_congr_symm (e : G ≃* G') (χ' : Irr G') : (χ'.congr e.symm).congr e = χ' :=
  ext fun g' => by rw [congr_apply, congr_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]

variable (G G') in
/-- `Irr.congr` as an equivalence `Irr G ≃ Irr G'`. -/
def congrEquiv (e : G ≃* G') : Irr G ≃ Irr G' where
  toFun := congr e
  invFun := congr e.symm
  left_inv := congr_symm_congr e
  right_inv := congr_congr_symm e

@[simp]
theorem congrEquiv_apply (e : G ≃* G') (χ : Irr G) : congrEquiv G G' e χ = χ.congr e :=
  rfl

end Irr

/-! ### `IsChar` and `IsVirtualChar` transport along `congr` -/

namespace ClassFunction

variable {G : Type u} {G' : Type v} [Group G] [Group G'] [Fintype G] [Fintype G']

theorem IsChar.congr (e : G ≃* G') {φ : ClassFunction G} (hφ : φ.IsChar) :
    (ClassFunction.congr e φ).IsChar := by
  obtain ⟨c, hc⟩ := hφ
  rw [hc, map_sum]
  refine ClassFunction.isChar_sum _ _ fun χ _ => ?_
  rw [map_smul]
  have hcoe : ClassFunction.congr e (χ : ClassFunction G) = ((χ.congr e : Irr G')
      : ClassFunction G') := rfl
  rw [hcoe]
  exact (Irr.isChar (χ.congr e)).natCast_smul (c χ)

end ClassFunction

/-! ### Restriction and induction between nested subgroups -/

namespace ClassFunction

variable {G : Type u} [Group G] {K H : Subgroup G}

/-- Restriction of a class function of `H` to a subgroup `K ≤ H` (both subgroups of an
ambient group `G`): `res` for `K.subgroupOf H`, transported along
`Subgroup.subgroupOfEquivOfLe`.  MathComp: `'Res[K]` between subgroups of `gT`
(`classfun.v`). -/
def resNested (hKH : K ≤ H) : ClassFunction ↥H →ₗ[ℂ] ClassFunction ↥K :=
  (congr (Subgroup.subgroupOfEquivOfLe hKH)).toLinearMap.comp
    (res (K.subgroupOf H) : ClassFunction ↥H →ₗ[ℂ] ClassFunction ↥(K.subgroupOf H))

@[simp]
theorem resNested_apply (hKH : K ≤ H) (φ : ClassFunction ↥H) (k : ↥K) :
    resNested hKH φ k = φ ⟨(k : G), hKH k.2⟩ :=
  rfl

/-- Induction of a class function of `K` to a larger subgroup `K ≤ H` (both subgroups of an
ambient group `G`).  MathComp: `'Ind[H]` between subgroups of `gT` (`classfun.v`). -/
def indNested [Fintype H] (hKH : K ≤ H) : ClassFunction ↥K →ₗ[ℂ] ClassFunction ↥H :=
  (ind (K.subgroupOf H)).comp (congr (Subgroup.subgroupOfEquivOfLe hKH)).symm.toLinearMap

theorem indNested_def [Fintype H] (hKH : K ≤ H) (φ : ClassFunction ↥K) :
    indNested hKH φ
      = ind (K.subgroupOf H) ((congr (Subgroup.subgroupOfEquivOfLe hKH)).symm φ) :=
  rfl

/-- Restriction is transitive: restricting from `G` to `H` and then to `K ≤ H` is
restriction to `K`.  MathComp: `cfResRes` (`classfun.v`). -/
theorem resNested_res (hKH : K ≤ H) (ψ : ClassFunction G) :
    resNested hKH (res H ψ) = res K ψ :=
  ext fun _ => rfl

/-- The degree identity for nested induction:
`(indNested φ) 1 = |H : K| * φ 1`. -/
theorem indNested_apply_one [Fintype H] (hKH : K ≤ H) (φ : ClassFunction ↥K) :
    indNested hKH φ 1 = (K.relIndex H : ℂ) * φ 1 := by
  rw [indNested_def, ind_apply_one]
  have h1 : ((congr (Subgroup.subgroupOfEquivOfLe hKH)).symm φ) 1 = φ 1 := by
    rw [congr_symm_apply, map_one]
  rw [h1]
  rfl

section FintypeBoth

variable [Fintype H] [Fintype K]

/-- Frobenius reciprocity for nested subgroups `K ≤ H`.
MathComp: `Frobenius_reciprocity` between subgroups of `gT`. -/
theorem cfInner_indNested_eq_cfInner_resNested (hKH : K ≤ H) (φ : ClassFunction ↥K)
    (ψ : ClassFunction ↥H) :
    ⟪indNested hKH φ, ψ⟫_[↥H] = ⟪φ, resNested hKH ψ⟫_[↥K] := by
  haveI : Fintype ↥(K.subgroupOf H) := Fintype.ofFinite _
  rw [indNested_def, cfInner_ind_eq_cfInner_res]
  have hφ : congr (Subgroup.subgroupOfEquivOfLe hKH)
      ((congr (Subgroup.subgroupOfEquivOfLe hKH)).symm φ) = φ :=
    (congr (Subgroup.subgroupOfEquivOfLe hKH)).apply_symm_apply φ
  calc ⟪(congr (Subgroup.subgroupOfEquivOfLe hKH)).symm φ, res (K.subgroupOf H) ψ⟫_[
        ↥(K.subgroupOf H)]
      = ⟪congr (Subgroup.subgroupOfEquivOfLe hKH)
            ((congr (Subgroup.subgroupOfEquivOfLe hKH)).symm φ),
          congr (Subgroup.subgroupOfEquivOfLe hKH) (res (K.subgroupOf H) ψ)⟫_[↥K] :=
        (cfInner_congr _ _ _).symm
    _ = ⟪φ, resNested hKH ψ⟫_[↥K] := by rw [hφ]; rfl

end FintypeBoth

/-- Class functions agreeing against every irreducible character are equal. -/
theorem eq_of_forall_cfInner_irr_eq {G₀ : Type*} [Group G₀] [Fintype G₀]
    {φ ψ : ClassFunction G₀}
    (h : ∀ χ : Irr G₀,
      ⟪φ, χ.toClassFunction⟫_[G₀] = ⟪ψ, χ.toClassFunction⟫_[G₀]) :
    φ = ψ := by
  calc φ = ∑ χ : Irr G₀, ⟪φ, χ.toClassFunction⟫_[G₀] • χ.toClassFunction :=
        ClassFunction.eq_sum_cfInner_smul φ
    _ = ∑ χ : Irr G₀, ⟪ψ, χ.toClassFunction⟫_[G₀] • χ.toClassFunction :=
        Finset.sum_congr rfl fun χ _ => by rw [h χ]
    _ = ψ := (ClassFunction.eq_sum_cfInner_smul ψ).symm

/-- Induction is transitive: inducing from `K` to `H ≥ K` and then to `G` is induction
to `G`.  MathComp: `cfIndInd` (`classfun.v`). -/
theorem ind_indNested [Fintype G] [Fintype H] [Finite K] (hKH : K ≤ H)
    (φ : ClassFunction ↥K) :
    ind H (indNested hKH φ) = ind K φ := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  refine eq_of_forall_cfInner_irr_eq fun χ => ?_
  rw [cfInner_ind_eq_cfInner_res, cfInner_ind_eq_cfInner_res,
    cfInner_indNested_eq_cfInner_resNested, resNested_res]

end ClassFunction

/-! ### Inflation of class functions from a quotient (`cfMod`) -/

namespace ClassFunction

variable {G : Type u} [Group G] (N : Subgroup G) [N.Normal]

/-- Inflation of a class function of `G ⧸ N` to `G` along the quotient map.
MathComp: `cfMod`, `(phi %% H)%CF` (`classfun.v`). -/
def cfMod : ClassFunction (G ⧸ N) →ₗ[ℂ] ClassFunction G where
  toFun φ :=
    ⟨fun g => φ (g : G ⧸ N), fun g h => by
      have : ((h * g * h⁻¹ : G) : G ⧸ N) = (h : G ⧸ N) * g * (h : G ⧸ N)⁻¹ := by
        simp
      rw [this, conj_apply]⟩
  map_add' φ ψ := ext fun g => rfl
  map_smul' c φ := ext fun g => rfl

@[simp]
theorem cfMod_apply (φ : ClassFunction (G ⧸ N)) (g : G) : cfMod N φ g = φ (g : G ⧸ N) :=
  rfl

end ClassFunction

/-! ### The quotient correspondence for irreducible characters (`mod_Iirr` / `quo_Iirr`) -/

namespace Irr

variable {G : Type u} [Group G] (N : Subgroup G) [N.Normal] [Fintype G] [Fintype (G ⧸ N)]

/-- Inflation of an irreducible character of `G ⧸ N` to `G`: precomposition with the
quotient map, irreducible by surjectivity of the quotient map.  MathComp: `mod_Iirr`
(with `cfMod_irr`) (`character.v`). -/
def mod (χ : Irr (G ⧸ N)) : Irr G where
  toClassFunction := ClassFunction.cfMod N (χ : ClassFunction (G ⧸ N))
  exists_simple' := by
    obtain ⟨M, hM, hval⟩ := χ.exists_simple'
    haveI hirr : (Representation.ofModule' (k := ℂ) (G := G ⧸ N) M).IsIrreducible :=
      MonoidAlgebra.isIrreducible_ofModule' M hM
    haveI hirr' : Representation.IsIrreducible
        ((Representation.ofModule' (k := ℂ) (G := G ⧸ N) M).comp (QuotientGroup.mk' N)) :=
      hirr.compSurjective _ (QuotientGroup.mk'_surjective N)
    obtain ⟨χ', hχ'⟩ := Representation.exists_irr_classFunction_eq
      ((Representation.ofModule' (k := ℂ) (G := G ⧸ N) M).comp (QuotientGroup.mk' N))
    obtain ⟨M', hM', hval'⟩ := χ'.exists_simple'
    refine ⟨M', hM', ?_⟩
    rw [← hval', hχ']
    ext g
    rw [ClassFunction.cfMod_apply, Representation.classFunction_apply, hval]
    rfl

@[simp]
theorem mod_apply (χ : Irr (G ⧸ N)) (g : G) : χ.mod N g = χ (g : G ⧸ N) :=
  rfl

@[simp]
theorem coe_mod (χ : Irr (G ⧸ N)) :
    ((χ.mod N : Irr G) : ClassFunction G) = ClassFunction.cfMod N (χ : ClassFunction (G ⧸ N)) :=
  rfl

/-- The kernel of an inflated character contains `N`.  MathComp: `cfker_mod`
(`classfun.v`). -/
theorem le_ker_mod (χ : Irr (G ⧸ N)) : N ≤ (χ.mod N).ker := fun n hn => by
  rw [Irr.mem_ker_iff, mod_apply, mod_apply]
  have h1 : ((n : G) : G ⧸ N) = ((1 : G) : G ⧸ N) := by
    rw [QuotientGroup.mk_one]
    exact (QuotientGroup.eq_one_iff n).mpr hn
  rw [h1]

/-- **Descent (`cfQuo`)**: an irreducible character of `G` whose kernel contains `N`
factors through an irreducible character of `G ⧸ N`.  MathComp: `quo_Iirr` / `cfQuoE`
(`classfun.v`, `character.v`). -/
theorem exists_quo (χ : Irr G) (hker : N ≤ χ.ker) :
    ∃ χ' : Irr (G ⧸ N), ∀ g : G, χ' (g : G ⧸ N) = χ g := by
  classical
  set N₀ := χ.exists_simple'.choose with hN₀def
  have hN₀ : IsSimpleModule (MonoidAlgebra ℂ G) N₀ := χ.exists_simple'.choose_spec.1
  have hval : χ.toClassFunction = MonoidAlgebra.moduleCharacter G N₀ :=
    χ.exists_simple'.choose_spec.2
  set ρ : Representation ℂ G ↥N₀ := Representation.ofModule' (k := ℂ) (G := G) N₀ with hρdef
  have hkerρ : N ≤ MonoidHom.ker ρ := hker
  set ρ' : Representation ℂ (G ⧸ N) ↥N₀ := QuotientGroup.lift N ρ hkerρ with hρ'def
  have hcomp : ρ'.comp (QuotientGroup.mk' N) = ρ :=
    MonoidHom.ext fun g => QuotientGroup.lift_mk' N hkerρ g
  haveI hρirr : ρ.IsIrreducible := MonoidAlgebra.isIrreducible_ofModule' N₀ hN₀
  haveI hρ'irr : ρ'.IsIrreducible := by
    refine Representation.IsIrreducible.of_compSurjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) ?_
    rw [hcomp]
    exact hρirr
  obtain ⟨χ', hχ'⟩ := Representation.exists_irr_classFunction_eq ρ'
  refine ⟨χ', fun g => ?_⟩
  have h1 : χ' ((g : G) : G ⧸ N) = ρ'.character (g : G ⧸ N) := by
    have := congrArg (fun φ : ClassFunction (G ⧸ N) => φ (g : G ⧸ N)) hχ'
    simpa using this
  have h2 : ρ'.character ((g : G) : G ⧸ N) = ρ.character g := by
    have : ρ' ((g : G) : G ⧸ N) = ρ g := QuotientGroup.lift_mk' N hkerρ g
    rw [Representation.character, Representation.character, this]
  have h3 : ρ.character g = χ g := by
    have := congrArg (fun φ : ClassFunction G => φ g) hval
    simp only [Irr.coe_toClassFunction] at this
    rw [this]
    rfl
  rw [h1, h2, h3]

/-- **The quotient correspondence**: irreducible characters of `G ⧸ N` biject with the
irreducible characters of `G` whose kernel contains `N`, via inflation.  MathComp:
`mod_IirrK` / `quo_IirrK` (`character.v`). -/
def quotientKerEquiv : Irr (G ⧸ N) ≃ {χ : Irr G // N ≤ χ.ker} where
  toFun χ := ⟨χ.mod N, le_ker_mod N χ⟩
  invFun χ := (exists_quo N χ.1 χ.2).choose
  left_inv χ := by
    refine Irr.ext fun q => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact (exists_quo N (χ.mod N) (le_ker_mod N χ)).choose_spec g
  right_inv χ := by
    have hspec := (exists_quo N χ.1 χ.2).choose_spec
    refine Subtype.ext (Irr.ext fun g => ?_)
    rw [mod_apply, hspec g]

@[simp]
theorem quotientKerEquiv_apply (χ : Irr (G ⧸ N)) :
    ((quotientKerEquiv N χ : {χ : Irr G // N ≤ χ.ker}) : Irr G) = χ.mod N :=
  rfl

theorem quotientKerEquiv_symm_apply (χ : {χ : Irr G // N ≤ χ.ker}) (g : G) :
    (quotientKerEquiv N).symm χ (g : G ⧸ N) = (χ : Irr G) g :=
  (exists_quo N χ.1 χ.2).choose_spec g

end Irr

/-! ### Linear (degree-one) characters -/

namespace Irr

variable {G : Type u} [Group G] [Fintype G]

/-- A **linear character** is an irreducible character of degree one.
MathComp: `lin_char` (`character.v`). -/
def IsLinear (χ : Irr G) : Prop := χ 1 = 1

theorem isLinear_iff (χ : Irr G) : χ.IsLinear ↔ χ 1 = 1 := Iff.rfl

/-- A linear character is multiplicative: its witnessing simple module is one-dimensional,
so the group acts by scalars.  MathComp: `lin_charM` (`character.v`). -/
theorem IsLinear.map_mul {χ : Irr G} (hχ : χ.IsLinear) (g h : G) :
    χ (g * h) = χ g * χ h := by
  obtain ⟨N, hN, hval⟩ := χ.exists_simple'
  haveI := hN
  have happ : ∀ x : G, χ x = trace ℂ N (MonoidAlgebra.actionEnd N x) := by
    intro x
    have h := congrArg (fun φ : ClassFunction G => φ x) hval
    simpa [MonoidAlgebra.moduleCharacter_apply] using h
  have hone : MonoidAlgebra.actionEnd N (1 : G) = 1 := by
    refine LinearMap.ext fun v => ?_
    rw [MonoidAlgebra.actionEnd_apply, ← MonoidAlgebra.one_def, one_smul, Module.End.one_apply]
  have hfr : Module.finrank ℂ N = 1 := by
    have h1 := happ 1
    rw [hone, LinearMap.trace_one] at h1
    have : (Module.finrank ℂ N : ℂ) = 1 := by rw [← h1]; exact hχ
    exact_mod_cast this
  haveI : Module.Free ℂ N := Module.Free.of_divisionRing ℂ N
  obtain ⟨v, hv0, hspan⟩ := (finrank_eq_one_iff' (K := ℂ) (V := N)).mp hfr
  -- every endomorphism scaling `v` is the corresponding scalar times the identity
  have hscalar : ∀ (f : Module.End ℂ N) (c : ℂ), f v = c • v → f = c • 1 := by
    intro f c hfv
    refine LinearMap.ext fun w => ?_
    obtain ⟨a, rfl⟩ := hspan w
    rw [map_smul, hfv, LinearMap.smul_apply, Module.End.one_apply, smul_comm]
  have htrace : ∀ (f : Module.End ℂ N) (c : ℂ), f = c • 1 → trace ℂ N f = c := by
    intro f c hf
    rw [hf, map_smul, LinearMap.trace_one, hfr, Nat.cast_one, smul_eq_mul, mul_one]
  have hcg : ∀ x : G, MonoidAlgebra.actionEnd N x v = χ x • v := by
    intro x
    obtain ⟨c, hc⟩ := hspan (MonoidAlgebra.actionEnd N x v)
    have hχc : χ x = c := by rw [happ x, htrace _ c (hscalar _ c hc.symm)]
    rw [hχc, hc]
  have key : MonoidAlgebra.actionEnd N (g * h) v = (χ g * χ h) • v := by
    rw [MonoidAlgebra.actionEnd_mul, LinearMap.comp_apply, hcg h, map_smul, hcg g, smul_smul,
      mul_comm (χ h) (χ g)]
  have heq : χ (g * h) • v = (χ g * χ h) • v := (hcg (g * h)).symm.trans key
  exact smul_left_injective ℂ hv0 heq

/-- A linear character sends `1` to `1`. -/
@[simp]
theorem IsLinear.map_one {χ : Irr G} (hχ : χ.IsLinear) : χ 1 = 1 := hχ

/-- A linear character is multiplicative on powers.  MathComp: `lin_charX`
(`character.v`). -/
theorem IsLinear.map_pow {χ : Irr G} (hχ : χ.IsLinear) (g : G) (n : ℕ) :
    χ (g ^ n) = (χ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, hχ.map_one]
  | succ n ih => rw [pow_succ, pow_succ, hχ.map_mul, ih]

/-- A linear character sends a group element to a root of unity of its order.
MathComp: `lin_char_unity_root`-shaped (`character.v`). -/
theorem IsLinear.apply_pow_orderOf_eq_one {χ : Irr G} (hχ : χ.IsLinear) (g : G) :
    (χ g) ^ orderOf g = 1 := by
  rw [← hχ.map_pow, pow_orderOf_eq_one, hχ.map_one]

/-- **Every irreducible character of a commutative group is linear.**  Counting: the number
of irreducible characters equals the number of conjugacy classes, which for a commutative
group is `|G|`; together with `∑ χ(1)² = |G|` and `χ(1) ≥ 1`, every degree must be `1`.
The commutativity is passed as a hypothesis (rather than a `CommGroup` instance) so the
lemma applies to subgroups generated by commuting elements without an extra instance.
MathComp: `char_abelianP` (`character.v`). -/
theorem isLinear_of_comm (hcomm : ∀ a b : G, a * b = b * a) (χ : Irr G) : χ.IsLinear := by
  classical
  -- for a commutative group, conjugacy classes are singletons, so `#Irr = |G|`
  have hconj : ∀ a b : G, IsConj a b ↔ a = b := by
    intro a b
    constructor
    · intro h
      obtain ⟨c, hc⟩ := isConj_iff.mp h
      rw [hcomm c a, mul_assoc, mul_inv_cancel, mul_one] at hc
      exact hc
    · rintro rfl; exact IsConj.refl a
  have hcard : Fintype.card (Irr G) = Fintype.card G := by
    have h1 : Nat.card (Irr G) = Nat.card (ConjClasses G) := Irr.card_eq_card_conjClasses
    have hEquiv : ConjClasses G ≃ G :=
      { toFun := fun c => Quotient.liftOn c (fun a => a) fun a b h => (hconj a b).mp h
        invFun := ConjClasses.mk
        left_inv := fun c => by
          induction c using Quotient.inductionOn with
          | h a => rfl
        right_inv := fun a => rfl }
    have h2 : Nat.card (ConjClasses G) = Nat.card G := Nat.card_congr hEquiv
    have h3 : Nat.card (Irr G) = Nat.card G := h1.trans h2
    simpa [Nat.card_eq_fintype_card] using h3
  -- the natural-number degrees
  set d : Irr G → ℕ := fun ψ => ψ.exists_degree.choose with hddef
  have hdpos : ∀ ψ : Irr G, 1 ≤ d ψ := fun ψ => ψ.exists_degree.choose_spec.1
  have hdval : ∀ ψ : Irr G, (ψ 1 : ℂ) = (d ψ : ℂ) := fun ψ => ψ.exists_degree.choose_spec.2
  -- `∑ (d ψ)² = |G|`
  have h' : ∑ ψ : Irr G, ((d ψ : ℂ)) ^ 2 = (Nat.card G : ℂ) := by
    rw [← Irr.sum_sq_degree (G := G)]
    exact Finset.sum_congr rfl fun ψ _ => by rw [hdval ψ]
  have hsum : ∑ ψ : Irr G, (d ψ) ^ 2 = Fintype.card G := by
    have hnat : ((∑ ψ : Irr G, (d ψ) ^ 2 : ℕ) : ℂ) = (Nat.card G : ℂ) := by
      push_cast
      exact h'
    rw [Nat.card_eq_fintype_card] at hnat
    exact_mod_cast hnat
  -- each degree is `1`
  by_contra hnl
  rw [isLinear_iff] at hnl
  have hd0 : d χ ≠ 1 := fun heq => hnl (by rw [hdval χ, heq, Nat.cast_one])
  have hd2 : 2 ≤ d χ := by have := hdpos χ; omega
  -- but then `∑ (d ψ)² > |G|`
  have hlt : ∑ _ψ : Irr G, 1 < ∑ ψ : Irr G, (d ψ) ^ 2 := by
    refine Finset.sum_lt_sum (fun ψ _ => ?_) ⟨χ, Finset.mem_univ χ, ?_⟩
    · nlinarith [hdpos ψ]
    · nlinarith [hd2]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hsum, hcard] at hlt
  exact lt_irrefl _ hlt

end Irr

/-! ### Pullback of class functions along an arbitrary group homomorphism (`cfMorph`)

Added with M6 Task 3 (PFsection2): the Dade restriction `'aa_B` is the pullback of a class
function of `'N_L(B)` along the projection `'M(B) → 'N_L(B)`, i.e. `cfMorph` for a
homomorphism that is neither injective nor a quotient map, so neither `res` nor `cfMod`
covers it. -/

section CompHom

variable {K : Type u} {H : Type v} [Group K] [Group H]

/-- Pullback of a class function along a group homomorphism `f : K →* H`:
`(compHom f φ) k = φ (f k)`.  Conjugation-invariance is inherited pointwise, so no
injectivity, surjectivity, or kernel hypothesis is needed.  MathComp: `cfMorph`
(`classfun.v`); `ClassFunction.cfMod` is the special case `f = QuotientGroup.mk' N`, and
`ClassFunction.res` the special case `f = H.subtype`. -/
def ClassFunction.compHom (f : K →* H) : ClassFunction H →ₗ[ℂ] ClassFunction K where
  toFun φ :=
    ⟨fun k => φ (f k), fun k h => by
      have harg : f (h * k * h⁻¹) = f h * f k * (f h)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [harg, conj_apply]⟩
  map_add' φ ψ := ext fun k => rfl
  map_smul' c φ := ext fun k => rfl

@[simp]
theorem ClassFunction.compHom_apply (f : K →* H) (φ : ClassFunction H) (k : K) :
    ClassFunction.compHom f φ k = φ (f k) :=
  rfl

/-- Pullback along a group homomorphism sends characters to characters: an irreducible
character realized by the representation `ρ` of a simple submodule pulls back to the
character of `ρ.comp f`, a module character (`ClassFunction.isChar_moduleCharacter'`);
extend by `ℕ`-linearity.  MathComp: `cfMorph_char` (`character.v`). -/
theorem ClassFunction.IsChar.compHom [Fintype K] [Fintype H] {φ : ClassFunction H}
    (hφ : φ.IsChar) (f : K →* H) : (ClassFunction.compHom f φ).IsChar := by
  classical
  have hstep : ∀ χ : Irr H, (ClassFunction.compHom f (χ : ClassFunction H)).IsChar := by
    intro χ
    obtain ⟨N, hN, hχ⟩ := χ.exists_simple'
    haveI := hN
    set ρ := Representation.ofModule' (k := ℂ) (G := H) N with hρdef
    have hχ' : (χ : ClassFunction H) = ρ.classFunction := by
      rw [show (χ : ClassFunction H) = χ.toClassFunction from rfl, hχ]
      ext g
      rw [MonoidAlgebra.moduleCharacter_eq_ofModule'_character,
        Representation.classFunction_apply]
    set ρ' : Representation ℂ K N := ρ.comp f with hρ'def
    have hres : ClassFunction.compHom f (χ : ClassFunction H) = ρ'.classFunction := by
      ext k
      have hg := congrArg (fun ψ : ClassFunction H => ψ (f k)) hχ'
      simp only [ClassFunction.compHom_apply, Representation.classFunction_apply] at hg ⊢
      rw [hg]
      rfl
    rw [hres, ← MonoidAlgebra.moduleCharacter_asModule ρ']
    exact ClassFunction.isChar_moduleCharacter' (G := K)
  obtain ⟨c, hc⟩ := hφ
  rw [hc, map_sum]
  have hterm : ∀ χ : Irr H, ClassFunction.compHom f ((c χ : ℂ) • (χ : ClassFunction H))
      = (c χ : ℂ) • ClassFunction.compHom f (χ : ClassFunction H) := fun χ => map_smul _ _ _
  rw [Finset.sum_congr rfl fun χ _ => hterm χ]
  refine ClassFunction.isChar_sum Finset.univ _ fun χ _ => ?_
  obtain ⟨d, hd⟩ := hstep χ
  refine ⟨fun ψ => c χ * d ψ, ?_⟩
  rw [hd, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [smul_smul, Nat.cast_mul]

end CompHom
