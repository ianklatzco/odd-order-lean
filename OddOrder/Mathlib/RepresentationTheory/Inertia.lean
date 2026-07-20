/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import OddOrder.Mathlib.RepresentationTheory.Induced
import OddOrder.Mathlib.RepresentationTheory.CharAut

/-!
# Conjugate characters, inertia groups, and character-level Clifford theory

This file is Task 1 of the M6 plan (Peterfalvi PF1–PF7 lane): the inertia-group
infrastructure that MathComp's `inertia.v` provides to `PFsection1.v`'s (1.5)/(1.7)
Clifford region.  For a normal subgroup `H ⊴ G` it delivers conjugation of class
functions of `H` by elements of `G`, the induced action on irreducible characters,
the inertia subgroup `'I_G[θ]`, the conjugation orbit `cfclass`, and Clifford's
theorem at the character level, in the shapes PF (1.5)(a)–(d) consume.

## Main definitions

* `ClassFunction.conjg φ g`: the conjugate class function, `(conjg φ g) h = φ (g⁻¹ h g)`
  (a left action: `conjg φ (a * b) = conjg (conjg φ b) a`).  MathComp: `cfConjg`,
  `(phi ^ y)%CF` (`inertia.v`) — **note the inverse convention**: MathComp's
  `(phi ^ y)%CF x = phi (x ^ y⁻¹) = phi (y x y⁻¹)` is our `conjg φ y⁻¹`; orbits and
  stabilizers coincide, per the M6 Task 1 binding decision `(φ ^ g) h = φ (g⁻¹ h g)`.
* `Irr.conjg θ g`: the same action on irreducible characters (the conjugate of an
  irreducible character is irreducible).  MathComp: `conjg_Iirr` (`inertia.v`).
* `ClassFunction.inertia φ` / `Irr.inertia θ`: the inertia subgroup, the stabilizer
  `{g : G | conjg φ g = φ}` of `φ` in `G`.  MathComp: `'I_G[phi]` (`inertia.v`).
  `H ≤ inertia φ` is `ClassFunction.le_inertia`; MathComp's `normal_Inertia`
  (`H ⊴ 'I_G[θ]`) is Mathlib's `Subgroup.Normal.subgroupOf`.
* `Irr.cfclass θ`: the orbit of `θ : Irr H` under `G`-conjugation, as a
  `Finset (Irr H)`.  MathComp: `('chi_t ^: G)%CF` (`inertia.v`).

## Main results

* `Irr.card_cfclass`: `#(cfclass θ) = (inertia θ).index` (orbit–stabilizer).
  MathComp: `size_cfclass`.
* `Irr.res_ind_eq_smul_sum_cfclass`:
  `'Res[H] ('Ind[G] θ) = |I_G(θ) : H| • ∑_{ξ ∈ θ ^: G} ξ` — the engine behind
  Peterfalvi (1.5)(a) (`cfResInd_sum_cfclass`), proved here at `inertia.v` strength.
* `Irr.cfInner_res_ind_self`: `⟪'Res[H] ('Ind[G] θ), θ⟫ = |I_G(θ) : H|` — the
  `⟪res (ind θ), θ⟫`-fact PF (1.5)(b) consumes via Frobenius reciprocity.
* `Irr.mem_cfclass_of_cfInner_res_ne_zero`: two irreducible constituents of a
  restriction `'Res[H] χ` are `G`-conjugate ("the constituents of `Res` lie in one
  orbit").  MathComp: the `cfclass`-membership content of Clifford's theorem.
* `Irr.res_eq_cfInner_smul_sum_cfclass` — **Clifford's theorem** at character level:
  if `θ` is an irreducible constituent of `'Res[H] χ`, then
  `'Res[H] χ = ⟪'Res[H] χ, θ⟫ • ∑_{ξ ∈ θ ^: G} ξ`.
  MathComp: `Clifford_Res_sum_cfclass` (`inertia.v`).
* `ClassFunction.ind_conjg` / `Irr.ind_eq_of_mem_cfclass`: induction is constant on
  conjugation orbits.  MathComp: `cfclass_Ind` (`inertia.v`).
* `Representation.IsIrreducible.compMulEquiv`: precomposition with a monoid
  isomorphism preserves irreducibility (the subrepresentation lattices are isomorphic;
  the engine behind `Irr.conjg`, playing the role of MathComp's `morphim_repr`
  irreducibility transport).

## Design notes

* **Left-action convention.**  Per the M6 Task 1 binding decision, `conjg φ g` evaluates
  as `φ (g⁻¹ h g)`, so `g • φ := conjg φ g` is a *left* action
  (`conjg_mul : conjg φ (a * b) = conjg (conjg φ b) a`), matching Mathlib's convention
  for actions on function spaces.  MathComp's `cfConjg` is the corresponding right
  action, `(phi ^ y) = conjg phi y⁻¹`; every orbit/stabilizer statement is unaffected.
  No `MulAction` instance is installed (it would be an orphan instance on the subtype
  `ClassFunction ↥H`); the action laws are provided as standalone lemmas.
* **Normality, not normalizer membership.**  MathComp defines `cfConjg` for arbitrary
  `y` with a junk-value fallback and hypotheses `y ∈ 'N(H)` on the lemmas.  All PF uses
  have `H ⊴ G`, so `conjg` takes `[H.Normal]` and every lemma is hypothesis-free.
* **`Irr.conjg` via representation transport.**  The witness that the conjugate of an
  irreducible character is irreducible precomposes the representation
  `Representation.ofModule'` of a simple-submodule witness with the conjugation
  automorphism `(MulAut.conjNormal g).symm : H ≃* H`; irreducibility transports along
  the (identity-on-submodules) order isomorphism of subrepresentation lattices
  (`Subrepresentation.orderIsoCompMulEquiv`), and
  `Representation.exists_irr_classFunction_eq` converts back to a simple-submodule
  witness.  This reuses ClassFunction.lean's engine instead of building a
  `MonoidAlgebra.domCongr`-twisted submodule kit parallel to CharAut.lean's.
* **Clifford at class-function level.**  `res_ind_eq_smul_sum_cfclass` is proved by
  direct computation with the averaging formula (fibering the sum over `G` by the
  conjugated character, orbit–stabilizer for the fiber sizes) — the same route as
  PFsection1's proof of (1.5)(a) — and Clifford's theorem follows from it by
  basis-expansion and Frobenius reciprocity, with no further representation theory.
  Scope per the task: the full inertia-induction bijection (Peterfalvi (1.7)(a),
  MathComp `constt_Inertia_bijection`) is deliberately deferred to M6 Task 2.
-/

noncomputable section

open Finset LinearMap Module
open scoped ClassFunction

universe u

variable {G : Type u} [Group G]

/-! ### Conjugation of class functions of a normal subgroup -/

namespace ClassFunction

variable {H : Subgroup G} [hH : H.Normal]

/-- The conjugate of a class function of a normal subgroup `H ⊴ G` by an element of `G`:
`(conjg φ g) h = φ (g⁻¹ h g)`.  A left action of `G` on `ClassFunction H`
(see `conjg_mul`).  MathComp: `cfConjg` / `(phi ^ y)%CF` (`inertia.v`), with the inverse
convention — MathComp's `(phi ^ y)%CF` is `conjg φ y⁻¹` (see the module docstring). -/
def conjg (φ : ClassFunction H) (g : G) : ClassFunction H where
  toFun h := φ ((MulAut.conjNormal g).symm h)
  conj_invariant' h k := by
    have hmul : (MulAut.conjNormal g).symm (k * h * k⁻¹)
        = (MulAut.conjNormal g).symm k * (MulAut.conjNormal g).symm h
            * ((MulAut.conjNormal g).symm k)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hmul, φ.conj_apply]

/-- Evaluation of a conjugated class function, automorphism form.  For the explicit
`g⁻¹ * h * g` form, see `conjg_apply_mk`.  MathComp: `cfConjgE` (`inertia.v`). -/
theorem conjg_apply (φ : ClassFunction H) (g : G) (h : H) :
    conjg φ g h = φ ((MulAut.conjNormal g).symm h) :=
  rfl

/-- Evaluation of a conjugated class function, explicit form:
`(conjg φ g) h = φ ⟨g⁻¹ * h * g, _⟩`.  MathComp: `cfConjgE` (`inertia.v`). -/
theorem conjg_apply_mk (φ : ClassFunction H) (g : G) (h : H) (hmem : g⁻¹ * ↑h * g ∈ H) :
    conjg φ g h = φ ⟨g⁻¹ * ↑h * g, hmem⟩ := by
  rw [conjg_apply]
  congr 1
  exact Subtype.ext (MulAut.conjNormal_symm_apply g h)

/-- Conjugating by `1` is the identity.  MathComp: `cfConjgJ1` (`inertia.v`). -/
@[simp]
theorem conjg_one (φ : ClassFunction H) : conjg φ (1 : G) = φ :=
  ext fun h => by
    rw [conjg_apply, map_one]
    rfl

/-- The left-action law for conjugation: `conjg φ (a * b) = conjg (conjg φ b) a`.
MathComp: `cfConjgM` (`inertia.v`), with the opposite (right-action) bracketing —
see the module docstring for the convention. -/
theorem conjg_mul (φ : ClassFunction H) (a b : G) :
    conjg φ (a * b) = conjg (conjg φ b) a :=
  ext fun h => by
    rw [conjg_apply, conjg_apply, conjg_apply]
    congr 1
    ext
    simp only [MulAut.conjNormal_symm_apply]
    group

/-- Conjugating by `g` then `g⁻¹` recovers the class function.
MathComp: `cfConjgK` (`inertia.v`). -/
@[simp]
theorem conjg_conjg_inv (φ : ClassFunction H) (g : G) : conjg (conjg φ g) g⁻¹ = φ := by
  rw [← conjg_mul, inv_mul_cancel, conjg_one]

/-- Conjugating by `g⁻¹` then `g` recovers the class function.
MathComp: `cfConjgKV` (`inertia.v`). -/
@[simp]
theorem conjg_inv_conjg (φ : ClassFunction H) (g : G) : conjg (conjg φ g⁻¹) g = φ := by
  rw [← conjg_mul, mul_inv_cancel, conjg_one]

theorem conjg_injective (g : G) :
    Function.Injective fun φ : ClassFunction H => conjg φ g := fun φ ψ h => by
  have h2 : conjg (conjg φ g) g⁻¹ = conjg (conjg ψ g) g⁻¹ := congrArg (conjg · g⁻¹) h
  simpa using h2

/-- Conjugation by an element of `H` itself fixes every class function of `H` (class
functions are conjugation-invariant).  MathComp: `cfConjg_id`-shaped; gives
`H ≤ inertia φ` (`sub_Inertia`). -/
theorem conjg_eq_self_of_mem (φ : ClassFunction H) {g : G} (hg : g ∈ H) :
    conjg φ g = φ :=
  ext fun h => by
    rw [conjg_apply]
    have hval : (MulAut.conjNormal g).symm h = (⟨g, hg⟩ : H)⁻¹ * h * ⟨g, hg⟩ :=
      Subtype.ext (by simp [MulAut.conjNormal_symm_apply])
    rw [hval]
    have hconj := φ.conj_apply h (⟨g, hg⟩ : H)⁻¹
    rwa [inv_inv] at hconj

/-- A conjugated class function has the same value at `1`.
MathComp: `cfConjg1` (`inertia.v`). -/
@[simp]
theorem conjg_apply_one (φ : ClassFunction H) (g : G) : conjg φ g 1 = φ 1 := by
  rw [conjg_apply, map_one]

theorem conjg_add (φ ψ : ClassFunction H) (g : G) :
    conjg (φ + ψ) g = conjg φ g + conjg ψ g :=
  ext fun _ => rfl

theorem conjg_smul (c : ℂ) (φ : ClassFunction H) (g : G) :
    conjg (c • φ) g = c • conjg φ g :=
  ext fun _ => rfl

theorem conjg_sum {ι : Type*} (s : Finset ι) (f : ι → ClassFunction H) (g : G) :
    conjg (∑ i ∈ s, f i) g = ∑ i ∈ s, conjg (f i) g :=
  ext fun h => by
    rw [conjg_apply, sum_apply, sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl

/-- Complex conjugation commutes with conjugation of class functions.
MathComp: `conj_cfConjg` (`inertia.v`). -/
theorem conjC_conjg (φ : ClassFunction H) (g : G) :
    (conjg φ g).conjC = conjg φ.conjC g :=
  ext fun _ => rfl

/-- The restriction of a class function of `G` is invariant under `G`-conjugation.
MathComp: `sub_inertia_Res`-shaped (`'I_G[φ] ≤ 'I_G['Res φ]` collapses to this when the
ambient group stabilizes `φ`) (`inertia.v`). -/
theorem conjg_res (ψ : ClassFunction G) (g : G) : conjg (res H ψ) g = res H ψ :=
  ext fun h => by
    rw [conjg_apply, res_apply, res_apply, MulAut.conjNormal_symm_apply]
    have hconj := ψ.conj_apply (↑h) g⁻¹
    rwa [inv_inv] at hconj

/-- The zero-extension of a conjugated class function is the conjugate-shifted
zero-extension (both sides vanish together, by normality of `H`). -/
theorem extendZero_conjg (φ : ClassFunction H) (g z : G) :
    extendZero (conjg φ g) z = extendZero φ (g⁻¹ * z * g) := by
  by_cases hz : z ∈ H
  · have hz' : g⁻¹ * z * g ∈ H := by
      have hmem := hH.conj_mem z hz g⁻¹
      rwa [inv_inv] at hmem
    rw [extendZero_apply_of_mem _ hz, extendZero_apply_of_mem _ hz',
      conjg_apply_mk φ g ⟨z, hz⟩ hz']
  · have hz' : g⁻¹ * z * g ∉ H := fun hmem => by
      have hback := hH.conj_mem _ hmem g
      rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at hback
      exact hz hback
    rw [extendZero_apply_of_not_mem _ hz, extendZero_apply_of_not_mem _ hz']

section FintypeH

variable [Fintype H]

/-- Conjugation is an isometry for the hermitian inner product.
MathComp: `cfdot_cfConjg`-shaped (`inertia.v`). -/
theorem cfInner_conjg (φ ψ : ClassFunction H) (g : G) :
    ⟪conjg φ g, conjg ψ g⟫_[H] = ⟪φ, ψ⟫_[H] := by
  rw [cfInner_def, cfInner_def]
  congr 1
  exact Fintype.sum_equiv (MulAut.conjNormal g).symm.toEquiv _ _ fun h => rfl

end FintypeH

section FintypeG

variable [Fintype G]

/-- Induction is invariant under conjugation of the induced class function.
MathComp: `cfclass_Ind`-engine (`inertia.v`); see `Irr.ind_eq_of_mem_cfclass` for the
orbit form. -/
theorem ind_conjg (φ : ClassFunction H) (g : G) : ind H (conjg φ g) = ind H φ := by
  ext x
  rw [ind_apply, ind_apply]
  congr 1
  have hshift : ∀ y : G,
      extendZero (conjg φ g) (y⁻¹ * x * y) = extendZero φ ((y * g)⁻¹ * x * (y * g)) := by
    intro y
    rw [extendZero_conjg]
    congr 1
    group
  rw [Finset.sum_congr rfl fun y _ => hshift y]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun y => rfl

end FintypeG

/-! ### The inertia subgroup -/

/-- The inertia subgroup of a class function `φ` of a normal subgroup `H ⊴ G`: the
stabilizer `{g : G | conjg φ g = φ}` of `φ` under conjugation.
MathComp: `'I_G[phi]` (`inertia.v`; MathComp's ambient intersection with `G` is the
whole group here). -/
def inertia (φ : ClassFunction H) : Subgroup G where
  carrier := {g : G | conjg φ g = φ}
  one_mem' := conjg_one φ
  mul_mem' := fun {a b} ha hb => by
    have ha' : conjg φ a = φ := ha
    have hb' : conjg φ b = φ := hb
    have hab : conjg φ (a * b) = φ := by rw [conjg_mul, hb', ha']
    exact hab
  inv_mem' := fun {g} hg => by
    have hg' : conjg φ g = φ := hg
    have hginv : conjg φ g⁻¹ = φ := by
      conv_lhs => rw [← hg']
      rw [conjg_conjg_inv]
    exact hginv

@[simp]
theorem mem_inertia {φ : ClassFunction H} {g : G} : g ∈ inertia φ ↔ conjg φ g = φ :=
  Iff.rfl

/-- The normal subgroup is contained in every inertia subgroup.
MathComp: `sub_Inertia` (`inertia.v`).  For `H ⊴ inertia φ` (MathComp's
`normal_Inertia`), combine with Mathlib's `Subgroup.Normal.subgroupOf`. -/
theorem le_inertia (φ : ClassFunction H) : H ≤ inertia φ := fun _ hg =>
  conjg_eq_self_of_mem φ hg

end ClassFunction

/-! ### Complex conjugation versus restriction and induction

The `cfAut`-commutation facts the PF1 (1.5)(e) region consumes (`conj_cfInd` in
`odd_induced_orthogonal`'s proof); placed here because CharAut.lean (which owns
`conjC`) and Induced.lean (which owns `res`/`ind`) do not import each other. -/

namespace ClassFunction

variable {H : Subgroup G}

/-- Complex conjugation commutes with restriction.  MathComp: `cfAut_cfRes`
specialized to conjugation (`classfun.v`). -/
theorem conjC_res (ψ : ClassFunction G) : (res H ψ).conjC = res H ψ.conjC :=
  ext fun _ => rfl

/-- Complex conjugation commutes with zero-extension. -/
theorem extendZero_conjC (φ : ClassFunction H) (z : G) :
    starRingEnd ℂ (extendZero φ z) = extendZero φ.conjC z := by
  by_cases hz : z ∈ H
  · rw [extendZero_apply_of_mem _ hz, extendZero_apply_of_mem _ hz, conjC_apply]
  · rw [extendZero_apply_of_not_mem _ hz, extendZero_apply_of_not_mem _ hz, map_zero]

/-- Complex conjugation commutes with induction.  MathComp: `conj_cfInd`
(`classfun.v`; used in the proof of Peterfalvi (1.5)(e)). -/
theorem conjC_ind [Fintype G] (φ : ClassFunction H) : (ind H φ).conjC = ind H φ.conjC :=
  ext fun x => by
    rw [conjC_apply, ind_apply, ind_apply, map_mul, map_inv₀, map_natCast, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun y _ => extendZero_conjC φ _

end ClassFunction

/-! ### Precomposition with a monoid isomorphism preserves irreducibility -/

section CompMulEquiv

variable {A W : Type*} [Semiring A] [AddCommMonoid W] [Module A W]
variable {G₁ G₂ : Type*} [Monoid G₁] [Monoid G₂]

/-- Precomposing a representation with a monoid isomorphism leaves its lattice of
subrepresentations unchanged (a subspace is invariant under `ρ ∘ e` iff it is invariant
under `ρ`, since `e` is surjective).

This is the `MulEquiv` case of the order isomorphism inlined in
`Representation.isIrreducible_comp_iff` (`AbelemRepr.lean`); it is restated here
because importing the BG-lane `AbelemRepr.lean` (and its `CoprimeAction` import chain
with priority-100 global instances) into the PF character-theory lane for one lemma
would invert the layering.  Consolidating the two into a shared low-level home is on
the deferred list (M6 Task 1 report). -/
def Subrepresentation.orderIsoCompMulEquiv (ρ : Representation A G₂ W) (e : G₁ ≃* G₂) :
    Subrepresentation (ρ.comp e.toMonoidHom) ≃o Subrepresentation ρ where
  toFun σ := ⟨σ.toSubmodule, fun g v hv => by
    have hmem := σ.apply_mem_toSubmodule (e.symm g) hv
    simpa using hmem⟩
  invFun σ := ⟨σ.toSubmodule, fun g v hv => σ.apply_mem_toSubmodule (e g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Precomposition with a monoid isomorphism preserves irreducibility of a
representation.  The transport engine behind `Irr.conjg`; the `MulEquiv` case of
`Representation.isIrreducible_comp_iff` (`AbelemRepr.lean` — see
`Subrepresentation.orderIsoCompMulEquiv` for why it is not imported). -/
theorem Representation.IsIrreducible.compMulEquiv {ρ : Representation k G₂ V}
    (hρ : ρ.IsIrreducible) (e : G₁ ≃* G₂) :
    Representation.IsIrreducible (ρ.comp e.toMonoidHom) :=
  (Subrepresentation.orderIsoCompMulEquiv ρ e).isSimpleOrder_iff.mpr hρ

end CompMulEquiv

/-! ### `G` acts on the irreducible characters of a normal subgroup -/

namespace Irr

variable {H : Subgroup G} [hH : H.Normal] [Fintype H]

/-- The conjugate of an irreducible character of a normal subgroup `H ⊴ G` by `g : G` is
again an irreducible character: `Irr.conjg` is the action of `G` on `Irr H` underlying
Clifford theory.  Irreducibility of the conjugate transports along
`Representation.IsIrreducible.compMulEquiv` applied to the conjugation automorphism
`(MulAut.conjNormal g).symm` of `H`.  MathComp: `conjg_Iirr` (with `cfConjg_irr`)
(`inertia.v`). -/
def conjg (θ : Irr H) (g : G) : Irr H where
  toClassFunction := ClassFunction.conjg (θ : ClassFunction H) g
  exists_simple' := by
    obtain ⟨N, hN, hθN⟩ := θ.exists_simple'
    haveI hirr : (Representation.ofModule' (k := ℂ) (G := H) N).IsIrreducible :=
      MonoidAlgebra.isIrreducible_ofModule' N hN
    haveI hirr' : Representation.IsIrreducible
        ((Representation.ofModule' (k := ℂ) (G := H) N).comp
          ((MulAut.conjNormal g).symm : H ≃* H).toMonoidHom) :=
      Representation.IsIrreducible.compMulEquiv hirr _
    obtain ⟨χ', hχ'⟩ := Representation.exists_irr_classFunction_eq
      ((Representation.ofModule' (k := ℂ) (G := H) N).comp
        ((MulAut.conjNormal g).symm : H ≃* H).toMonoidHom)
    obtain ⟨N', hN', hval⟩ := χ'.exists_simple'
    refine ⟨N', hN', ?_⟩
    rw [← hval, hχ']
    ext h
    rw [ClassFunction.conjg_apply, Representation.classFunction_apply, hθN]
    rfl

@[simp]
theorem coe_conjg (θ : Irr H) (g : G) :
    ((θ.conjg g : Irr H) : ClassFunction H) = ClassFunction.conjg (θ : ClassFunction H) g :=
  rfl

theorem conjg_apply (θ : Irr H) (g : G) (h : H) :
    θ.conjg g h = θ ((MulAut.conjNormal g).symm h) :=
  rfl

/-- Evaluation of a conjugated irreducible character, explicit form.
MathComp: `conjg_IirrE` with `cfConjgE` (`inertia.v`). -/
theorem conjg_apply_mk (θ : Irr H) (g : G) (h : H) (hmem : g⁻¹ * ↑h * g ∈ H) :
    θ.conjg g h = θ ⟨g⁻¹ * ↑h * g, hmem⟩ :=
  ClassFunction.conjg_apply_mk (θ : ClassFunction H) g h hmem

@[simp]
theorem conjg_one (θ : Irr H) : θ.conjg (1 : G) = θ :=
  toClassFunction_injective (ClassFunction.conjg_one _)

/-- The left-action law on `Irr H`.  MathComp: `cfConjgM` at `Iirr` level
(`inertia.v`); see the module docstring for the convention. -/
theorem conjg_mul (θ : Irr H) (a b : G) : θ.conjg (a * b) = (θ.conjg b).conjg a :=
  toClassFunction_injective (ClassFunction.conjg_mul _ a b)

@[simp]
theorem conjg_conjg_inv (θ : Irr H) (g : G) : (θ.conjg g).conjg g⁻¹ = θ :=
  toClassFunction_injective (ClassFunction.conjg_conjg_inv _ g)

@[simp]
theorem conjg_inv_conjg (θ : Irr H) (g : G) : (θ.conjg g⁻¹).conjg g = θ :=
  toClassFunction_injective (ClassFunction.conjg_inv_conjg _ g)

theorem conjg_injective (g : G) :
    Function.Injective fun θ : Irr H => θ.conjg g := fun θ ξ h => by
  have h2 : (θ.conjg g).conjg g⁻¹ = (ξ.conjg g).conjg g⁻¹ := congrArg (conjg · g⁻¹) h
  simpa using h2

/-- Conjugation by `g` permutes the irreducible characters of `H`.
MathComp: injectivity/bijectivity of `conjg_Iirr` (`inertia.v`). -/
theorem conjg_bijective (g : G) :
    Function.Bijective fun θ : Irr H => θ.conjg g :=
  ⟨conjg_injective g, fun θ => ⟨θ.conjg g⁻¹, conjg_inv_conjg θ g⟩⟩

theorem conjg_eq_self_of_mem (θ : Irr H) {g : G} (hg : g ∈ H) : θ.conjg g = θ :=
  toClassFunction_injective (ClassFunction.conjg_eq_self_of_mem _ hg)

/-- Complex conjugation commutes with the conjugation action on `Irr H`.
MathComp: `conj_cfConjg` at `Iirr` level (`inertia.v`). -/
theorem conj_conjg (θ : Irr H) (g : G) : (θ.conjg g).conj = θ.conj.conjg g :=
  toClassFunction_injective (ClassFunction.conjC_conjg _ g)

/-- The inertia subgroup of an irreducible character.
MathComp: `'I_G['chi_t]` (`inertia.v`). -/
def inertia (θ : Irr H) : Subgroup G :=
  ClassFunction.inertia (θ : ClassFunction H)

theorem mem_inertia {θ : Irr H} {g : G} : g ∈ θ.inertia ↔ θ.conjg g = θ := by
  constructor
  · intro h
    exact toClassFunction_injective h
  · intro h
    exact congrArg toClassFunction h

/-- `H` is contained in the inertia subgroup of each of its irreducible characters.
MathComp: `sub_Inertia` (`inertia.v`). -/
theorem le_inertia (θ : Irr H) : H ≤ θ.inertia :=
  ClassFunction.le_inertia _

/-- Two conjugates of an irreducible character agree iff the conjugating elements lie in
the same left coset of the inertia subgroup.  MathComp: `cfConjg_eqE` (`inertia.v`;
stated there with right cosets, per the opposite action convention). -/
theorem conjg_eq_conjg_iff {θ : Irr H} {x y : G} :
    θ.conjg x = θ.conjg y ↔ y⁻¹ * x ∈ θ.inertia := by
  rw [mem_inertia]
  constructor
  · intro h
    rw [conjg_mul, h, ← conjg_mul, inv_mul_cancel, conjg_one]
  · intro h
    have h2 : θ.conjg (y * (y⁻¹ * x)) = θ.conjg y := by rw [conjg_mul, h]
    rwa [show y * (y⁻¹ * x) = x by group] at h2

end Irr

/-! ### The conjugation orbit (`cfclass`) -/

namespace Irr

variable [Fintype G] {H : Subgroup G} [hH : H.Normal] [Fintype H]

open scoped Classical in
/-- The orbit of an irreducible character `θ` of `H ⊴ G` under `G`-conjugation, as a
`Finset (Irr H)`.  MathComp: `cfclass` / `('chi_t ^: G)%CF` (`inertia.v`; a
duplicate-free `seq` there). -/
def cfclass (θ : Irr H) : Finset (Irr H) :=
  Finset.image (fun g : G => θ.conjg g) Finset.univ

theorem mem_cfclass_iff {θ ξ : Irr H} : ξ ∈ θ.cfclass ↔ ∃ g : G, θ.conjg g = ξ := by
  classical
  simp [cfclass]

/-- MathComp: `cfclass_refl` (`inertia.v`). -/
theorem self_mem_cfclass (θ : Irr H) : θ ∈ θ.cfclass :=
  mem_cfclass_iff.mpr ⟨1, conjg_one θ⟩

theorem conjg_mem_cfclass (θ : Irr H) (g : G) : θ.conjg g ∈ θ.cfclass :=
  mem_cfclass_iff.mpr ⟨g, rfl⟩

/-- MathComp: `cfclass_sym` (`inertia.v`). -/
theorem mem_cfclass_symm {θ ξ : Irr H} (h : ξ ∈ θ.cfclass) : θ ∈ ξ.cfclass := by
  obtain ⟨g, rfl⟩ := mem_cfclass_iff.mp h
  exact mem_cfclass_iff.mpr ⟨g⁻¹, conjg_conjg_inv θ g⟩

/-- Conjugate irreducible characters have the same conjugation orbit.
MathComp: `cfclass_transr`-shaped (`inertia.v`). -/
theorem cfclass_eq_of_mem {θ ξ : Irr H} (h : ξ ∈ θ.cfclass) : ξ.cfclass = θ.cfclass := by
  obtain ⟨g, rfl⟩ := mem_cfclass_iff.mp h
  ext ζ
  rw [mem_cfclass_iff, mem_cfclass_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a * g, conjg_mul θ a g⟩
  · rintro ⟨b, rfl⟩
    refine ⟨b * g⁻¹, ?_⟩
    rw [← conjg_mul, inv_mul_cancel_right]

/-- The fiber of `x ↦ θ.conjg x` over any point of the orbit has the size of the
inertia subgroup (the fibers are the left cosets of `inertia θ`). -/
private theorem card_fiber_conjg (θ : Irr H) {ξ : Irr H} (hξ : ∃ g : G, θ.conjg g = ξ)
    [DecidablePred fun x : G => θ.conjg x = ξ] :
    ({x ∈ Finset.univ | θ.conjg x = ξ} : Finset G).card = Nat.card θ.inertia := by
  classical
  obtain ⟨x₀, rfl⟩ := hξ
  calc ({x ∈ Finset.univ | θ.conjg x = θ.conjg x₀} : Finset G).card
      = Fintype.card {x : G // θ.conjg x = θ.conjg x₀} := (Fintype.card_subtype _).symm
    _ = Nat.card {x : G // θ.conjg x = θ.conjg x₀} := Nat.card_eq_fintype_card.symm
    _ = Nat.card θ.inertia := Nat.card_congr
        { toFun := fun x => ⟨x₀⁻¹ * x.1, conjg_eq_conjg_iff.mp x.2⟩
          invFun := fun i => ⟨x₀ * i.1, conjg_eq_conjg_iff.mpr (by
            rw [inv_mul_cancel_left]
            exact i.2)⟩
          left_inv := fun x => Subtype.ext (mul_inv_cancel_left x₀ x.1)
          right_inv := fun i => Subtype.ext (inv_mul_cancel_left x₀ i.1) }

/-- **Orbit–stabilizer for conjugation orbits of irreducible characters**: the orbit of
`θ` has `(inertia θ).index` elements.  MathComp: `size_cfclass` (`inertia.v`). -/
theorem card_cfclass (θ : Irr H) : θ.cfclass.card = θ.inertia.index := by
  classical
  have himage : Finset.univ.image (fun x : G => θ.conjg x) = θ.cfclass :=
    Finset.ext fun ξ => by
      rw [Finset.mem_image, mem_cfclass_iff]
      simp
  have hfib := Finset.card_eq_sum_card_image (fun x : G => θ.conjg x)
    (Finset.univ : Finset G)
  rw [himage, Finset.sum_congr rfl fun ξ hξ =>
      card_fiber_conjg θ (mem_cfclass_iff.mp hξ),
    Finset.sum_const, smul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card] at hfib
  have hIndex : Nat.card θ.inertia * θ.inertia.index = Nat.card G :=
    Subgroup.card_mul_index θ.inertia
  have hpos : 0 < Nat.card θ.inertia := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← hfib, ← hIndex]
  exact Nat.mul_comm _ _

end Irr

/-! ### Clifford theory at the character level -/

namespace Irr

variable [Fintype G] {H : Subgroup G} [hH : H.Normal] [Fintype H]

/-- **The restriction of an induced irreducible character is the scaled orbit sum**:
`'Res[H] ('Ind[G] θ) = |I_G(θ) : H| • ∑_{ξ ∈ θ ^: G} ξ` for `H ⊴ G`.  Proved by direct
computation with the averaging formula, fibering the sum over `G` by the conjugated
character.  This is the engine behind Peterfalvi (1.5)(a); MathComp:
`cfResInd_sum_cfclass` (`PFsection1.v`), stated here at `inertia.v` strength. -/
theorem res_ind_eq_smul_sum_cfclass (θ : Irr H) :
    ClassFunction.res H (ClassFunction.ind H (θ : ClassFunction H))
      = (H.relIndex θ.inertia : ℂ) • ∑ ξ ∈ θ.cfclass, (ξ : ClassFunction H) := by
  classical
  -- each summand of the averaging formula is a conjugated character value
  have hterm : ∀ (x : G) (h : H),
      ClassFunction.extendZero (θ : ClassFunction H) (x⁻¹ * ↑h * x) = θ.conjg x h := by
    intro x h
    have hmem : x⁻¹ * ↑h * x ∈ H := by
      have hconj := hH.conj_mem _ h.2 x⁻¹
      rwa [inv_inv] at hconj
    rw [ClassFunction.extendZero_apply_of_mem _ hmem, conjg_apply_mk θ x h hmem]
    rfl
  -- `res (ind θ)` is the `|H|⁻¹`-scaled sum of all `G`-conjugates of `θ`
  have hres : ClassFunction.res H (ClassFunction.ind H (θ : ClassFunction H))
      = (Nat.card H : ℂ)⁻¹ • ∑ x : G, ((θ.conjg x : Irr H) : ClassFunction H) := by
    ext h
    rw [ClassFunction.res_apply, ClassFunction.ind_apply, ClassFunction.smul_apply,
      ClassFunction.sum_apply, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun x _ => hterm x h
  -- fiber the sum over `G` by the conjugated character (orbit–stabilizer)
  have himage : Finset.univ.image (fun x : G => θ.conjg x) = θ.cfclass :=
    Finset.ext fun ξ => by
      rw [Finset.mem_image, mem_cfclass_iff]
      simp
  have hsum : ∑ x : G, ((θ.conjg x : Irr H) : ClassFunction H)
      = (Nat.card θ.inertia) • ∑ ξ ∈ θ.cfclass, (ξ : ClassFunction H) := by
    have hcomp := Finset.sum_comp (s := (Finset.univ : Finset G))
      (fun ξ : Irr H => (ξ : ClassFunction H)) (fun x : G => θ.conjg x)
    rw [himage] at hcomp
    rw [hcomp, Finset.smul_sum]
    exact Finset.sum_congr rfl fun ξ hξ => by
      rw [card_fiber_conjg θ (mem_cfclass_iff.mp hξ)]
  rw [hres, hsum, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  -- `|H|⁻¹ * |I_G(θ)| = |I_G(θ) : H|`
  have h2 : Nat.card (H.subgroupOf θ.inertia) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe θ.le_inertia).toEquiv
  have hcards : Nat.card θ.inertia = H.relIndex θ.inertia * Nat.card H := by
    have h1 : Nat.card (H.subgroupOf θ.inertia) * (H.subgroupOf θ.inertia).index
        = Nat.card θ.inertia := Subgroup.card_mul_index (H.subgroupOf θ.inertia)
    rw [← h1, h2, mul_comm]
    rfl
  have hH0 : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [inv_mul_eq_iff_eq_mul₀ hH0, mul_comm]
  exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) hcards

/-- `⟪'Res[H] ('Ind[G] θ), θ⟫ = |I_G(θ) : H|` — the `⟪res (ind θ), θ⟫`-fact from which
PF (1.5)(b) (`cfnorm_Ind_irr`) follows by Frobenius reciprocity.  MathComp:
`cfdot_Res_Ind`-shaped consequence of `cfResInd_sum_cfclass`. -/
theorem cfInner_res_ind_self (θ : Irr H) :
    ⟪ClassFunction.res H (ClassFunction.ind H (θ : ClassFunction H)),
        (θ : ClassFunction H)⟫_[H]
      = (H.relIndex θ.inertia : ℂ) := by
  classical
  have hterm : ∀ ξ : Irr H,
      ⟪(ξ : ClassFunction H), (θ : ClassFunction H)⟫_[H]
        = if ξ = θ then (1 : ℂ) else 0 := fun ξ => Irr.cfInner_eq ξ θ
  rw [θ.res_ind_eq_smul_sum_cfclass, ClassFunction.cfInner_smul_left,
    ClassFunction.cfInner_sum_left, Finset.sum_congr rfl fun ξ _ => hterm ξ,
    Finset.sum_ite_eq_of_mem' _ _ _ (self_mem_cfclass θ), mul_one]

/-- **The irreducible constituents of a restriction lie in a single conjugation
orbit**: if `θ` and `θ'` are both constituents of `'Res[H] χ`, then `θ'` is
`G`-conjugate to `θ`.  Clifford's theorem, constituent form; MathComp: the
`cfclass`-membership content of `Clifford_Res_sum_cfclass` (`inertia.v`). -/
theorem mem_cfclass_of_cfInner_res_ne_zero (χ : Irr G) {θ θ' : Irr H}
    (hθ : ⟪ClassFunction.res H (χ : ClassFunction G), (θ : ClassFunction H)⟫_[H] ≠ 0)
    (hθ' : ⟪ClassFunction.res H (χ : ClassFunction G), (θ' : ClassFunction H)⟫_[H] ≠ 0) :
    θ' ∈ θ.cfclass := by
  classical
  by_contra hnot
  -- orthogonality of `θ'` to the orbit of `θ` forces `⟪res (ind θ), θ'⟫ = 0` …
  have hterm : ∀ ξ : Irr H,
      ⟪(ξ : ClassFunction H), (θ' : ClassFunction H)⟫_[H]
        = if ξ = θ' then (1 : ℂ) else 0 := fun ξ => Irr.cfInner_eq ξ θ'
  have hzero : ⟪ClassFunction.res H (ClassFunction.ind H (θ : ClassFunction H)),
      (θ' : ClassFunction H)⟫_[H] = 0 := by
    rw [θ.res_ind_eq_smul_sum_cfclass, ClassFunction.cfInner_smul_left,
      ClassFunction.cfInner_sum_left, Finset.sum_congr rfl fun ξ _ => hterm ξ,
      Finset.sum_ite_eq' θ.cfclass θ' _, if_neg hnot, mul_zero]
  -- … but expanding `ind θ` into irreducible characters bounds it below by
  -- `⟪ind θ, χ⟫ * ⟪res χ, θ'⟫ > 0`.
  have hindχ : ⟪ClassFunction.ind H (θ : ClassFunction H), (χ : ClassFunction G)⟫_[G]
      ≠ 0 := by
    rw [ClassFunction.cfInner_ind_eq_cfInner_res]
    intro h0
    exact hθ (by rw [ClassFunction.cfInner_conj_symm, h0, map_zero])
  obtain ⟨n, hn⟩ := (Irr.isChar θ).ind (H := H)
  have hcoefχ : ⟪ClassFunction.ind H (θ : ClassFunction H), (χ : ClassFunction G)⟫_[G]
      = (n χ : ℂ) := by
    have hterm2 : ∀ ψ : Irr G,
        ⟪(n ψ : ℂ) • (ψ : ClassFunction G), (χ : ClassFunction G)⟫_[G]
          = if ψ = χ then (n ψ : ℂ) else 0 := by
      intro ψ
      rw [ClassFunction.cfInner_smul_left, Irr.cfInner_eq, mul_ite, mul_one, mul_zero]
    rw [hn, ClassFunction.cfInner_sum_left, Finset.sum_congr rfl fun ψ _ => hterm2 ψ,
      Finset.sum_ite_eq' Finset.univ χ _, if_pos (Finset.mem_univ χ)]
  choose m hm using fun ψ : Irr G =>
    ((Irr.isChar ψ).res (H := H)).cfInner_mem_nat θ'
  have hcalc : ⟪ClassFunction.res H (ClassFunction.ind H (θ : ClassFunction H)),
      (θ' : ClassFunction H)⟫_[H] = ((∑ ψ : Irr G, n ψ * m ψ : ℕ) : ℂ) := by
    have hterm3 : ∀ ψ : Irr G,
        ⟪ClassFunction.res H ((n ψ : ℂ) • (ψ : ClassFunction G)),
            (θ' : ClassFunction H)⟫_[H]
          = (n ψ : ℂ) * (m ψ : ℂ) := by
      intro ψ
      rw [map_smul, ClassFunction.cfInner_smul_left, hm ψ]
    conv_lhs => rw [hn, map_sum]
    rw [ClassFunction.cfInner_sum_left, Finset.sum_congr rfl fun ψ _ => hterm3 ψ]
    push_cast
    ring
  rw [hzero] at hcalc
  have hsum0 : (∑ ψ : Irr G, n ψ * m ψ) = 0 := by exact_mod_cast hcalc.symm
  have hterm0 := (Finset.sum_eq_zero_iff_of_nonneg fun ψ _ => Nat.zero_le _).mp hsum0
    χ (Finset.mem_univ χ)
  rcases Nat.mul_eq_zero.mp hterm0 with hn0 | hm0
  · exact hindχ (by rw [hcoefχ, hn0, Nat.cast_zero])
  · exact hθ' (by rw [hm χ, hm0, Nat.cast_zero])

/-- **Clifford's theorem at the character level**: if `θ` is an irreducible constituent
of `'Res[H] χ` (for `H ⊴ G`, `χ ∈ Irr G`), then
`'Res[H] χ = ⟪'Res[H] χ, θ⟫ • ∑_{ξ ∈ θ ^: G} ξ` — the restriction is the common
multiplicity times the orbit sum.  MathComp: `Clifford_Res_sum_cfclass`
(`inertia.v`). -/
theorem res_eq_cfInner_smul_sum_cfclass (χ : Irr G) (θ : Irr H)
    (hθ : ⟪ClassFunction.res H (χ : ClassFunction G), (θ : ClassFunction H)⟫_[H] ≠ 0) :
    ClassFunction.res H (χ : ClassFunction G)
      = ⟪ClassFunction.res H (χ : ClassFunction G), (θ : ClassFunction H)⟫_[H]
          • ∑ ξ ∈ θ.cfclass, (ξ : ClassFunction H) := by
  classical
  -- the multiplicity is constant along the orbit
  have hconst : ∀ ξ ∈ θ.cfclass,
      ⟪ClassFunction.res H (χ : ClassFunction G), (ξ : ClassFunction H)⟫_[H]
        = ⟪ClassFunction.res H (χ : ClassFunction G), (θ : ClassFunction H)⟫_[H] := by
    intro ξ hξ
    obtain ⟨g, rfl⟩ := mem_cfclass_iff.mp hξ
    conv_lhs => rw [← ClassFunction.conjg_res (χ : ClassFunction G) g]
    rw [coe_conjg, ClassFunction.cfInner_conjg]
  -- constituents off the orbit vanish
  have hvanish : ∀ ξ ∈ (Finset.univ : Finset (Irr H)), ξ ∉ θ.cfclass →
      ⟪ClassFunction.res H (χ : ClassFunction G), (ξ : ClassFunction H)⟫_[H]
        • (ξ : ClassFunction H) = 0 := by
    intro ξ _ hξ
    have h0 : ⟪ClassFunction.res H (χ : ClassFunction G), (ξ : ClassFunction H)⟫_[H]
        = 0 := by
      by_contra hne
      exact hξ (mem_cfclass_of_cfInner_res_ne_zero χ hθ hne)
    rw [h0, zero_smul]
  calc ClassFunction.res H (χ : ClassFunction G)
      = ∑ ξ : Irr H,
          ⟪ClassFunction.res H (χ : ClassFunction G), (ξ : ClassFunction H)⟫_[H]
            • (ξ : ClassFunction H) :=
        ClassFunction.eq_sum_cfInner_smul _
    _ = ∑ ξ ∈ θ.cfclass,
          ⟪ClassFunction.res H (χ : ClassFunction G), (ξ : ClassFunction H)⟫_[H]
            • (ξ : ClassFunction H) :=
        (Finset.sum_subset (Finset.subset_univ θ.cfclass) hvanish).symm
    _ = ∑ ξ ∈ θ.cfclass,
          ⟪ClassFunction.res H (χ : ClassFunction G), (θ : ClassFunction H)⟫_[H]
            • (ξ : ClassFunction H) :=
        Finset.sum_congr rfl fun ξ hξ => by rw [hconst ξ hξ]
    _ = ⟪ClassFunction.res H (χ : ClassFunction G), (θ : ClassFunction H)⟫_[H]
          • ∑ ξ ∈ θ.cfclass, (ξ : ClassFunction H) :=
        (Finset.smul_sum).symm

/-- Induction is constant on conjugation orbits: conjugate irreducible characters of
`H ⊴ G` induce the same class function on `G`.  MathComp: `cfclass_Ind`
(`inertia.v`). -/
theorem ind_eq_of_mem_cfclass {θ ξ : Irr H} (h : ξ ∈ θ.cfclass) :
    ClassFunction.ind H (ξ : ClassFunction H)
      = ClassFunction.ind H (θ : ClassFunction H) := by
  obtain ⟨g, rfl⟩ := mem_cfclass_iff.mp h
  rw [coe_conjg]
  exact ClassFunction.ind_conjg _ g

end Irr

/-! ### Smoke examples: the PF1 (1.5)-region hypothesis shapes

Statement-shape checks against the consumption sites in `PFsection1.v:150-360`
(kept as documentation, per the M6 Task 1 dispatch). -/

section SmokeExamples

variable {G : Type u} [Group G] [Fintype G] {H : Subgroup G} [H.Normal] [Fintype H]

/-- Peterfalvi (1.5)(a) shape (`cfResInd_sum_cfclass`):
`'Res[H] ('Ind[G] 'chi_t) = #|'I_G['chi_t] : H|%:R *: \sum_(xi <- 'chi_t ^: G) xi`. -/
example (θ : Irr H) :
    ClassFunction.res H (ClassFunction.ind H (θ : ClassFunction H))
      = (H.relIndex θ.inertia : ℂ) • ∑ ξ ∈ θ.cfclass, (ξ : ClassFunction H) :=
  θ.res_ind_eq_smul_sum_cfclass

/-- The Clifford hypothesis shape of the (1.7)(b) proof (`Clifford_Res_sum_cfclass`
applied to `psi1Hs : s \in irr_constt ('Res psi1)`): a nonvanishing constituent
multiplicity yields the orbit-sum decomposition of the restriction. -/
example (χ : Irr G) (θ : Irr H)
    (hθ : ⟪ClassFunction.res H (χ : ClassFunction G), (θ : ClassFunction H)⟫_[H] ≠ 0) :
    ClassFunction.res H (χ : ClassFunction G)
      = ⟪ClassFunction.res H (χ : ClassFunction G), (θ : ClassFunction H)⟫_[H]
          • ∑ ξ ∈ θ.cfclass, (ξ : ClassFunction H) :=
  Irr.res_eq_cfInner_smul_sum_cfclass χ θ hθ

/-- The PFsection2 hypothesis shape (`cfInd_on`): an `A`-supported class function of
`L` induces a class function of `G` supported on the class support of `A`
(`alpha \in 'CF(L, A) -> 'Ind[G] alpha \in 'CF(G, class_support A G)`). -/
example (L : Subgroup G) [Fintype L] (A : Set L) (α : ClassFunction L)
    (hα : α ∈ ClassFunction.supportedOn L A) :
    ClassFunction.ind L α
      ∈ ClassFunction.supportedOn G (Group.conjugatesOfSet (((↑) : L → G) '' A)) :=
  ClassFunction.ind_mem_supportedOn_conjugatesOfSet L hα

end SmokeExamples
