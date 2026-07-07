/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
-- `Mathlib.GroupTheory.Rank` is needed for `Subgroup.nat_card_centralizer_nat_card_stabilizer`
-- (used in `ConjClasses.nat_card_carrier_mul_card_centralizer`), which happens to live there.
import Mathlib.GroupTheory.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Class functions and the orthogonality relations for complex characters

This file develops the theory of complex-valued class functions on a finite group `G` and the
character theory built on top of them: the first orthogonality relation restated for the
hermitian inner product, the completeness of irreducible characters
(`#Irr G = #ConjClasses G`), and the second orthogonality relation.  It is the foundational
interface for the character-theoretic half (M2 onwards) of the odd-order port, corresponding
to MathComp's `classfun.v` and the orthogonality material of `character.v`.

## Main definitions

* `ClassFunction G`: bundled complex-valued functions on `G` that are constant on conjugacy
  classes, a `ℂ`-module with `FunLike`.  MathComp: `'CF(G)` / `classfun`.
* `ClassFunction.cfInner φ ψ`, notation `⟪φ, ψ⟫_[G]` (scoped in `ClassFunction`):
  the hermitian inner product `(#G)⁻¹ * ∑ g, φ g * conj (ψ g)`.  MathComp: `'[phi, psi]`,
  `cfdot`.  It is ℂ-linear in the *first* argument and conjugate-linear in the second.
* `ClassFunction.supportedOn A`: the subspace of class functions vanishing off `A`.
  MathComp: `'CF(G, A)`.
* `Representation.classFunction` / `FDRep.classFunction`: the character of a
  finite-dimensional representation, bundled as a class function (built on
  `Representation.character` / `FDRep.character`, not forked).
* `MonoidAlgebra.moduleCharacter M`: the character of a `MonoidAlgebra ℂ G`-module.
* `Irr G`: the irreducible characters of `G`, as a bundled structure wrapping a
  `ClassFunction` that is the character of some simple module over `MonoidAlgebra ℂ G`.
  MathComp: `irr G`.

## Main results

* `Representation.char_inv`, `FDRep.char_inv`: `χ(g⁻¹) = conj (χ g)` for characters of
  finite groups over `ℂ` (via the projections onto eigenspaces of `ρ g`, which are
  polynomials in `ρ g`; no inner-product-space machinery).
* `Irr.cfInner_eq`: **first orthogonality**, `⟪χ, ψ⟫_[G] = if χ = ψ then 1 else 0` for
  irreducible characters; `FDRep.cfInner_classFunction` is the `FDRep`-language version.
* `MonoidAlgebra.centerEquivClassFunction`: the center of the group algebra is isomorphic to
  the space of class functions; `MonoidAlgebra.finrank_center` computes its dimension as the
  number of conjugacy classes.
* `Irr.card_eq_card_conjClasses`: **completeness**, `#Irr G = #ConjClasses G`.
  MathComp: `NirrE`/`card_irr`.
* `Irr.basis`: the irreducible characters form a basis of `ClassFunction G`, with the
  expansion `ClassFunction.eq_sum_cfInner_smul` (`f = ∑ χ, ⟪f, χ⟫ • χ`; MathComp
  `cfun_sum_cfdot`).
* `Irr.second_orthogonality`: **second orthogonality**,
  `∑ χ : Irr G, χ g * conj (χ h) = if IsConj g h then #C_G(g) else 0`.

## Design notes

* **Bundled structure.** `ClassFunction G` is a structure (not a subtype of `G → ℂ` and not a
  submodule of `Rep`-morphisms) so that downstream Peterfalvi-style arguments can state
  hypotheses like `φ ∈ supportedOn A` and manipulate `φ` with `FunLike` directly.
* **`Fintype.card` convention.** Following `Mathlib.RepresentationTheory.Character`, the
  inner product uses `[Fintype G]` and `∑ g : G` with `(Fintype.card G : ℂ)⁻¹`.  Statements
  that only count things use the instance-free `Nat.card` (e.g. the centralizer in
  `Irr.second_orthogonality`); `Nat.card_eq_fintype_card` converts.
* **No `InnerProductSpace` instance.** `cfInner` is a plain definition with scoped notation.
  A full `InnerProductSpace` instance would drag in norms and topology that nothing in the
  port needs yet; it can be added later without changing this interface.
* **Coercion.** `Irr G` coerces to `ClassFunction G` (via `Irr.toClassFunction`, mirroring
  the `Sylow → Subgroup` coercion); new (M2+) statements should use the coercion `↑χ`,
  while pre-existing statements keep the explicit `.toClassFunction` spelling.
* **Irreducibility via the group algebra.** `Irr G` is defined through simple submodules of
  `MonoidAlgebra ℂ G` (every simple module is isomorphic to one, so this is no loss:
  `Representation.exists_irr_classFunction_eq` recovers arbitrary irreducible representations).
  This keeps the completeness proof self-contained: it needs Schur's lemma
  (`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`), Maschke's theorem
  (`IsSemisimpleModule (MonoidAlgebra ℂ G) _`), and the center of the group algebra —
  but *not* the Wedderburn pi-of-matrix-algebras decomposition nor any categorical
  transport of `CategoryTheory.Simple` between `FDRep` and module categories.
  The bridge to `Representation.IsIrreducible` is `MonoidAlgebra.isIrreducible_ofModule'`
  (Mathlib's `isSimpleModule_iff_irreducible_ofModule`), and Mathlib's
  `Representation.char_orthonormal` supplies orthonormality.
* **Completeness route.** `#Irr ≤ #classes` is linear independence (orthonormality).
  For `#Irr ≥ #classes`, the pairing `f ↦ (χ ↦ ∑ g, χ g * f g⁻¹)` is injective on
  `ClassFunction G`: if all pairings vanish, then `z := ∑ g, f g⁻¹ • single g 1` is a
  central element of `MonoidAlgebra ℂ G` acting by a trace-zero scalar (Schur) on every
  simple submodule, hence acting by zero; semisimplicity makes the simple submodules span,
  so `z = z * 1 = 0` and `f = 0`.
* **Second orthogonality route.** Instead of the character-table matrix identity
  (`Matrix.mul_eq_one_comm` after reindexing along `Irr G ≃ ConjClasses G`), we expand the
  indicator function of the conjugacy class of `h` in the basis `Irr.basis` and evaluate at
  `g`.  This uses completeness through the basis in the same essential way, avoids matrix
  reindexing, and yields the expansion lemma `ClassFunction.eq_sum_cfInner_smul` as
  independently useful API.

## TODO (M2 follow-ups, not this file)

* Class sums as an explicit basis of the center (integrality arguments for Burnside).
* Degrees `χ 1`, the regular character, induction/restriction, `⊗`-products of characters.
-/

noncomputable section

open Finset LinearMap Module

universe u

/-- A **class function** on a group `G` is a complex-valued function that is constant on
conjugacy classes.  MathComp: `classfun`, `'CF(G)`. -/
structure ClassFunction (G : Type u) [Group G] where
  /-- The underlying function `G → ℂ`. -/
  toFun : G → ℂ
  /-- The defining conjugation-invariance property.  Use `ClassFunction.conj_apply` instead. -/
  conj_invariant' : ∀ g h : G, toFun (h * g * h⁻¹) = toFun g

namespace ClassFunction

variable {G : Type u} [Group G]

instance : FunLike (ClassFunction G) G ℂ where
  coe := toFun
  coe_injective φ ψ h := by cases φ; cases ψ; congr

@[ext]
theorem ext {φ ψ : ClassFunction G} (h : ∀ g, φ g = ψ g) : φ = ψ :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_mk (f : G → ℂ) (hf) : ⇑(⟨f, hf⟩ : ClassFunction G) = f :=
  rfl

@[simp]
theorem conj_apply (φ : ClassFunction G) (g h : G) : φ (h * g * h⁻¹) = φ g :=
  φ.conj_invariant' g h

theorem mul_comm_apply (φ : ClassFunction G) (g h : G) : φ (g * h) = φ (h * g) := by
  have := φ.conj_apply (g * h) h
  rw [show h * (g * h) * h⁻¹ = h * g by group] at this
  exact this.symm

theorem apply_eq_of_isConj (φ : ClassFunction G) {g h : G} (hc : IsConj g h) : φ g = φ h := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  rw [← hc, conj_apply]

/-! ### Module structure -/

instance : Zero (ClassFunction G) := ⟨⟨0, fun _ _ => rfl⟩⟩
instance : Add (ClassFunction G) :=
  ⟨fun φ ψ => ⟨⇑φ + ⇑ψ, fun g h => by simp⟩⟩
instance : Neg (ClassFunction G) := ⟨fun φ => ⟨-⇑φ, fun g h => by simp⟩⟩
instance : Sub (ClassFunction G) :=
  ⟨fun φ ψ => ⟨⇑φ - ⇑ψ, fun g h => by simp⟩⟩
instance {S : Type*} [SMulZeroClass S ℂ] : SMul S (ClassFunction G) :=
  ⟨fun c φ => ⟨c • ⇑φ, fun g h => by simp⟩⟩

@[simp] theorem coe_zero : ⇑(0 : ClassFunction G) = 0 := rfl
@[simp] theorem coe_add (φ ψ : ClassFunction G) : ⇑(φ + ψ) = ⇑φ + ⇑ψ := rfl
@[simp] theorem coe_neg (φ : ClassFunction G) : ⇑(-φ) = -⇑φ := rfl
@[simp] theorem coe_sub (φ ψ : ClassFunction G) : ⇑(φ - ψ) = ⇑φ - ⇑ψ := rfl
@[simp] theorem coe_smul {S : Type*} [SMulZeroClass S ℂ] (c : S) (φ : ClassFunction G) :
    ⇑(c • φ) = c • ⇑φ := rfl

theorem zero_apply (g : G) : (0 : ClassFunction G) g = 0 := rfl
theorem add_apply (φ ψ : ClassFunction G) (g : G) : (φ + ψ) g = φ g + ψ g := rfl
theorem smul_apply {S : Type*} [SMulZeroClass S ℂ] (c : S) (φ : ClassFunction G) (g : G) :
    (c • φ) g = c • φ g := rfl

instance : AddCommGroup (ClassFunction G) :=
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

/-- The coercion to functions as an additive monoid homomorphism. -/
def coeHom : ClassFunction G →+ (G → ℂ) where
  toFun := (⇑)
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℂ (ClassFunction G) :=
  DFunLike.coe_injective.module ℂ coeHom fun _ _ => rfl

@[simp]
theorem coe_sum {ι : Type*} (s : Finset ι) (f : ι → ClassFunction G) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) :=
  map_sum coeHom f s

theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → ClassFunction G) (g : G) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
  simp

/-! ### Class functions are functions on the conjugacy classes -/

/-- Class functions are exactly the functions on the set of conjugacy classes.  This is the
dimension count behind completeness: `finrank ℂ (ClassFunction G) = #ConjClasses G`. -/
def equivFunConjClasses : ClassFunction G ≃ₗ[ℂ] (ConjClasses G → ℂ) where
  toFun φ c := Quotient.liftOn c ⇑φ fun _ _ h => φ.apply_eq_of_isConj h
  invFun F :=
    ⟨fun g => F (ConjClasses.mk g), fun g h => by
      congr 1
      rw [ConjClasses.mk_eq_mk_iff_isConj]
      exact (isConj_iff.mpr ⟨h, rfl⟩).symm⟩
  map_add' φ ψ := by
    funext c
    induction c using Quotient.inductionOn with
    | h g => simp
  map_smul' c φ := by
    funext d
    induction d using Quotient.inductionOn with
    | h g => simp
  left_inv φ := by ext g; rfl
  right_inv F := by
    funext c
    induction c using Quotient.inductionOn with
    | h g => rfl

@[simp]
theorem equivFunConjClasses_apply_mk (φ : ClassFunction G) (g : G) :
    equivFunConjClasses φ (ConjClasses.mk g) = φ g :=
  rfl

instance [Finite G] : FiniteDimensional ℂ (ClassFunction G) :=
  Module.Finite.equiv (equivFunConjClasses (G := G)).symm

theorem finrank_classFunction [Finite G] :
    Module.finrank ℂ (ClassFunction G) = Nat.card (ConjClasses G) := by
  have : Fintype (ConjClasses G) := Fintype.ofFinite _
  rw [(equivFunConjClasses (G := G)).finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]

/-! ### Class functions supported on a subset -/

variable (G) in
/-- The subspace of class functions vanishing outside `A`.  MathComp: `'CF(G, A)`. -/
def supportedOn (A : Set G) : Submodule ℂ (ClassFunction G) where
  carrier := {φ | ∀ g ∉ A, φ g = 0}
  add_mem' {φ ψ} hφ hψ g hg := by simp [add_apply, hφ g hg, hψ g hg]
  zero_mem' _ _ := rfl
  smul_mem' c φ hφ g hg := by simp [smul_apply, hφ g hg]

@[simp]
theorem mem_supportedOn {A : Set G} {φ : ClassFunction G} :
    φ ∈ supportedOn G A ↔ ∀ g ∉ A, φ g = 0 :=
  Iff.rfl

theorem supportedOn_univ (φ : ClassFunction G) : φ ∈ supportedOn G Set.univ :=
  fun g hg => absurd (Set.mem_univ g) hg

/-! ### The inner product -/

section CfInner

variable [Fintype G]

/-- The hermitian inner product of class functions,
`⟪φ, ψ⟫ = (#G)⁻¹ * ∑ g, φ g * conj (ψ g)`; it is ℂ-linear in the first argument and
conjugate-linear in the second.  MathComp: `cfdot`, `'[phi, psi]`. -/
def cfInner (φ ψ : ClassFunction G) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, φ g * starRingEnd ℂ (ψ g)

@[inherit_doc]
scoped notation "⟪" φ ", " ψ "⟫_[" G "]" => ClassFunction.cfInner (G := G) φ ψ

theorem cfInner_def (φ ψ : ClassFunction G) :
    ⟪φ, ψ⟫_[G] = (Fintype.card G : ℂ)⁻¹ * ∑ g : G, φ g * starRingEnd ℂ (ψ g) :=
  rfl

/-- The inner product with a fixed second argument, as a linear functional. -/
def cfInnerₗ (ψ : ClassFunction G) : ClassFunction G →ₗ[ℂ] ℂ where
  toFun φ := ⟪φ, ψ⟫_[G]
  map_add' φ φ' := by
    simp only [cfInner, add_apply, add_mul, sum_add_distrib, mul_add]
  map_smul' c φ := by
    simp only [cfInner, smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring

@[simp]
theorem cfInnerₗ_apply (φ ψ : ClassFunction G) : cfInnerₗ ψ φ = ⟪φ, ψ⟫_[G] :=
  rfl

theorem cfInner_add_left (φ φ' ψ : ClassFunction G) :
    ⟪φ + φ', ψ⟫_[G] = ⟪φ, ψ⟫_[G] + ⟪φ', ψ⟫_[G] :=
  map_add (cfInnerₗ ψ) φ φ'

theorem cfInner_smul_left (c : ℂ) (φ ψ : ClassFunction G) :
    ⟪c • φ, ψ⟫_[G] = c * ⟪φ, ψ⟫_[G] :=
  map_smul (cfInnerₗ ψ) c φ

theorem cfInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → ClassFunction G)
    (ψ : ClassFunction G) : ⟪∑ i ∈ s, f i, ψ⟫_[G] = ∑ i ∈ s, ⟪f i, ψ⟫_[G] :=
  map_sum (cfInnerₗ ψ) f s

theorem cfInner_conj_symm (φ ψ : ClassFunction G) :
    ⟪ψ, φ⟫_[G] = starRingEnd ℂ ⟪φ, ψ⟫_[G] := by
  simp only [cfInner, map_mul, map_inv₀, map_natCast, map_sum, Complex.conj_conj]
  exact congrArg _ (Finset.sum_congr rfl fun g _ => mul_comm _ _)

theorem cfInner_zero_left (ψ : ClassFunction G) : ⟪(0 : ClassFunction G), ψ⟫_[G] = 0 :=
  map_zero (cfInnerₗ ψ)

theorem cfInner_zero_right (φ : ClassFunction G) : ⟪φ, (0 : ClassFunction G)⟫_[G] = 0 := by
  rw [cfInner_conj_symm, cfInner_zero_left, map_zero]

theorem cfInner_add_right (φ ψ₁ ψ₂ : ClassFunction G) :
    ⟪φ, ψ₁ + ψ₂⟫_[G] = ⟪φ, ψ₁⟫_[G] + ⟪φ, ψ₂⟫_[G] := by
  rw [cfInner_conj_symm, cfInner_add_left, map_add, ← cfInner_conj_symm ψ₁ φ,
    ← cfInner_conj_symm ψ₂ φ]

theorem cfInner_smul_right (c : ℂ) (φ ψ : ClassFunction G) :
    ⟪φ, c • ψ⟫_[G] = starRingEnd ℂ c * ⟪φ, ψ⟫_[G] := by
  rw [cfInner_conj_symm, cfInner_smul_left, map_mul, ← cfInner_conj_symm ψ φ]

theorem cfInner_sum_right {ι : Type*} (s : Finset ι) (φ : ClassFunction G)
    (ψ : ι → ClassFunction G) : ⟪φ, ∑ i ∈ s, ψ i⟫_[G] = ∑ i ∈ s, ⟪φ, ψ i⟫_[G] := by
  rw [cfInner_conj_symm, cfInner_sum_left, map_sum]
  exact Finset.sum_congr rfl fun i _ => (cfInner_conj_symm (ψ i) φ).symm

end CfInner

end ClassFunction

/-! ### Characters as class functions -/

section Characters

variable {G : Type u} [Group G]

/-- The character of a finite-dimensional representation, as a bundled class function.
Builds on `Representation.character`. -/
def Representation.classFunction {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) : ClassFunction G :=
  ⟨ρ.character, ρ.char_conj⟩

@[simp]
theorem Representation.classFunction_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ρ.classFunction g = ρ.character g :=
  rfl

/-- The character of a finite-dimensional representation in `FDRep ℂ G`, as a bundled class
function.  Builds on `FDRep.character`. -/
def FDRep.classFunction (V : FDRep ℂ G) : ClassFunction G :=
  ⟨V.character, V.char_conj⟩

@[simp]
theorem FDRep.classFunction_apply (V : FDRep ℂ G) (g : G) :
    V.classFunction g = V.character g :=
  rfl

end Characters

/-! ### `χ(g⁻¹) = conj (χ g)`

The engine is `Module.End.trace_pow_pred_eq_star_trace`: if `f ^ n = 1` on a
finite-dimensional complex space, then `trace (f ^ (n - 1)) = conj (trace f)`.  The proof
diagonalizes `f` *implicitly*: for each `j < n`, the averaged operator
`Q j = n⁻¹ • ∑ i < n, ζ⁻¹ ^ (i * j) • f ^ i` (with `ζ` a primitive `n`-th root of unity) is
the projection onto the `ζ ^ j`-eigenspace of `f`.  The identities `∑ j, Q j = 1`,
`f * Q j = ζ ^ j • Q j`, and `Q j * Q j = Q j` are pure algebra (geometric sums), and the
trace of a projection is a natural number, hence conjugation-fixed.  This avoids both
inner-product-space machinery (unitarizability) and charpoly-root multiset bookkeeping. -/

section CharInv

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- If `f ^ n = 1`, then the trace of `f ^ (n - 1) = f⁻¹` is the complex conjugate of the
trace of `f`. -/
theorem Module.End.trace_pow_pred_eq_star_trace {f : Module.End ℂ V} {n : ℕ} (hn : n ≠ 0)
    (hf : f ^ n = 1) :
    trace ℂ V (f ^ (n - 1)) = starRingEnd ℂ (trace ℂ V f) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζdef
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn
  have hζn : ζ ^ n = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow hn] at hζn
    exact zero_ne_one hζn
  -- `Q j` is the projection onto the `ζ ^ j`-eigenspace of `f`.
  set Q : ℕ → Module.End ℂ V := fun j => (n : ℂ)⁻¹ • ∑ i ∈ range n, ζ⁻¹ ^ (i * j) • f ^ i
    with hQdef
  -- The projections sum to the identity.
  have hQsum : ∑ j ∈ range n, Q j = 1 := by
    have key : ∀ i ∈ range n, (∑ j ∈ range n, ζ⁻¹ ^ (i * j)) • f ^ i
        = if i = 0 then (n : ℂ) • 1 else 0 := by
      intro i hi
      rcases eq_or_ne i 0 with rfl | hi0
      · simp
      · have hne1 : ζ⁻¹ ^ i ≠ 1 :=
          hζ.inv.pow_ne_one_of_pos_of_lt hi0 (mem_range.mp hi)
        have hpow1 : (ζ⁻¹ ^ i) ^ n = 1 := by
          rw [← pow_mul, mul_comm i n, pow_mul, inv_pow, hζn, inv_one, one_pow]
        rw [if_neg hi0]
        have : ∑ j ∈ range n, ζ⁻¹ ^ (i * j) = 0 := by
          have := geom_sum_eq hne1 n
          simp only [hpow1, sub_self, zero_div] at this
          simpa only [pow_mul] using this
        rw [this, zero_smul]
    calc ∑ j ∈ range n, Q j
        = (n : ℂ)⁻¹ • ∑ j ∈ range n, ∑ i ∈ range n, ζ⁻¹ ^ (i * j) • f ^ i := by
          rw [Finset.smul_sum]
      _ = (n : ℂ)⁻¹ • ∑ i ∈ range n, (∑ j ∈ range n, ζ⁻¹ ^ (i * j)) • f ^ i := by
          rw [Finset.sum_comm]
          congr 1
          exact Finset.sum_congr rfl fun i _ => (Finset.sum_smul).symm
      _ = (n : ℂ)⁻¹ • ((n : ℂ) • 1) := by
          rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' (range n) 0,
            if_pos (mem_range.mpr (Nat.pos_of_ne_zero hn))]
      _ = 1 := by rw [smul_smul, inv_mul_cancel₀ hn0, one_smul]
  -- `Q j` projects onto the `ζ ^ j`-eigenspace: `f * Q j = ζ ^ j • Q j`.
  have hfQ : ∀ j, f * Q j = ζ ^ j • Q j := by
    intro j
    have expand : f * Q j = (n : ℂ)⁻¹ • ∑ i ∈ range n, ζ⁻¹ ^ (i * j) • f ^ (i + 1) := by
      rw [hQdef, mul_smul_comm, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [mul_smul_comm, ← pow_succ']
    -- shift the summation index cyclically, using `f ^ n = 1`
    set h : ℕ → Module.End ℂ V := fun i => (ζ ^ j * ζ⁻¹ ^ (i * j)) • f ^ i with hh
    have hstep : ∀ i, ζ⁻¹ ^ (i * j) • f ^ (i + 1) = h (i + 1) := by
      intro i
      rw [hh]
      congr 1
      rw [add_mul, one_mul, pow_add, ← mul_assoc, mul_comm (ζ ^ j), mul_assoc, ← mul_pow,
        mul_inv_cancel₀ hζ0, one_pow, mul_one]
    have hshift : ∑ i ∈ range n, h (i + 1) = ∑ i ∈ range n, h i := by
      have h1 : ∑ i ∈ range (n + 1), h i = ∑ i ∈ range n, h (i + 1) + h 0 :=
        Finset.sum_range_succ' h n
      have h2 : ∑ i ∈ range (n + 1), h i = ∑ i ∈ range n, h i + h n :=
        Finset.sum_range_succ h n
      have hn' : h n = h 0 := by
        rw [hh]
        simp only [Nat.zero_mul, pow_zero, mul_one]
        rw [pow_mul, inv_pow, hζn, inv_one, one_pow, mul_one, hf]
      have := h1.symm.trans h2
      rw [hn'] at this
      exact add_right_cancel this
    calc f * Q j
        = (n : ℂ)⁻¹ • ∑ i ∈ range n, h (i + 1) := by
          rw [expand]
          exact congrArg _ (Finset.sum_congr rfl fun i _ => hstep i)
      _ = (n : ℂ)⁻¹ • ∑ i ∈ range n, h i := by rw [hshift]
      _ = ζ ^ j • Q j := by
          rw [hQdef]
          simp only [hh, mul_smul, ← Finset.smul_sum]
          rw [smul_comm]
  -- hence `f ^ k * Q j = ζ ^ (j * k) • Q j` for every `k`
  have hfpowQ : ∀ j k, f ^ k * Q j = (ζ ^ j) ^ k • Q j := by
    intro j k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_assoc, hfQ j, mul_smul_comm, ih, smul_smul, pow_succ,
        mul_comm (ζ ^ j)]
  -- `Q j` is idempotent
  have hQQ : ∀ j, Q j * Q j = Q j := by
    intro j
    have expand : Q j * Q j = (n : ℂ)⁻¹ • ∑ i ∈ range n, ζ⁻¹ ^ (i * j) • (f ^ i * Q j) := by
      conv_lhs => rw [hQdef]
      rw [smul_mul_assoc, Finset.sum_mul]
      congr 1
    rw [expand]
    have : ∀ i ∈ range n, ζ⁻¹ ^ (i * j) • (f ^ i * Q j) = Q j := by
      intro i _
      rw [hfpowQ j i, smul_smul, ← pow_mul, mul_comm j i, ← mul_pow, inv_mul_cancel₀ hζ0,
        one_pow, one_smul]
    rw [Finset.sum_congr rfl this, Finset.sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ hn0, one_smul]
  -- traces of the projections are natural numbers, hence fixed by conjugation
  have htrQ : ∀ j, starRingEnd ℂ (trace ℂ V (Q j)) = trace ℂ V (Q j) := by
    intro j
    have hproj : LinearMap.IsProj (LinearMap.range (Q j)) (Q j) := by
      refine ⟨fun x => LinearMap.mem_range_self _ x, fun x hx => ?_⟩
      obtain ⟨y, rfl⟩ := hx
      have := congrArg (fun T : Module.End ℂ V => T y) (hQQ j)
      simpa [Module.End.mul_apply] using this
    rw [hproj.trace, map_natCast]
  -- star of each eigenvalue is its inverse, realized as the `(n-1)`-st power
  have hstar : ∀ j, (ζ ^ j) ^ (n - 1) = starRingEnd ℂ (ζ ^ j) := by
    intro j
    have hpow1 : (ζ ^ j) ^ n = 1 := by rw [← pow_mul, mul_comm j n, pow_mul, hζn, one_pow]
    have hnorm : ‖ζ ^ j‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow1 hn
    have hmul : (ζ ^ j) ^ (n - 1) * ζ ^ j = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn), hpow1]
    rw [← Complex.inv_eq_conj hnorm]
    exact (inv_eq_of_mul_eq_one_left hmul).symm
  -- expand the two traces over the projections and compare termwise
  have hexp : ∀ k, trace ℂ V (f ^ k) = ∑ j ∈ range n, (ζ ^ j) ^ k * trace ℂ V (Q j) := by
    intro k
    conv_lhs => rw [← mul_one (f ^ k), ← hQsum, Finset.mul_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hfpowQ j k, map_smul, smul_eq_mul]
  calc trace ℂ V (f ^ (n - 1))
      = ∑ j ∈ range n, (ζ ^ j) ^ (n - 1) * trace ℂ V (Q j) := hexp (n - 1)
    _ = ∑ j ∈ range n, starRingEnd ℂ (ζ ^ j * trace ℂ V (Q j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, htrQ j, hstar j]
    _ = starRingEnd ℂ (∑ j ∈ range n, ζ ^ j * trace ℂ V (Q j)) := by rw [map_sum]
    _ = starRingEnd ℂ (trace ℂ V f) := by
        congr 1
        have := hexp 1
        simpa [pow_one] using this.symm

variable {G : Type u} [Group G] [Finite G]

/-- For a finite group `G` and `g : G`, the character of a finite-dimensional complex
representation satisfies `χ(g⁻¹) = conj (χ g)`.  MathComp: `char_inv` (`character.v`). -/
theorem Representation.char_inv (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = starRingEnd ℂ (ρ.character g) := by
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hpow : ρ g ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hg : g⁻¹ = g ^ (orderOf g - 1) := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn), pow_orderOf_eq_one]
  calc ρ.character g⁻¹
      = trace ℂ V (ρ g ^ (orderOf g - 1)) := by rw [Representation.character, hg, map_pow]
    _ = starRingEnd ℂ (trace ℂ V (ρ g)) := Module.End.trace_pow_pred_eq_star_trace hn hpow
    _ = starRingEnd ℂ (ρ.character g) := rfl

/-- For a finite group `G` and `g : G`, the character of `V : FDRep ℂ G` satisfies
`χ(g⁻¹) = conj (χ g)`.  MathComp: `char_inv` (`character.v`). -/
theorem FDRep.char_inv (W : FDRep ℂ G) (g : G) :
    W.character g⁻¹ = starRingEnd ℂ (W.character g) := by
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hpow : W.ρ g ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hg : g⁻¹ = g ^ (orderOf g - 1) := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn), pow_orderOf_eq_one]
  calc W.character g⁻¹
      = trace ℂ W (W.ρ g ^ (orderOf g - 1)) := by rw [FDRep.character, hg, map_pow]
    _ = starRingEnd ℂ (trace ℂ W (W.ρ g)) := Module.End.trace_pow_pred_eq_star_trace hn hpow
    _ = starRingEnd ℂ (W.character g) := rfl

end CharInv

/-! ### The center of the group algebra

The center of `MonoidAlgebra ℂ G` consists exactly of the elements whose coefficient
function is a class function; consequently it is linearly equivalent to `ClassFunction G`
and has dimension `#ConjClasses G`.  (The class sums are the image of the indicator basis
under this equivalence; they are not needed as explicit elements in this file.) -/

section Center

variable {G : Type u} [Group G]

/-- An element of the group algebra is central if and only if its coefficient function is
constant on conjugacy classes. -/
theorem MonoidAlgebra.mem_center_iff {x : MonoidAlgebra ℂ G} :
    x ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) ↔ ∀ g h : G, x (h * g * h⁻¹) = x g := by
  constructor
  · intro hx g h
    have hcomm := Subalgebra.mem_center_iff.mp hx (single h 1)
    have := congrArg (fun y : MonoidAlgebra ℂ G => y (h * g)) hcomm
    simp only [single_mul_apply, mul_single_apply, one_mul, mul_one, inv_mul_cancel_left]
      at this
    exact this.symm
  · intro hx
    rw [Subalgebra.mem_center_iff]
    intro y
    induction y using MonoidAlgebra.induction_on with
    | hM g =>
      refine Finsupp.ext fun h => ?_
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply,
        MonoidAlgebra.mul_single_apply, one_mul, mul_one]
      have := hx (h * g⁻¹) g⁻¹
      rw [show g⁻¹ * (h * g⁻¹) * g⁻¹⁻¹ = g⁻¹ * h by group] at this
      exact this
    | hadd y₁ y₂ h₁ h₂ => rw [add_mul, mul_add, h₁, h₂]
    | hsmul c y hy => rw [smul_mul_assoc, mul_smul_comm, hy]

variable (G) in
/-- For a finite group, the center of the group algebra is linearly equivalent to the space
of class functions. -/
def MonoidAlgebra.centerEquivClassFunction [Finite G] :
    Subalgebra.center ℂ (MonoidAlgebra ℂ G) ≃ₗ[ℂ] ClassFunction G where
  toFun x := ⟨fun g => (x : MonoidAlgebra ℂ G) g, MonoidAlgebra.mem_center_iff.mp x.2⟩
  invFun φ :=
    ⟨Finsupp.equivFunOnFinite.symm ⇑φ, MonoidAlgebra.mem_center_iff.mpr fun g h => by
      simp only [Finsupp.coe_equivFunOnFinite_symm]
      exact φ.conj_apply g h⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  left_inv x := Subtype.ext (Finsupp.equivFunOnFinite_symm_coe _)
  right_inv φ := rfl

theorem MonoidAlgebra.finrank_center [Finite G] :
    Module.finrank ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G)) = Nat.card (ConjClasses G) := by
  rw [(MonoidAlgebra.centerEquivClassFunction G).finrank_eq,
    ClassFunction.finrank_classFunction]

end Center

/-! ### Characters of modules over the group algebra -/

section ModuleCharacter

variable {G : Type u} [Group G]

instance MonoidAlgebra.instModuleFiniteOfFinite [Finite G] :
    Module.Finite ℂ (MonoidAlgebra ℂ G) :=
  Module.Finite.equiv (Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm

instance (N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) [Finite G] :
    FiniteDimensional ℂ N :=
  FiniteDimensional.of_injective ((Submodule.subtype N).restrictScalars ℂ) N.injective_subtype

variable (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (MonoidAlgebra ℂ G) M]
  [IsScalarTower ℂ (MonoidAlgebra ℂ G) M]

namespace MonoidAlgebra

/-- The ℂ-linear endomorphism of a `ℂ[G]`-module given by the action of `g : G`. -/
def actionEnd (g : G) : M →ₗ[ℂ] M where
  toFun x := MonoidAlgebra.single g (1 : ℂ) • x
  map_add' := smul_add _
  map_smul' c x := smul_comm _ c x

@[simp]
theorem actionEnd_apply (g : G) (x : M) :
    actionEnd M g x = MonoidAlgebra.single g (1 : ℂ) • x :=
  rfl

theorem actionEnd_mul (g h : G) :
    actionEnd M (g * h) = actionEnd M g ∘ₗ actionEnd M h := by
  refine LinearMap.ext fun x => ?_
  simp only [actionEnd_apply, LinearMap.comp_apply, ← mul_smul,
    MonoidAlgebra.single_mul_single, one_mul]

theorem ofModule'_eq_actionEnd (g : G) :
    Representation.ofModule' (k := ℂ) (G := G) M g = actionEnd M g :=
  rfl

theorem ofModule'_asAlgebraHom_apply (r : MonoidAlgebra ℂ G) (x : M) :
    (Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom r x = r • x := by
  induction r using MonoidAlgebra.induction_on with
  | hM g =>
    rw [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single, one_smul,
      ofModule'_eq_actionEnd, actionEnd_apply]
  | hadd a b ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_smul]
  | hsmul c r hr => rw [map_smul, LinearMap.smul_apply, hr, smul_assoc]

/-- The identity map, as a `ℂ[G]`-linear equivalence between the auxiliary module
`(ofModule' M).asModule` and `M` itself. -/
def ofModule'AsModuleEquiv :
    (Representation.ofModule' (k := ℂ) (G := G) M).asModule ≃ₗ[MonoidAlgebra ℂ G] M where
  toFun := (Representation.ofModule' (k := ℂ) (G := G) M).asModuleEquiv
  invFun := (Representation.ofModule' (k := ℂ) (G := G) M).asModuleEquiv.symm
  left_inv x := by simp
  right_inv x := by simp
  map_add' := map_add _
  map_smul' r x := by
    rw [RingHom.id_apply, Representation.asModuleEquiv_map_smul,
      ofModule'_asAlgebraHom_apply]

theorem isIrreducible_ofModule' (h : IsSimpleModule (MonoidAlgebra ℂ G) M) :
    (Representation.ofModule' (k := ℂ) (G := G) M).IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  haveI := h
  exact IsSimpleModule.congr (ofModule'AsModuleEquiv M)

variable [FiniteDimensional ℂ M]

variable (G) in
/-- The character of a finite-dimensional `ℂ[G]`-module, as a class function on `G`: the
trace of the action of `g`.  For simple modules these are the irreducible characters
(`Irr`). -/
def moduleCharacter : ClassFunction G where
  toFun g := trace ℂ M (actionEnd M g)
  conj_invariant' g h := by
    rw [actionEnd_mul, trace_comp_comm', ← actionEnd_mul, inv_mul_cancel_left]

theorem moduleCharacter_apply (g : G) :
    moduleCharacter G M g = trace ℂ M (actionEnd M g) :=
  rfl

/-- The class function `moduleCharacter` is the character of the representation
`Representation.ofModule'` associated to the module. -/
theorem moduleCharacter_eq_ofModule'_character (g : G) :
    moduleCharacter G M g = (Representation.ofModule' (k := ℂ) (G := G) M).character g :=
  rfl

end MonoidAlgebra

end ModuleCharacter

/-! ### Irreducible characters -/

section Irr

variable {G : Type u} [Group G]

variable (G) in
/-- The irreducible characters of a finite group `G` over `ℂ` (MathComp: `irr G`): class
functions that arise as the character of some simple module over the group algebra
`ℂ[G]` — equivalently (see `Representation.exists_irr_classFunction_eq`) of some
irreducible finite-dimensional representation.  The witness is an existential over
submodules of the regular module, which every simple module embeds into. -/
structure Irr [Fintype G] where
  /-- The underlying class function (the character). -/
  toClassFunction : ClassFunction G
  /-- The character comes from a simple submodule of the regular module. -/
  exists_simple' : ∃ N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G),
    IsSimpleModule (MonoidAlgebra ℂ G) N ∧
      toClassFunction = MonoidAlgebra.moduleCharacter G N

namespace Irr

variable [Fintype G]

attribute [coe] toClassFunction

/-- Irreducible characters coerce to their underlying class functions, mirroring the
`Sylow p G → Subgroup G` coercion. -/
instance : CoeOut (Irr G) (ClassFunction G) :=
  ⟨toClassFunction⟩

instance : FunLike (Irr G) G ℂ where
  coe χ := χ.toClassFunction
  coe_injective χ ψ h := by
    cases χ; cases ψ
    congr 1
    exact DFunLike.coe_injective h

@[ext]
theorem ext {χ ψ : Irr G} (h : ∀ g, χ g = ψ g) : χ = ψ :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_toClassFunction (χ : Irr G) : ⇑χ.toClassFunction = ⇑χ :=
  rfl

/-- Applying the coercion `Irr G → ClassFunction G` agrees with applying
`Irr.toClassFunction` (the coercion is definitionally `toClassFunction`, and the
right-hand side is its simp-normal application form). -/
@[simp]
theorem coe_apply (χ : Irr G) (g : G) : (χ : ClassFunction G) g = χ g :=
  rfl

theorem toClassFunction_injective :
    Function.Injective (toClassFunction : Irr G → ClassFunction G) := by
  intro χ ψ h
  exact DFunLike.coe_injective (congrArg (⇑· : ClassFunction G → G → ℂ) h)

theorem toClassFunction_inj {χ ψ : Irr G} :
    χ.toClassFunction = ψ.toClassFunction ↔ χ = ψ :=
  toClassFunction_injective.eq_iff

end Irr

open scoped ClassFunction

open scoped Classical in
/-- **First orthogonality relation** for characters of simple `ℂ[G]`-modules, in
inner-product form. -/
theorem MonoidAlgebra.cfInner_moduleCharacter [Fintype G]
    {N N' : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)}
    (hN : IsSimpleModule (MonoidAlgebra ℂ G) N) (hN' : IsSimpleModule (MonoidAlgebra ℂ G) N') :
    ⟪moduleCharacter G N, moduleCharacter G N'⟫_[G] =
      if moduleCharacter G N = moduleCharacter G N' then 1 else 0 := by
  classical
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have key : ∀ P P' : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G),
      IsSimpleModule (MonoidAlgebra ℂ G) P → IsSimpleModule (MonoidAlgebra ℂ G) P' →
      ⟪moduleCharacter G P, moduleCharacter G P'⟫_[G] =
        if Nonempty ((Representation.ofModule' (k := ℂ) (G := G) P').Equiv
            (Representation.ofModule' (k := ℂ) (G := G) P)) then 1 else 0 := by
    intro P P' hP hP'
    haveI := isIrreducible_ofModule' P hP
    haveI := isIrreducible_ofModule' P' hP'
    rw [ClassFunction.cfInner_def]
    have hterm : ∀ g : G,
        moduleCharacter G P g * starRingEnd ℂ (moduleCharacter G P' g) =
          (Representation.ofModule' (k := ℂ) (G := G) P).character g *
            (Representation.ofModule' (k := ℂ) (G := G) P').character g⁻¹ := by
      intro g
      rw [moduleCharacter_eq_ofModule'_character, moduleCharacter_eq_ofModule'_character,
        Representation.char_inv]
    rw [Finset.sum_congr rfl fun g _ => hterm g, Fintype.card_eq_nat_card]
    exact Representation.char_orthonormal _ _
  rcases eq_or_ne (moduleCharacter G N) (moduleCharacter G N') with heq | hne
  · rw [if_pos heq, heq, key N' N' hN' hN', if_pos ⟨Representation.Equiv.refl _⟩]
  · rw [if_neg hne, key N N' hN hN']
    refine if_neg ?_
    rintro ⟨e⟩
    refine hne (ClassFunction.ext fun g => ?_)
    rw [moduleCharacter_eq_ofModule'_character, moduleCharacter_eq_ofModule'_character,
      Representation.char_iso e]

namespace Irr

variable [Fintype G]

open scoped Classical in
/-- **First orthogonality relation**: the irreducible characters are orthonormal.
MathComp: `cfdot_irr`. -/
theorem cfInner_eq (χ ψ : Irr G) :
    ⟪χ.toClassFunction, ψ.toClassFunction⟫_[G] = if χ = ψ then 1 else 0 := by
  classical
  obtain ⟨N, hN, hχ⟩ := χ.exists_simple'
  obtain ⟨N', hN', hψ⟩ := ψ.exists_simple'
  rw [hχ, hψ, MonoidAlgebra.cfInner_moduleCharacter hN hN']
  exact if_congr (by rw [← hχ, ← hψ, toClassFunction_inj]) rfl rfl

theorem linearIndependent :
    LinearIndependent ℂ (toClassFunction : Irr G → ClassFunction G) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  refine Finsupp.ext fun ψ => ?_
  have h0 : ClassFunction.cfInnerₗ ψ.toClassFunction
      (Finsupp.linearCombination ℂ toClassFunction l) = 0 := by
    rw [hl, map_zero]
  rw [Finsupp.linearCombination_apply, map_finsuppSum] at h0
  have hterm : ∀ χ ∈ l.support,
      ClassFunction.cfInnerₗ ψ.toClassFunction (l χ • χ.toClassFunction) =
        if χ = ψ then l χ else 0 := by
    intro χ _
    rw [map_smul, smul_eq_mul, ClassFunction.cfInnerₗ_apply, cfInner_eq, mul_ite, mul_one,
      mul_zero]
  rw [Finsupp.sum_congr (g2 := fun χ a => if χ = ψ then a else 0) hterm,
    Finsupp.sum_ite_eq' l ψ fun _ a => a] at h0
  rw [Finsupp.zero_apply]
  by_cases hmem : ψ ∈ l.support
  · rwa [if_pos hmem] at h0
  · rwa [Finsupp.notMem_support_iff] at hmem

instance : Finite (Irr G) := by
  by_contra hinf
  rw [not_finite_iff_infinite] at hinf
  have h0 := (linearIndependent (G := G)).finrank_eq_zero_of_infinite
  rw [ClassFunction.finrank_classFunction] at h0
  have : Nonempty (ConjClasses G) := ⟨ConjClasses.mk 1⟩
  exact Nat.card_pos.ne' h0

noncomputable instance : Fintype (Irr G) :=
  Fintype.ofFinite _

theorem card_le_card_conjClasses : Fintype.card (Irr G) ≤ Nat.card (ConjClasses G) := by
  have h := (linearIndependent (G := G)).fintype_card_le_finrank
  rwa [ClassFunction.finrank_classFunction] at h

end Irr

open scoped Classical in
/-- The restatement of `FDRep.char_orthonormal` in the language of class functions and the
hermitian inner product. -/
theorem FDRep.cfInner_classFunction [Fintype G] (V W : FDRep ℂ G)
    [CategoryTheory.Simple V] [CategoryTheory.Simple W] :
    ⟪V.classFunction, W.classFunction⟫_[G] = if Nonempty (V ≅ W) then 1 else 0 := by
  classical
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have horth := FDRep.char_orthonormal V W
  rw [ClassFunction.cfInner_def]
  have hterm : ∀ g : G,
      V.classFunction g * starRingEnd ℂ (W.classFunction g) =
        V.character g * W.character g⁻¹ := by
    intro g
    rw [FDRep.classFunction_apply, FDRep.classFunction_apply, FDRep.char_inv]
  rw [Finset.sum_congr rfl fun g _ => hterm g, ← invOf_eq_inv, ← smul_eq_mul]
  exact horth

/-- Every finite-dimensional irreducible representation contributes its character to
`Irr G`: the enumeration by simple submodules of the regular module is exhaustive. -/
theorem Representation.exists_irr_classFunction_eq [Fintype G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    ∃ χ : Irr G, χ.toClassFunction = ρ.classFunction := by
  classical
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  -- the simple module attached to `ρ` embeds in the (semisimple) regular module
  haveI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨m, hm⟩ := exists_ne (0 : ρ.asModule)
  have hf : LinearMap.toSpanSingleton (MonoidAlgebra ℂ G) ρ.asModule m ≠ 0 := by
    intro hzero
    apply hm
    have := congrArg (fun f : MonoidAlgebra ℂ G →ₗ[MonoidAlgebra ℂ G] ρ.asModule => f 1) hzero
    simpa [LinearMap.toSpanSingleton_apply] using this
  obtain ⟨S, ⟨e⟩⟩ := LinearMap.linearEquiv_of_ne_zero hf
  haveI hS : IsSimpleModule (MonoidAlgebra ℂ G) S := IsSimpleModule.congr e.symm
  refine ⟨⟨MonoidAlgebra.moduleCharacter G S, ⟨S, hS, rfl⟩⟩, ClassFunction.ext fun g => ?_⟩
  -- transfer the trace along `S ≃ ρ.asModule ≃ V`
  have h1 : (e.restrictScalars ℂ).conj (MonoidAlgebra.actionEnd ρ.asModule g) =
      MonoidAlgebra.actionEnd S g := by
    refine LinearMap.ext fun x => ?_
    have hsymm : (e.restrictScalars ℂ).symm x = e.symm x := rfl
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.restrictScalars_apply, MonoidAlgebra.actionEnd_apply, hsymm, map_smul,
      LinearEquiv.apply_symm_apply]
  have h2 : ρ.asModuleEquiv.conj (MonoidAlgebra.actionEnd ρ.asModule g) = ρ g := by
    refine LinearMap.ext fun v => ?_
    change ρ.asModuleEquiv (MonoidAlgebra.single g (1 : ℂ) • ρ.asModuleEquiv.symm v) = ρ g v
    rw [Representation.single_smul, one_smul, LinearEquiv.apply_symm_apply]
    rfl
  calc MonoidAlgebra.moduleCharacter G S g
      = trace ℂ S (MonoidAlgebra.actionEnd S g) := rfl
    _ = trace ℂ ρ.asModule (MonoidAlgebra.actionEnd ρ.asModule g) := by
        rw [← h1, LinearMap.trace_conj']
    _ = trace ℂ V (ρ g) := by rw [← h2, LinearMap.trace_conj']
    _ = ρ.classFunction g := rfl

end Irr

/-! ### Completeness: `#Irr G = #ConjClasses G`

If a class function `f` pairs to zero with every irreducible character, then the central
element `z = ∑ g, f g⁻¹ • single g 1` of the group algebra acts as a trace-zero scalar
(Schur's lemma) — hence as zero — on every simple submodule of the regular module; by
semisimplicity (Maschke) these span, so `z = z * 1 = 0` and `f = 0`.  This injectivity
gives `#ConjClasses G ≤ #Irr G`; linear independence of the irreducible characters gives
the reverse inequality. -/

section Completeness

variable {G : Type u} [Group G] [Fintype G]

open scoped ClassFunction

namespace Irr

private def centralOfClassFunction (f : ClassFunction G) : MonoidAlgebra ℂ G :=
  Finsupp.equivFunOnFinite.symm fun g => f g⁻¹

private theorem centralOfClassFunction_apply (f : ClassFunction G) (h : G) :
    centralOfClassFunction f h = f h⁻¹ :=
  rfl

private theorem centralOfClassFunction_eq_sum (f : ClassFunction G) :
    centralOfClassFunction f = ∑ g : G, f g⁻¹ • MonoidAlgebra.single g (1 : ℂ) :=
  (Finsupp.univ_sum_single (centralOfClassFunction f)).symm.trans
    (Finset.sum_congr rfl fun g _ => by
      rw [centralOfClassFunction_apply, MonoidAlgebra.smul_single', mul_one])

private theorem centralOfClassFunction_mem_center (f : ClassFunction G) :
    centralOfClassFunction f ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
  rw [MonoidAlgebra.mem_center_iff]
  intro g h
  rw [centralOfClassFunction_apply, centralOfClassFunction_apply,
    show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ by group, ClassFunction.conj_apply]

private def pairing : ClassFunction G →ₗ[ℂ] (Irr G → ℂ) where
  toFun f χ := ∑ g : G, χ g * f g⁻¹
  map_add' f₁ f₂ := by
    funext χ
    simp only [ClassFunction.add_apply, mul_add, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' c f := by
    funext χ
    simp only [ClassFunction.smul_apply, smul_eq_mul, RingHom.id_apply, Pi.smul_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring

private theorem eq_zero_of_pairing_eq_zero (f : ClassFunction G) (hf : pairing f = 0) :
    f = 0 := by
  classical
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  set z := centralOfClassFunction f with hzdef
  have hzc : ∀ a : MonoidAlgebra ℂ G, a * z = z * a := fun a =>
    Subalgebra.mem_center_iff.mp (centralOfClassFunction_mem_center f) a
  -- multiplication by `z` is `ℂ[G]`-linear (as `z` is central)
  set Lz : MonoidAlgebra ℂ G →ₗ[MonoidAlgebra ℂ G] MonoidAlgebra ℂ G :=
    { toFun := fun x => z * x
      map_add' := mul_add z
      map_smul' := fun a x => by
        simp only [smul_eq_mul, RingHom.id_apply]
        rw [← mul_assoc, ← hzc a, mul_assoc] } with hLzdef
  have hLz_apply : ∀ x, Lz x = z * x := fun x => rfl
  -- `z` annihilates every simple submodule of the regular module
  have hann : ∀ N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G),
      IsSimpleModule (MonoidAlgebra ℂ G) N → ∀ x ∈ N, z * x = 0 := by
    intro N hN x hx
    haveI := hN
    haveI : Nontrivial N := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) N
    have hmaps : ∀ y ∈ N, Lz y ∈ N := fun y hy => by
      rw [hLz_apply, ← smul_eq_mul]
      exact N.smul_mem z hy
    set L : N →ₗ[MonoidAlgebra ℂ G] N := Lz.restrict hmaps with hLdef
    -- Schur: `L` is scalar
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (k := ℂ) (A := MonoidAlgebra ℂ G) (V := N)).2 L
    -- its trace is the pairing of `f` with the character of `N`, which vanishes
    have hL_restrict : LinearMap.restrictScalars ℂ L
        = ∑ g : G, f g⁻¹ • MonoidAlgebra.actionEnd (↥N) g := by
      refine LinearMap.ext fun y => Subtype.ext ?_
      have hcoeL : ((LinearMap.restrictScalars ℂ L) y : MonoidAlgebra ℂ G) = z * y := by
        rw [LinearMap.restrictScalars_apply, hLdef, LinearMap.restrict_apply]
        rfl
      rw [hcoeL, hzdef, centralOfClassFunction_eq_sum, Finset.sum_mul]
      have hcoeR : (((∑ g : G, f g⁻¹ • MonoidAlgebra.actionEnd (↥N) g) y : N)
          : MonoidAlgebra ℂ G) = ∑ g : G, f g⁻¹ • (MonoidAlgebra.single g (1 : ℂ) * y) := by
        rw [LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum]
        exact Finset.sum_congr rfl fun g _ => by
          rw [LinearMap.smul_apply, Submodule.coe_smul_of_tower, MonoidAlgebra.actionEnd_apply,
            Submodule.coe_smul, smul_eq_mul]
      rw [hcoeR]
      exact Finset.sum_congr rfl fun g _ => by rw [smul_mul_assoc]
    have htrace1 : trace ℂ N (LinearMap.restrictScalars ℂ L)
        = ∑ g : G, f g⁻¹ * MonoidAlgebra.moduleCharacter G N g := by
      rw [hL_restrict, map_sum]
      exact Finset.sum_congr rfl fun g _ => by
        rw [map_smul, smul_eq_mul, MonoidAlgebra.moduleCharacter_apply]
    have htrace2 : trace ℂ N (LinearMap.restrictScalars ℂ L)
        = c * Module.finrank ℂ N := by
      have hLc : LinearMap.restrictScalars ℂ L = c • LinearMap.id := by
        refine LinearMap.ext fun y => ?_
        rw [LinearMap.restrictScalars_apply, ← hc, Algebra.algebraMap_eq_smul_one,
          LinearMap.smul_apply, Module.End.one_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hLc, map_smul, LinearMap.trace_id, smul_eq_mul]
    have hpair0 : ∑ g : G, f g⁻¹ * MonoidAlgebra.moduleCharacter G N g = 0 := by
      have h0 := congrFun hf ⟨MonoidAlgebra.moduleCharacter G N, ⟨N, hN, rfl⟩⟩
      rw [Pi.zero_apply] at h0
      rw [← h0]
      exact Finset.sum_congr rfl fun g _ => mul_comm _ _
    have hc0 : c = 0 := by
      have hfr : (Module.finrank ℂ N : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
      have := htrace2.symm.trans (htrace1.trans hpair0)
      exact (mul_eq_zero.mp this).resolve_right hfr
    have hL0 : L ⟨x, hx⟩ = 0 := by
      rw [← hc, hc0, map_zero, LinearMap.zero_apply]
    have := congrArg (Subtype.val : N → MonoidAlgebra ℂ G) hL0
    rwa [hLdef, LinearMap.restrict_apply] at this
  -- semisimplicity: the simple submodules span, so `z = z * 1 = 0`
  have hz0 : z = 0 := by
    have htop := IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)
    have hle : (⊤ : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
        ≤ LinearMap.ker Lz := by
      rw [← htop]
      exact sSup_le fun N hN => fun x hx => LinearMap.mem_ker.mpr (hann N hN x hx)
    have h1 : Lz 1 = 0 := LinearMap.mem_ker.mp (hle Submodule.mem_top)
    rwa [hLz_apply, mul_one] at h1
  refine ClassFunction.ext fun g => ?_
  have hg := congrArg (fun w : MonoidAlgebra ℂ G => w g⁻¹) hz0
  simp only [hzdef, centralOfClassFunction_apply, inv_inv] at hg
  exact hg

/-- **Completeness of irreducible characters**: the number of irreducible characters of a
finite group equals its number of conjugacy classes.  MathComp: `NirrE`/`card_irr`. -/
theorem card_eq_card_conjClasses : Nat.card (Irr G) = Nat.card (ConjClasses G) := by
  refine le_antisymm ?_ ?_
  · rw [Nat.card_eq_fintype_card]
    exact card_le_card_conjClasses
  · have hinj : Function.Injective (pairing (G := G)) := by
      rw [← LinearMap.ker_eq_bot]
      exact (Submodule.eq_bot_iff _).mpr fun f hf =>
        eq_zero_of_pairing_eq_zero f (LinearMap.mem_ker.mp hf)
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [ClassFunction.finrank_classFunction, Module.finrank_pi,
      ← Nat.card_eq_fintype_card] at hle

variable (G) in
/-- The irreducible characters form a basis of the space of class functions.
MathComp: `irr_basis`. -/
noncomputable def basis : Basis (Irr G) ℂ (ClassFunction G) :=
  basisOfLinearIndependentOfCardEqFinrank' _ Irr.linearIndependent (by
    rw [ClassFunction.finrank_classFunction, ← Nat.card_eq_fintype_card,
      card_eq_card_conjClasses])

@[simp]
theorem coe_basis : ⇑(basis G) = (toClassFunction : Irr G → ClassFunction G) :=
  coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _

theorem basis_apply (χ : Irr G) : basis G χ = χ.toClassFunction :=
  congrFun coe_basis χ

end Irr

/-- Expansion of a class function in the basis of irreducible characters.
MathComp: `cfun_sum_cfdot`. -/
theorem ClassFunction.eq_sum_cfInner_smul (f : ClassFunction G) :
    f = ∑ χ : Irr G, ⟪f, χ.toClassFunction⟫_[G] • χ.toClassFunction := by
  classical
  have hcoef : ∀ ψ : Irr G, ⟪f, ψ.toClassFunction⟫_[G] = (Irr.basis G).repr f ψ := by
    intro ψ
    conv_lhs => rw [← (Irr.basis G).sum_repr f]
    rw [ClassFunction.cfInner_sum_left, Finset.sum_congr rfl fun χ _ => by
      rw [Irr.basis_apply, ClassFunction.cfInner_smul_left, Irr.cfInner_eq, mul_ite, mul_one,
        mul_zero]]
    rw [Finset.sum_ite_eq' Finset.univ ψ, if_pos (Finset.mem_univ ψ)]
  rw [Finset.sum_congr rfl fun χ _ => by rw [hcoef χ]]
  conv_lhs => rw [← (Irr.basis G).sum_repr f]
  exact Finset.sum_congr rfl fun χ _ => by rw [Irr.basis_apply]

end Completeness

/-! ### The second orthogonality relation -/

section SecondOrthogonality

variable {G : Type u} [Group G]

/-- The class equation for a single conjugacy class:
`|class of g| * |centralizer of g| = |G|`. -/
theorem ConjClasses.nat_card_carrier_mul_card_centralizer [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier
      * Nat.card (Subgroup.centralizer ({g} : Set G)) = Nat.card G := by
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer, ← ConjAct.orbit_eq_carrier_conjClasses,
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct G) g),
    ← Subgroup.index_eq_card, Subgroup.index_mul_card]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

/-- Conjugate elements have centralizers of the same cardinality. -/
theorem Subgroup.card_centralizer_eq_of_isConj [Finite G] {g h : G} (hc : IsConj g h) :
    Nat.card (Subgroup.centralizer ({g} : Set G))
      = Nat.card (Subgroup.centralizer ({h} : Set G)) := by
  have h1 := ConjClasses.nat_card_carrier_mul_card_centralizer g
  have h2 := ConjClasses.nat_card_carrier_mul_card_centralizer h
  rw [show ConjClasses.mk g = ConjClasses.mk h from ConjClasses.mk_eq_mk_iff_isConj.mpr hc]
    at h1
  haveI : Nonempty (ConjClasses.mk h).carrier := ⟨⟨h, ConjClasses.mem_carrier_mk⟩⟩
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)

open scoped ClassFunction in
open scoped Classical in
/-- **Second orthogonality relation** (column orthogonality of the character table):
`∑ χ ∈ Irr G, χ g * conj (χ h)` equals the order of the centralizer of `g` if `g` and `h`
are conjugate, and `0` otherwise.  MathComp: `second_orthogonality_relation`. -/
theorem Irr.second_orthogonality [Fintype G] (g h : G) :
    ∑ χ : Irr G, χ g * starRingEnd ℂ (χ h) =
      if IsConj g h then (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) else 0 := by
  classical
  -- the indicator class function of the conjugacy class of `h`
  obtain ⟨δ, hδ⟩ : ∃ δ : ClassFunction G,
      ∀ x, δ x = if ConjClasses.mk x = ConjClasses.mk h then 1 else 0 :=
    ⟨⟨fun x => if ConjClasses.mk x = ConjClasses.mk h then 1 else 0, fun x k => by
      rw [show ConjClasses.mk (k * x * k⁻¹) = ConjClasses.mk x from
        ConjClasses.mk_eq_mk_iff_isConj.mpr (IsConj.symm (isConj_iff.mpr ⟨k, rfl⟩))]⟩,
      fun x => rfl⟩
  -- its coefficients in the basis of irreducible characters
  have hδcoef : ∀ χ : Irr G, ⟪δ, χ.toClassFunction⟫_[G]
      = (Nat.card (ConjClasses.mk h).carrier : ℂ) * (Fintype.card G : ℂ)⁻¹
          * starRingEnd ℂ (χ h) := by
    intro χ
    rw [ClassFunction.cfInner_def]
    have h1 : ∀ x : G, δ x * starRingEnd ℂ (χ.toClassFunction x)
        = if ConjClasses.mk x = ConjClasses.mk h then starRingEnd ℂ (χ x) else 0 := by
      intro x
      rw [hδ x, Irr.coe_toClassFunction]
      by_cases hx : ConjClasses.mk x = ConjClasses.mk h
      · rw [if_pos hx, if_pos hx, one_mul]
      · rw [if_neg hx, if_neg hx, zero_mul]
    have h2 : ∀ x ∈ Finset.univ.filter fun x => ConjClasses.mk x = ConjClasses.mk h,
        starRingEnd ℂ (χ x) = starRingEnd ℂ (χ h) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have := χ.toClassFunction.apply_eq_of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp hx.2)
      rw [Irr.coe_toClassFunction] at this
      rw [this]
    have hcard : Nat.card (ConjClasses.mk h).carrier
        = (Finset.univ.filter fun x => ConjClasses.mk x = ConjClasses.mk h).card := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_congr (Equiv.subtypeEquivRight fun x =>
          ConjClasses.mem_carrier_iff_mk_eq),
        Fintype.card_subtype]
    rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.sum_filter,
      Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul, ← hcard]
    ring
  -- expand the indicator in the basis and evaluate at `g`
  have heval := congrArg (fun F : ClassFunction G => F g) (ClassFunction.eq_sum_cfInner_smul δ)
  simp only [ClassFunction.sum_apply, ClassFunction.smul_apply, smul_eq_mul,
    Irr.coe_toClassFunction] at heval
  rw [Finset.sum_congr rfl fun χ _ => by rw [hδcoef χ]] at heval
  have hS : δ g = (Nat.card (ConjClasses.mk h).carrier : ℂ) * (Fintype.card G : ℂ)⁻¹
      * ∑ χ : Irr G, χ g * starRingEnd ℂ (χ h) := by
    rw [heval, Finset.mul_sum]
    exact Finset.sum_congr rfl fun χ _ => by ring
  haveI : Nonempty (ConjClasses.mk h).carrier := ⟨⟨h, ConjClasses.mem_carrier_mk⟩⟩
  have hcar0 : (Nat.card (ConjClasses.mk h).carrier : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hG0 : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases hgh : IsConj g h
  · rw [if_pos hgh, Subgroup.card_centralizer_eq_of_isConj hgh]
    have hδg : δ g = 1 := by
      rw [hδ g, if_pos (ConjClasses.mk_eq_mk_iff_isConj.mpr hgh)]
    rw [hδg] at hS
    have hmulC : (Nat.card (ConjClasses.mk h).carrier : ℂ)
        * (Nat.card (Subgroup.centralizer ({h} : Set G)) : ℂ) = (Fintype.card G : ℂ) := by
      rw [← Nat.cast_mul, ConjClasses.nat_card_carrier_mul_card_centralizer h,
        Nat.card_eq_fintype_card]
    field_simp at hS
    -- `hS : |G| = |class| * ∑ ...`; combine with `|class| * |centralizer| = |G|`
    have := hmulC.trans hS
    exact (mul_left_cancel₀ hcar0 this).symm
  · rw [if_neg hgh]
    have hδg : δ g = 0 := by
      rw [hδ g, if_neg fun hc => hgh (ConjClasses.mk_eq_mk_iff_isConj.mp hc)]
    rw [hδg] at hS
    have hc' : (Nat.card (ConjClasses.mk h).carrier : ℂ) * (Fintype.card G : ℂ)⁻¹ ≠ 0 :=
      mul_ne_zero hcar0 (inv_ne_zero hG0)
    exact (mul_eq_zero.mp hS.symm).resolve_left hc'

end SecondOrthogonality

