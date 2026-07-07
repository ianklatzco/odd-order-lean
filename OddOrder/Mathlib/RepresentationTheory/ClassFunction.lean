/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.GroupAction.ConjAct
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
* **Irreducibility via the group algebra.** `Irr G` is defined through simple submodules of
  `MonoidAlgebra ℂ G` (every simple module is isomorphic to one, so this is no loss:
  `Representation.classFunction_mem_irr` recovers arbitrary irreducible representations).
  This keeps the completeness proof self-contained: it needs Schur's lemma
  (`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`), Maschke's theorem
  (`IsSemisimpleModule (MonoidAlgebra ℂ G) _`), and the center of the group algebra —
  but *not* the Wedderburn pi-of-matrix-algebras decomposition nor any categorical
  transport of `CategoryTheory.Simple` between `FDRep` and module categories.
  The bridge to `Representation.IsIrreducible` is `Representation.isIrreducible_ofModule`
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
def MonoidAlgebra.centerEquivClassFunction [Fintype G] :
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

theorem MonoidAlgebra.finrank_center [Fintype G] :
    Module.finrank ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G)) = Nat.card (ConjClasses G) := by
  rw [(MonoidAlgebra.centerEquivClassFunction G).finrank_eq,
    ClassFunction.finrank_classFunction]

end Center

