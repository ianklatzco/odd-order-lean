/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import OddOrder.Mathlib.GroupTheory.SchurZassenhaus
import OddOrder.Mathlib.RepresentationTheory.CharacterArith
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-!
# Burnside's `p^a q^b` theorem

This file is Task 5 of the M2 character-theory plan, the milestone headline of this port:
Burnside's theorem that every finite group of order `p^a q^b` (`p, q` prime) is solvable.
Corresponds to standalone Mathlib-first target material; the exact MathComp counterpart name
(the Coq development proves this as `Burnside_normal_complement`-adjacent material inside
`BGsection1.v`/`PFsection1.v`) was not confirmed against a Coq checkout.

## Main results (three stages)

* **Stage 1 — the nonvanishing dichotomy** (`Irr.eq_zero_or_norm_eq`): if the conjugacy class
  of `g` has size coprime to `χ 1`, then `χ g = 0` or `‖χ g‖ = χ 1`. This is the one genuinely
  analytic ingredient (Risk 1 of the M2 plan); route: Bezout combines the algebraic integers
  `ω_χ` and `χ g` into an algebraic integer `α := χ g / χ 1`; `α` embeds into a cyclotomic
  number field, where **Kronecker's theorem**
  (`NumberField.Embeddings.pow_eq_one_of_norm_le_one`) shows a nonzero algebraic integer, all
  of whose conjugates lie in the closed unit disc, is a root of unity — hence `‖α‖ = 1`.
* **Stage 2 — the class-size lemma** (`not_isSimpleGroup_of_conjClasses_card_eq_prime_pow`):
  a conjugacy class of prime-power size forces `G` to be non-simple or abelian, via the
  character kernels `Irr.ker` (now in `CharacterArith.lean`; promoted by M3 Task 4).
* **Stage 3 — the theorem** (`burnside_solvable`): strong induction on `|G|` via normal
  subgroups (when they exist) and, in the simple case, the Sylow-center pigeonhole.

## Design notes

* **Kronecker's theorem over the norm-product route.** The M2 plan's Risk 1 sketch anticipated
  `Algebra.norm_eq_prod_embeddings` plus rational-integer descent; a from-scratch Mathlib audit
  (see the task report) found `NumberField.Embeddings.pow_eq_one_of_norm_le_one` gives the same
  conclusion (`x ≠ 0 → IsIntegral ℤ x → (∀ φ, ‖φ x‖ ≤ 1) → ∃ n > 0, x ^ n = 1`) directly from a
  *weak* (`≤ 1`) bound at *every* embedding, with no separability/norm-integrality/rational-
  descent machinery needed at all. This is strictly less code and is the route taken here.
* **Eigen-projection kit and `Irr.ker` promoted out (M3 Task 4).** The eigen-projection
  construction, the scalar-action lemma
  (`Module.End.eq_smul_one_of_trace_eq_mul_finrank`), and the character-kernel API
  (`Irr.ker`, `Irr.mem_ker_iff`, `Irr.eq_one_of_ker_eq_top`) originally lived here as a
  deliberately local kit (see the M2 Task 5 report); they now live in `CharacterArith.lean`
  (statements unchanged), promoted per the M2 deferred-consolidation list when Frobenius'
  kernel theorem (`FrobeniusKernel.lean`) became their second consumer. This file keeps only
  its private specialization `Irr.exists_scalar_of_norm_eq_degree`.
-/

noncomputable section

open Finset LinearMap Module
open scoped ClassFunction

universe u

/-! ### Stage 1: the nonvanishing dichotomy

The one analytic ingredient (Risk 1 of the M2 plan). If the conjugacy class of `g` has size
coprime to `χ 1`, then `χ g = 0` or `χ g` has the same norm as `χ 1`. -/

section Dichotomy

variable {G : Type u} [Group G] [Fintype G]

/-- The character value `χ g` decomposes as a `ℕ`-weighted sum of powers of a fixed primitive
`orderOf g`-th root of unity `ζ`, with weights summing to the degree `χ 1`. Reconstructs (for a
witnessing simple module) the same trace decomposition `Irr.isIntegral_apply` uses, exposing
both the `k = 1` and `k = 0` instances needed here. -/
private theorem Irr.exists_eq_sum_zeta_pow_mul_natCast (χ : Irr G) (g : G) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (orderOf g)) :
    ∃ m : ℕ → ℕ, χ g = ∑ j ∈ range (orderOf g), ζ ^ j * (m j : ℂ)
      ∧ ∑ j ∈ range (orderOf g), (m j : ℂ) = χ 1 := by
  obtain ⟨N, hN, hχ⟩ := χ.exists_simple'
  haveI := hN
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hpow1 : (MonoidAlgebra.actionEnd (↥N) g) ^ orderOf g = 1 := by
    rw [← MonoidAlgebra.ofModule'_eq_actionEnd, ← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨m, hm⟩ := Module.End.trace_eq_sum_zeta_pow_mul_natCast hn hpow1 hζ
  have hχg : χ g = trace ℂ (↥N) (MonoidAlgebra.actionEnd (↥N) g) := by
    have := congrArg (fun φ : ClassFunction G => φ g) hχ
    simpa [MonoidAlgebra.moduleCharacter_apply] using this
  have hχ1 : χ 1 = (Module.finrank ℂ (↥N) : ℂ) := by
    have := congrArg (fun φ : ClassFunction G => φ 1) hχ
    simpa [MonoidAlgebra.moduleCharacter_one] using this
  refine ⟨m, ?_, ?_⟩
  · have h1 := hm 1
    rw [hχg]
    simpa using h1
  · have h0 := hm 0
    simp only [pow_zero, one_mul] at h0
    rw [LinearMap.trace_one ℂ (↥N)] at h0
    rw [hχ1, h0]

/-- **The nonvanishing dichotomy.** If the size of the conjugacy class of `g` is coprime to
the degree `d = χ 1`, then `χ g = 0`, or `χ g` has the same norm as `χ 1`. The crux of
Burnside's `p^a q^b` theorem. -/
theorem Irr.eq_zero_or_norm_eq (χ : Irr G) (g : G) {d : ℕ} (hd : (χ 1 : ℂ) = d)
    (hcop : Nat.Coprime (Nat.card (ConjClasses.mk g).carrier) d) :
    χ g = 0 ∨ ‖χ g‖ = (d : ℝ) := by
  classical
  set c : ConjClasses G := ConjClasses.mk g with hcdef
  have hd0 : d ≠ 0 := by
    obtain ⟨d', hd'0, hd'⟩ := χ.exists_degree
    have : (d : ℂ) = (d' : ℂ) := hd.symm.trans hd'
    have : d = d' := by exact_mod_cast this
    rw [this]; exact hd'0.ne'
  -- Bezout: `∃ u v : ℤ, u * |c| + v * d = 1`
  obtain ⟨u, v, huv⟩ := hcop.isCoprime
  -- `ω_χ(c) = |c| * χ g / d` (bridging `c.out` conjugate to `g`)
  have hcout : χ c.out = χ g := by
    have hxc : IsConj c.out g :=
      ConjClasses.mk_eq_mk_iff_isConj.mp
        ((ConjClasses.mem_carrier_iff_mk_eq.mp
          (ConjClasses.mem_carrier_iff_mk_eq.mpr c.out_eq)).trans (hcdef ▸ rfl))
    have := χ.toClassFunction.apply_eq_of_isConj hxc
    simpa using this
  have homega : Irr.omega χ c = (Nat.card c.carrier : ℂ) * χ g / d := by
    rw [Irr.omega_eq, hcout, hd]
  have hcardmul : (Nat.card c.carrier : ℂ) * (χ g / d) = Irr.omega χ c := by
    rw [homega, mul_div_assoc]
  -- `α := χ g / d` is an algebraic integer via the Bezout combination
  set α : ℂ := χ g / d with hαdef
  have hdCne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have hdα : (d : ℂ) * α = χ g := by rw [hαdef, mul_div_cancel₀ _ hdCne]
  have hαcomb : α = (u : ℂ) * Irr.omega χ c + (v : ℂ) * χ g := by
    have hcast : (u : ℂ) * (Nat.card c.carrier : ℂ) + (v : ℂ) * (d : ℂ) = 1 := by
      have := congrArg (fun z : ℤ => (z : ℂ)) huv
      push_cast at this
      linear_combination this
    rw [← hcardmul, ← hdα]
    linear_combination (-α) * hcast
  have hαint : IsIntegral ℤ α := by
    rw [hαcomb]
    exact IsIntegral.add (IsIntegral.mul (isIntegral_intCast u) (Irr.isIntegral_omega χ c))
      (IsIntegral.mul (isIntegral_intCast v) (Irr.isIntegral_apply χ g))
  by_cases hα0 : α = 0
  · left
    rw [hαdef, div_eq_zero_iff] at hα0
    exact hα0.resolve_right hdCne
  · right
    -- transport `α` into a cyclotomic number field and apply Kronecker's theorem
    set n : ℕ := orderOf g with hndef
    have hn : n ≠ 0 := (orderOf_pos g).ne'
    haveI : NeZero n := ⟨hn⟩
    haveI : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
      CyclotomicField.isCyclotomicExtension n ℚ
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζdef
    have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn
    obtain ⟨m, hmeq, hmsum⟩ := Irr.exists_eq_sum_zeta_pow_mul_natCast χ g hζ
    haveI : NumberField (CyclotomicField n ℚ) := inferInstance
    have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
      Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hn)
    have hζK : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)) n :=
      IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)
    have hζmem : ζ ∈ primitiveRoots n ℂ := (mem_primitiveRoots (Nat.pos_of_ne_zero hn)).mpr hζ
    set φ0 : CyclotomicField n ℚ →ₐ[ℚ] ℂ :=
      (hζK.embeddingsEquivPrimitiveRoots ℂ hirr).symm ⟨ζ, hζmem⟩ with hφ0def
    have hφ0ζ : φ0 (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)) = ζ := by
      have := IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe hζK ℂ hirr φ0
      rw [hφ0def, Equiv.apply_symm_apply] at this
      exact this.symm
    have hdKne : (d : CyclotomicField n ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
    set x : CyclotomicField n ℚ :=
      (∑ j ∈ range n, (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)) ^ j
        * (m j : CyclotomicField n ℚ)) / (d : CyclotomicField n ℚ) with hxdef
    have hdxeq : (d : CyclotomicField n ℚ) * x = ∑ j ∈ range n,
        (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)) ^ j
          * (m j : CyclotomicField n ℚ) := by
      rw [hxdef, mul_div_cancel₀ _ hdKne]
    -- every ring hom `K →+* ℂ` sends `x` to a value of norm `≤ 1`
    have hbound : ∀ φ : CyclotomicField n ℚ →+* ℂ, ‖φ x‖ ≤ 1 := by
      intro φ
      have hinjφ : Function.Injective φ := RingHom.injective φ
      have hζφ : IsPrimitiveRoot (φ (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ))) n :=
        hζK.map_of_injective hinjφ
      have himg : (d : ℂ) * φ x = ∑ j ∈ range n,
          (φ (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ))) ^ j * (m j : ℂ) := by
        have := congrArg φ hdxeq
        rw [map_mul, map_natCast, map_sum] at this
        rw [this]
        exact Finset.sum_congr rfl fun j _ => by rw [map_mul, map_pow, map_natCast]
      have hnorm_eq : ‖(d : ℂ) * φ x‖ ≤ ∑ j ∈ range n,
          ‖(φ (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ))) ^ j * (m j : ℂ)‖ := by
        rw [himg]; exact norm_sum_le _ _
      have hterm : ∀ j ∈ range n,
          ‖(φ (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ))) ^ j * (m j : ℂ)‖
          = (m j : ℝ) := by
        intro j _
        rw [norm_mul, norm_pow, Complex.norm_eq_one_of_pow_eq_one hζφ.pow_eq_one hn, one_pow,
          one_mul, Complex.norm_natCast]
      rw [Finset.sum_congr rfl hterm] at hnorm_eq
      have hmsumreal : ∑ j ∈ range n, (m j : ℝ) = (d : ℝ) := by
        have hre := congrArg Complex.re hmsum
        rw [Complex.re_natCast_finset_sum, hd, Complex.natCast_re] at hre
        exact hre
      rw [hmsumreal] at hnorm_eq
      have hdCnorm : ‖(d : ℂ) * φ x‖ = (d : ℝ) * ‖φ x‖ := by
        rw [norm_mul, Complex.norm_natCast]
      rw [hdCnorm] at hnorm_eq
      have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd0)
      exact le_of_mul_le_mul_left (by rwa [mul_one]) hdpos
    -- `x ≠ 0` and `IsIntegral ℤ x`, transported from `α`
    have hφ0x : φ0 x = α := by
      have hdφ0x : (d : ℂ) * φ0 x = ∑ j ∈ range n, ζ ^ j * (m j : ℂ) := by
        have heq0 := congrArg φ0 hdxeq
        rw [map_mul, map_natCast, map_sum] at heq0
        rw [heq0]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_pow, map_natCast, hφ0ζ]
      rw [← hmeq] at hdφ0x
      have hcancel : (d : ℂ) * φ0 x = (d : ℂ) * α := by
        rw [hdφ0x, hαdef, mul_div_cancel₀ _ hdCne]
      exact mul_left_cancel₀ hdCne hcancel
    have hxne0 : x ≠ 0 := fun h => hα0 (by rw [← hφ0x, h, map_zero])
    have hxint : IsIntegral ℤ x := by
      have hinj0 : Function.Injective (φ0.toRingHom.toIntAlgHom : CyclotomicField n ℚ →ₐ[ℤ] ℂ) :=
        RingHom.injective φ0.toRingHom
      refine (isIntegral_algHom_iff
        (φ0.toRingHom.toIntAlgHom : CyclotomicField n ℚ →ₐ[ℤ] ℂ) hinj0).mp ?_
      change IsIntegral ℤ (φ0 x)
      rw [hφ0x]
      exact hαint
    obtain ⟨n', hn'pos, hxn'⟩ :=
      NumberField.Embeddings.pow_eq_one_of_norm_le_one (CyclotomicField n ℚ) ℂ hxne0 hxint hbound
    have hαn' : α ^ n' = 1 := by
      rw [← hφ0x, ← map_pow, hxn', map_one]
    have hnorm1 : ‖α‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hαn' hn'pos.ne'
    have : ‖χ g‖ / d = 1 := by
      rw [hαdef, norm_div, Complex.norm_natCast] at hnorm1
      exact hnorm1
    rw [div_eq_one_iff_eq (Nat.cast_ne_zero.mpr hd0 : (d:ℝ) ≠ 0)] at this
    exact this

end Dichotomy

/-! ### Stage 2: the scalar-action specialization and the class-size lemma

The character-kernel API (`Irr.ker`, `Irr.mem_ker_iff`, `Irr.eq_one_of_ker_eq_top`) is
imported from `CharacterArith.lean` (promoted there by M3 Task 4). The class-size lemma is
the second analytic ingredient of Burnside's theorem: a conjugacy class of prime-power size
forces `G` to be non-simple or abelian. -/

section Kernel

variable {G : Type u} [Group G] [Fintype G]

/-- **Scalar-action lemma.** If `‖χ g‖ = χ 1`, the action of `g` on a witnessing simple module
is literally a scalar `λ` (`‖λ‖ = 1`, `χ g = λ * χ 1`) — the equality case of the trace bound
at a general (not necessarily `1`) unimodular target. -/
private theorem Irr.exists_scalar_of_norm_eq_degree (χ : Irr G) (g : G) {d : ℕ}
    (hd : (χ 1 : ℂ) = d) (heq : ‖χ g‖ = (d : ℝ)) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ χ g = lam * d ∧
      Representation.ofModule' (k := ℂ) (G := G) χ.exists_simple'.choose g
        = lam • (1 : Module.End ℂ χ.exists_simple'.choose) := by
  set N := χ.exists_simple'.choose with hNdef
  haveI hN : IsSimpleModule (MonoidAlgebra ℂ G) N := χ.exists_simple'.choose_spec.1
  haveI : Nontrivial N := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) N
  have hχ : χ.toClassFunction = MonoidAlgebra.moduleCharacter G N :=
    χ.exists_simple'.choose_spec.2
  have hχg : χ g = trace ℂ N (MonoidAlgebra.actionEnd N g) := by
    have := congrArg (fun φ : ClassFunction G => φ g) hχ
    simpa [MonoidAlgebra.moduleCharacter_apply] using this
  have hχ1 : χ 1 = (Module.finrank ℂ N : ℂ) := by
    have := congrArg (fun φ : ClassFunction G => φ 1) hχ
    simpa [MonoidAlgebra.moduleCharacter_one] using this
  have hd0 : d ≠ 0 := by
    obtain ⟨d', hd'0, hd'⟩ := χ.exists_degree
    have : (d : ℂ) = (d' : ℂ) := hd.symm.trans hd'
    have hdd' : d = d' := by exact_mod_cast this
    rw [hdd']; exact hd'0.ne'
  have hdCne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  set lam : ℂ := χ g / d with hlamdef
  have hlamnorm : ‖lam‖ = 1 := by
    rw [hlamdef, norm_div, heq, Complex.norm_natCast,
      div_self (Nat.cast_ne_zero.mpr hd0 : (d : ℝ) ≠ 0)]
  have hlameq : χ g = lam * d := by rw [hlamdef, div_mul_cancel₀ _ hdCne]
  have hdeq : (d : ℂ) = (Module.finrank ℂ N : ℂ) := hd.symm.trans hχ1
  have htrace : trace ℂ N (MonoidAlgebra.actionEnd N g) = lam * (Module.finrank ℂ N : ℂ) := by
    rw [← hχg, hlameq, hdeq]
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hpow1 : (MonoidAlgebra.actionEnd N g) ^ orderOf g = 1 := by
    rw [← MonoidAlgebra.ofModule'_eq_actionEnd, ← map_pow, pow_orderOf_eq_one, map_one]
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / orderOf g) with hζdef
  have hζ : IsPrimitiveRoot ζ (orderOf g) := Complex.isPrimitiveRoot_exp (orderOf g) hn
  have hscalar := Module.End.eq_smul_one_of_trace_eq_mul_finrank hn hpow1 hζ hlamnorm htrace
  refine ⟨lam, hlamnorm, hlameq, ?_⟩
  rw [MonoidAlgebra.ofModule'_eq_actionEnd]
  exact hscalar

end Kernel

section ClassSize

variable {G : Type u} [Group G] [Fintype G]

/-- The degree of an irreducible character, as a natural number (choice witness of
`Irr.exists_degree`). -/
noncomputable def Irr.degreeNat (χ : Irr G) : ℕ := χ.exists_degree.choose

theorem Irr.degreeNat_pos (χ : Irr G) : 0 < χ.degreeNat := χ.exists_degree.choose_spec.1

theorem Irr.degreeNat_spec (χ : Irr G) : (χ 1 : ℂ) = (χ.degreeNat : ℂ) :=
  χ.exists_degree.choose_spec.2

set_option linter.unusedFintypeInType false in
/-- **Class-size lemma**: a conjugacy class of prime-power size forces `G` to be non-simple or
abelian. Second orthogonality at `(g, 1)` splits off the trivial character; if every
nonprincipal character either vanishes at `g` or has `p`-divisible degree, the residual sum is
a rational algebraic integer with denominator `p` — impossible. So some nonprincipal `χ` has
`p ∤ χ 1` and `χ g ≠ 0`; the dichotomy and scalar-action lemma show `g` acts as a scalar on a
witnessing module for `χ`, forcing every commutator `[g, h]` into `χ.ker`; simplicity collapses
`χ.ker` to `⊥`, putting `g` in the center, hence (again by simplicity) forcing `G` abelian. -/
theorem not_isSimpleGroup_of_conjClasses_card_eq_prime_pow [IsSimpleGroup G]
    (hab : ¬ IsMulCommutative G) {p k : ℕ} (hp : p.Prime) {g : G} (hg1 : g ≠ 1)
    (hcard : Nat.card (ConjClasses.mk g).carrier = p ^ k) : False := by
  classical
  have hgconj : ¬ IsConj g 1 := fun hc => hg1 (isConj_one_left.mp hc)
  have hsum0 : ∑ χ : Irr G, χ g * starRingEnd ℂ (χ 1) = 0 := by
    have h2 := Irr.second_orthogonality g 1
    rwa [if_neg hgconj] at h2
  have hreal : ∀ χ : Irr G, starRingEnd ℂ (χ 1) = χ 1 := fun χ => by
    rw [χ.degreeNat_spec, map_natCast]
  have hsum0' : ∑ χ : Irr G, χ g * χ 1 = 0 := by
    rw [← hsum0]; exact Finset.sum_congr rfl fun χ _ => by rw [hreal χ]
  have hone_term : (Irr.one : Irr G) g * (Irr.one : Irr G) 1 = 1 := by
    rw [Irr.one_apply, Irr.one_apply, mul_one]
  have hsplit : (Irr.one : Irr G) g * (Irr.one : Irr G) 1
      + ∑ χ ∈ Finset.univ.erase (Irr.one : Irr G), χ g * χ 1 = 0 := by
    rw [Finset.add_sum_erase Finset.univ (fun χ : Irr G => χ g * χ 1)
      (Finset.mem_univ (Irr.one : Irr G))]
    exact hsum0'
  rw [hone_term] at hsplit
  have hsum2 : ∑ χ ∈ Finset.univ.erase (Irr.one : Irr G), χ g * χ 1 = -1 := by
    linear_combination hsplit
  by_cases hexists : ∃ χ0 ∈ Finset.univ.erase (Irr.one : Irr G),
      ¬ (p ∣ χ0.degreeNat) ∧ χ0 g ≠ 0
  · -- the good case: some nonprincipal character with `p ∤ deg` and nonvanishing value at `g`
    obtain ⟨χ0, hχ0mem, hndvd, hgne⟩ := hexists
    have hcop : Nat.Coprime (Nat.card (ConjClasses.mk g).carrier) χ0.degreeNat := by
      rw [hcard]
      exact ((hp.coprime_iff_not_dvd.mpr hndvd).pow_left k)
    have hdich := Irr.eq_zero_or_norm_eq χ0 g χ0.degreeNat_spec hcop
    have hnormeq : ‖χ0 g‖ = (χ0.degreeNat : ℝ) := hdich.resolve_left hgne
    obtain ⟨lam, _, _, hscalar⟩ :=
      Irr.exists_scalar_of_norm_eq_degree χ0 g χ0.degreeNat_spec hnormeq
    set N0 := χ0.exists_simple'.choose with hN0def
    set ρ0 := Representation.ofModule' (k := ℂ) (G := G) N0 with hρ0def
    have hcomm : ∀ h : G, ρ0 g * ρ0 h = ρ0 h * ρ0 g := by
      intro h
      rw [hscalar, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    have hgh : ∀ h : G, ρ0 (g * h) = ρ0 (h * g) := by
      intro h; rw [map_mul, map_mul, hcomm h]
    have hcommker : ∀ h : G, g * h * g⁻¹ * h⁻¹ ∈ χ0.ker := by
      intro h
      have hassoc : g * h * g⁻¹ * h⁻¹ = (g * h) * (h * g)⁻¹ := by group
      have hker_iff : g * h * g⁻¹ * h⁻¹ ∈ χ0.ker ↔ ρ0 (g * h * g⁻¹ * h⁻¹) = 1 := Iff.rfl
      rw [hker_iff, hassoc, map_mul, hgh h, ← map_mul, mul_inv_cancel, map_one]
    have hne_one : χ0 ≠ Irr.one := (Finset.mem_erase.mp hχ0mem).1
    have hkertop : χ0.ker ≠ ⊤ := fun h => hne_one (Irr.eq_one_of_ker_eq_top χ0 h)
    have hkerbot : χ0.ker = ⊥ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal χ0.ker (Irr.ker.normal χ0)).resolve_right hkertop
    have hgcenter : g ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro h
      have hh1 : g * h * g⁻¹ * h⁻¹ = 1 := by
        have hmem := hcommker h
        rwa [hkerbot, Subgroup.mem_bot] at hmem
      have hcalc : g * h * g⁻¹ * h⁻¹ * (h * g) = h * g := by rw [hh1, one_mul]
      have hcalc2 : g * h * g⁻¹ * h⁻¹ * (h * g) = g * h := by group
      rw [hcalc2] at hcalc
      exact hcalc.symm
    have hcenter_ne_bot : Subgroup.center G ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hgcenter
      exact hg1 hgcenter
    have hcenter_top : Subgroup.center G = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G)
        inferInstance).resolve_left hcenter_ne_bot
    exact hab (Subgroup.center_eq_top_iff.mp hcenter_top)
  · -- the bad case: every nonprincipal character has `p ∣ deg` or vanishes at `g` — impossible
    have hall2 : ∀ χ0 ∈ Finset.univ.erase (Irr.one : Irr G),
        p ∣ χ0.degreeNat ∨ χ0 g = 0 := by
      intro χ0 hχ0
      by_contra hcon
      push Not at hcon
      exact hexists ⟨χ0, hχ0, hcon.1, hcon.2⟩
    have hzero : ∑ χ ∈ (Finset.univ.erase (Irr.one : Irr G)).filter
        (fun χ => ¬ p ∣ χ.degreeNat), χ g * χ 1 = 0 := by
      refine Finset.sum_eq_zero fun χ hχ => ?_
      rw [Finset.mem_filter] at hχ
      rcases hall2 χ hχ.1 with h | h
      · exact absurd h hχ.2
      · rw [h, zero_mul]
    have hsplit2 : ∑ χ ∈ (Finset.univ.erase (Irr.one : Irr G)).filter
        (fun χ => p ∣ χ.degreeNat), χ g * χ 1 = -1 := by
      rw [← hsum2, ← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase (Irr.one : Irr G))
        (fun χ => p ∣ χ.degreeNat), hzero, add_zero]
    set S : ℂ := ∑ χ ∈ (Finset.univ.erase (Irr.one : Irr G)).filter
        (fun χ => p ∣ χ.degreeNat), χ g * ((χ.degreeNat / p : ℕ) : ℂ) with hSdef
    have hkeyterm : ∀ χ ∈ (Finset.univ.erase (Irr.one : Irr G)).filter
        (fun χ => p ∣ χ.degreeNat), χ g * χ 1 = (p : ℂ) * (χ g * ((χ.degreeNat / p : ℕ) : ℂ)) := by
      intro χ hχ
      rw [Finset.mem_filter] at hχ
      obtain ⟨e, he⟩ := hχ.2
      have hediv : χ.degreeNat / p = e := by rw [he]; exact Nat.mul_div_cancel_left e hp.pos
      rw [hediv, χ.degreeNat_spec, he]
      push_cast
      ring
    have hSeq : (p : ℂ) * S = -1 := by
      rw [hSdef, Finset.mul_sum, ← hsplit2]
      exact Finset.sum_congr rfl fun χ hχ => (hkeyterm χ hχ).symm
    have hSint : IsIntegral ℤ S :=
      IsIntegral.sum _ fun χ _ => IsIntegral.mul (Irr.isIntegral_apply χ g)
        (isIntegral_natCast _)
    have hSrat : S = ((-1 / p : ℚ) : ℂ) := by
      have hpCne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
      have hScomm : S * (p : ℂ) = -1 := by rw [mul_comm]; exact hSeq
      have hSeqdiv : S = -1 / (p : ℂ) := (eq_div_iff hpCne).mpr hScomm
      rw [hSeqdiv]
      push_cast
      ring
    have hqint : IsIntegral ℤ ((-1 / p : ℚ) : ℂ) := hSrat ▸ hSint
    have hinj : Function.Injective ((Rat.castHom ℂ).toIntAlgHom : ℚ →ₐ[ℤ] ℂ) := fun a b hab =>
      Rat.cast_injective (α := ℂ) hab
    have heqcast : ((Rat.castHom ℂ).toIntAlgHom : ℚ →ₐ[ℤ] ℂ) (-1 / p : ℚ) = ((-1 / p : ℚ) : ℂ) :=
      rfl
    have hqZ : IsIntegral ℤ (-1 / p : ℚ) := by
      rw [← heqcast] at hqint
      exact (isIntegral_algHom_iff ((Rat.castHom ℂ).toIntAlgHom : ℚ →ₐ[ℤ] ℂ) hinj).mp hqint
    obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff ℚ).mp inferInstance hqZ
    have hyQ : (y : ℚ) = -1 / p := by rw [← hy]; simp [algebraMap_int_eq]
    have hp2 : (2 : ℕ) ≤ p := hp.two_le
    have : ((y : ℚ) * p = -1) := by
      rw [hyQ]; field_simp
    have hpQ0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
    have hyp : (y : ℤ) * (p : ℤ) = -1 := by exact_mod_cast this
    have hdvd : (p : ℤ) ∣ (1 : ℤ) := ⟨-y, by linear_combination hyp⟩
    have hple : (p : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hdvd
    have hple' : p ≤ 1 := by exact_mod_cast hple
    omega

end ClassSize

/-! ### Stage 3: Burnside's theorem

Strong induction on `Nat.card G`: if `G` has a proper nontrivial normal subgroup, both it and
the quotient are strictly smaller and of the same `p^a q^b` form, so solvability follows from
`solvable_of_ker_le_range` and the induction hypothesis; otherwise `G` is simple, and either
abelian (done directly) or, via the Sylow-center pigeonhole and the class-size lemma, this is
impossible. -/

section BurnsideTheorem

/-- A divisor of `p ^ a * q ^ b` is itself of the form `p ^ a' * q ^ b'` (`a' ≤ a`, `b' ≤ b`):
split it as a product of a divisor of `p ^ a` and a divisor of `q ^ b`
(`exists_dvd_and_dvd_of_dvd_mul`), then each factor is a prime power (`Nat.dvd_prime_pow`). -/
private theorem exists_eq_pow_mul_pow_of_dvd {p q a b d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hd : d ∣ p ^ a * q ^ b) : ∃ a' ≤ a, ∃ b' ≤ b, d = p ^ a' * q ^ b' := by
  obtain ⟨d1, d2, hd1, hd2, hdeq⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  obtain ⟨a', ha'le, ha'eq⟩ := (Nat.dvd_prime_pow hp).mp hd1
  obtain ⟨b', hb'le, hb'eq⟩ := (Nat.dvd_prime_pow hq).mp hd2
  exact ⟨a', ha'le, b', hb'le, by rw [hdeq, ha'eq, hb'eq]⟩

/-- The `q`-adic valuation of `p ^ a * q ^ b` (for distinct primes `p, q`) is exactly `b`. Used
to compute the exact order of a Sylow `q`-subgroup. -/
private theorem factorization_pow_mul_pow_self_right {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : (p ^ a * q ^ b).factorization q = b := by
  have hqp : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  rw [Nat.factorization_mul (pow_ne_zero a hp.pos.ne') (pow_ne_zero b hq.pos.ne'),
    Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow_self hq,
    Finsupp.smul_apply, Nat.factorization_eq_zero_of_not_dvd hqp, smul_zero, zero_add]

set_option linter.unusedFintypeInType false in
/-- **Auxiliary induction for Burnside's theorem**, quantified over the group order `n`, so that
strong induction on `n` is available (the group type `G` itself cannot be inducted on). -/
private theorem burnside_solvable_aux (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∀ n : ℕ, ∀ {a b : ℕ} {G : Type*} [Group G] [Finite G],
      Nat.card G = n → n = p ^ a * q ^ b → IsSolvable G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b G _ _ hcardG hn
    classical
    haveI : Fintype G := Fintype.ofFinite G
    haveI hpfact : Fact p.Prime := ⟨hp⟩
    haveI hqfact : Fact q.Prime := ⟨hq⟩
    by_cases hn1 : n = 1
    · haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp (hn1 ▸ hcardG)).1
      infer_instance
    by_cases hcomm : ∀ x y : G, x * y = y * x
    · exact isSolvable_of_comm hcomm
    by_cases hexistsN : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤
    · obtain ⟨N, hNnormal, hNbot, hNtop⟩ := hexistsN
      haveI := hNnormal
      have hNdvd : Nat.card N ∣ Nat.card G := Subgroup.card_subgroup_dvd_card N
      have hQdvd : Nat.card (G ⧸ N) ∣ Nat.card G :=
        ⟨Nat.card N, Subgroup.card_eq_card_quotient_mul_card_subgroup N⟩
      have hNdvd' : Nat.card N ∣ p ^ a * q ^ b := by rw [← hn, ← hcardG]; exact hNdvd
      have hQdvd' : Nat.card (G ⧸ N) ∣ p ^ a * q ^ b := by rw [← hn, ← hcardG]; exact hQdvd
      obtain ⟨aN, haNle, bN, hbNle, hNeq⟩ := exists_eq_pow_mul_pow_of_dvd hp hq hNdvd'
      obtain ⟨aQ, haQle, bQ, hbQle, hQeq⟩ := exists_eq_pow_mul_pow_of_dvd hp hq hQdvd'
      have hNlt : Nat.card N < n := by rw [← hcardG]; exact Subgroup.card_lt_card_of_ne_top hNtop
      have hQlt : Nat.card (G ⧸ N) < n := by
        rw [← hcardG]; exact Subgroup.card_quotient_lt_card_of_ne_bot hNbot
      haveI hNsolv : IsSolvable N := ih (Nat.card N) hNlt rfl hNeq
      haveI hQsolv : IsSolvable (G ⧸ N) := ih (Nat.card (G ⧸ N)) hQlt rfl hQeq
      exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
        (le_of_eq (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))
    · exfalso
      haveI hGnontrivial : Nontrivial G := by
        rw [← not_subsingleton_iff_nontrivial]
        intro hsub
        exact hn1 (hcardG ▸ Nat.card_of_subsingleton (Classical.arbitrary G))
      haveI hsimple : IsSimpleGroup G := ⟨fun H hHnormal => by
        by_contra hcon
        push Not at hcon
        exact hexistsN ⟨H, hHnormal, hcon.1, hcon.2⟩⟩
      have hab : ¬ IsMulCommutative G := mt isMulCommutative_iff.mp hcomm
      have hcenterbot : Subgroup.center G = ⊥ := by
        rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
        · exact h
        · exact absurd (isMulCommutative_iff.mpr fun x y =>
            (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y).symm) hab
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · have hGcard : Nat.card G = p ^ a := by rw [hcardG, hn, hb0, pow_zero, mul_one]
        have hGpgroup : IsPGroup p G := fun g => by
          obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp (hGcard ▸ orderOf_dvd_natCard g)
          exact ⟨k, hk ▸ pow_orderOf_eq_one g⟩
        haveI := hGpgroup.center_nontrivial (G := G)
        rw [hcenterbot] at this
        exact false_of_nontrivial_of_subsingleton (⊥ : Subgroup G)
      · obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow q G))
        have hQcard : Nat.card Q = q ^ b := by
          rw [Sylow.card_eq_multiplicity, hcardG, hn,
            factorization_pow_mul_pow_self_right hp hq hpq]
        haveI hQpgroup : IsPGroup q Q := Q.isPGroup'
        haveI hQnontrivial : Nontrivial Q :=
          hQpgroup.nontrivial_iff_card.mpr ⟨b, hbpos, hQcard⟩
        haveI := hQpgroup.center_nontrivial (G := (Q : Subgroup G))
        obtain ⟨z0, hz0⟩ := exists_ne (1 : Subgroup.center (Q : Subgroup G))
        set z : G := ((z0 : (Q : Subgroup G)) : G) with hzdef
        have hzne1 : z ≠ 1 := by
          intro h
          exact hz0 (Subtype.ext (Subtype.ext h))
        have hQlecent : (Q : Subgroup G) ≤ Subgroup.centralizer {z} := by
          rintro x hx
          rw [Subgroup.mem_centralizer_iff]
          rintro y (rfl : y = z)
          have hcommQ : ∀ w : (Q : Subgroup G), w * (z0 : (Q : Subgroup G))
              = (z0 : (Q : Subgroup G)) * w :=
            fun w => Subgroup.mem_center_iff.mp z0.2 w
          have hval := congrArg (fun t : (Q : Subgroup G) => (t : G)) (hcommQ ⟨x, hx⟩)
          simpa [hzdef] using hval.symm
        have hQdvdCent : Nat.card Q ∣ Nat.card (Subgroup.centralizer ({z} : Set G)) :=
          Subgroup.card_dvd_of_le hQlecent
        obtain ⟨m, hm⟩ := hQdvdCent
        have hclasseq : Nat.card (ConjClasses.mk z).carrier
            * Nat.card (Subgroup.centralizer ({z} : Set G)) = Nat.card G :=
          ConjClasses.nat_card_carrier_mul_card_centralizer z
        have hqbne : (q ^ b : ℕ) ≠ 0 := pow_ne_zero b hq.pos.ne'
        have hcancel : Nat.card (ConjClasses.mk z).carrier * m = p ^ a := by
          have hqbm : q ^ b * m = Nat.card (Subgroup.centralizer ({z} : Set G)) := by
            rw [hQcard] at hm; exact hm.symm
          have hstep : Nat.card (ConjClasses.mk z).carrier * (q ^ b * m) = p ^ a * q ^ b := by
            rw [hqbm, hclasseq, hcardG, hn]
          have hstep2 : (Nat.card (ConjClasses.mk z).carrier * m) * q ^ b = p ^ a * q ^ b := by
            rw [← hstep]; ring
          exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hqbne) hstep2
        have hclassdvd : Nat.card (ConjClasses.mk z).carrier ∣ p ^ a :=
          ⟨m, hcancel.symm⟩
        obtain ⟨k, hkle, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hclassdvd
        rcases Nat.eq_zero_or_pos k with hk0 | _
        · -- class size 1: `z` is central, contradicting `hcenterbot`
          rw [hk0, pow_zero] at hkeq
          have hcentop : Subgroup.centralizer ({z} : Set G) = ⊤ := by
            apply Subgroup.eq_top_of_card_eq
            have hone : Nat.card (ConjClasses.mk z).carrier
                * Nat.card (Subgroup.centralizer ({z} : Set G)) = 1 * Nat.card G := by
              rw [hclasseq, one_mul]
            rw [hkeq] at hone
            simpa using hone
          have hzcenter : z ∈ Subgroup.center G := by
            rw [Subgroup.mem_center_iff]
            intro g
            have : g ∈ Subgroup.centralizer ({z} : Set G) := hcentop ▸ Subgroup.mem_top g
            exact (Subgroup.mem_centralizer_iff.mp this z rfl).symm
          rw [hcenterbot, Subgroup.mem_bot] at hzcenter
          exact hzne1 hzcenter
        · exact not_isSimpleGroup_of_conjClasses_card_eq_prime_pow hab hp hzne1 hkeq

/-- **Burnside's `p^a q^b` theorem.** Every finite group of order `p^a q^b` (`p, q` prime) is
solvable. The headline result of the M2 character-theory plan, formalized via the nonvanishing
dichotomy (Stage 1), the class-size lemma (Stage 2), and strong induction on `|G|` combined with
the Sylow-center pigeonhole for the simple case (Stage 3). -/
theorem burnside_solvable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {a b : ℕ} {G : Type*}
    [Group G] [Finite G] (h : Nat.card G = p ^ a * q ^ b) : IsSolvable G := by
  by_cases hpq : p = q
  · -- degenerate case: `p = q`, so `G` is a single prime's `p`-group, hence nilpotent/solvable
    subst hpq
    have hGcard : Nat.card G = p ^ (a + b) := by rw [h, pow_add]
    have hGpgroup : IsPGroup p G := fun g => by
      obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
        (hGcard ▸ orderOf_dvd_natCard g)
      exact ⟨k, hk ▸ pow_orderOf_eq_one g⟩
    haveI := IsPGroup.isNilpotent hGpgroup
    infer_instance
  · exact burnside_solvable_aux p q Fact.out Fact.out hpq (Nat.card G) rfl h

end BurnsideTheorem
