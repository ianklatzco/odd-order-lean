/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import OddOrder.Mathlib.RepresentationTheory.CharacterArith

/-!
# The character center and the Schur degree bound

This file is part of M6 Task 2 (the port of `PFsection1.v`): it supplies the two
`character.v` facts that Peterfalvi (1.8) rests on, namely the *character center*
`cfcenter` and the *Schur degree bound* `irr1_bound`.

## Main definitions

* `Irr.cfcenter χ : Subgroup G` — the **center of an irreducible character** `χ`, the set
  `{g | ‖χ g‖ = χ 1}` of elements on which `χ` attains its maximal modulus.  For an
  irreducible character these are exactly the group elements that act as a scalar in the
  affording representation, which is what makes the modulus-equality set a subgroup.
  MathComp: `cfcenter` (`character.v`).

## Main results

* `Irr.irr1_bound χ : (χ 1).re ^ 2 ≤ (χ.cfcenter.index : ℝ)` — the **Schur degree bound**
  `χ(1)² ≤ |G : Z(χ)|`.  Proof: `∑_{g ∈ Z(χ)} |χ g|² = |Z(χ)| · χ(1)²` (χ has modulus
  `χ(1)` on its center) is bounded by `∑_{g ∈ G} |χ g|² = |G|` (orthonormality), and
  Lagrange turns this into `χ(1)² ≤ |G : Z(χ)|`.  MathComp: `irr1_bound` (`character.v`).
* `Irr.norm_apply_eq_of_mem_center` — every central group element lies in `cfcenter`
  (Schur's lemma for a central element: it acts as a scalar); this is the bridge that lets
  (1.8) feed a group-central subgroup `D/B ≤ Z(K/B)` into the Schur bound.
* `Irr.sq_re_le_index_of_forall_norm_eq` — the reusable counting core: for **any** subgroup
  `H` on which `χ` has constant modulus `χ 1`, `χ(1)² ≤ |G : H|`.

## Implementation notes

The scalar behaviour of `χ` on its center is packaged through the auxiliary predicate
`Irr.IsScalarOn χ g` ("`g` acts as a scalar in the simple module witnessing `χ`").  Two
entry points produce it — the modulus-equality condition `‖χ g‖ = χ 1` (via the eigenvalue
equality case `Module.End.eq_smul_one_of_trace_eq_mul_finrank`, the same engine as
`Burnside.lean`) and group-centrality (via the central character `centralScalarHom`) — and
its group-closure gives `cfcenter` its subgroup structure and the modulus formula on it.
-/

universe u

open scoped ClassFunction

namespace Irr

variable {G : Type u} [Group G] [Fintype G]

/-! ### `IsScalarOn`: acting as a scalar in the affording representation -/

/-- `χ.IsScalarOn g` : the element `g` acts as a (unit-modulus) scalar on the simple module
witnessing the irreducible character `χ`.  This is the representation-level content behind
membership in the character center. -/
def IsScalarOn (χ : Irr G) (g : G) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧
    Representation.ofModule' (k := ℂ) (G := G) χ.exists_simple'.choose g
      = c • (1 : Module.End ℂ χ.exists_simple'.choose)

/-- If `g` acts as a scalar, then `χ` attains its maximal modulus `χ 1` at `g`. -/
theorem norm_apply_eq_re_one_of_isScalarOn (χ : Irr G) {g : G} (h : χ.IsScalarOn g) :
    ‖χ g‖ = (χ 1).re := by
  obtain ⟨c, hc1, hcg⟩ := h
  set N := χ.exists_simple'.choose with hNdef
  have hval : χ.toClassFunction = MonoidAlgebra.moduleCharacter G N :=
    χ.exists_simple'.choose_spec.2
  have hfd : χ 1 = (Module.finrank ℂ N : ℂ) := by
    have := congrArg (fun φ : ClassFunction G => φ 1) hval
    simpa [MonoidAlgebra.moduleCharacter_one] using this
  have hchar : χ g = LinearMap.trace ℂ N (MonoidAlgebra.actionEnd N g) := by
    have := congrArg (fun φ : ClassFunction G => φ g) hval
    simpa [MonoidAlgebra.moduleCharacter_apply] using this
  have hgc : χ g = c * (Module.finrank ℂ N : ℂ) := by
    rw [hchar, ← MonoidAlgebra.ofModule'_eq_actionEnd, hcg, map_smul, LinearMap.trace_one,
      smul_eq_mul]
  rw [hgc, norm_mul, hc1, one_mul, Complex.norm_natCast, hfd, Complex.natCast_re]

/-- The identity acts as the scalar `1`. -/
theorem isScalarOn_one (χ : Irr G) : χ.IsScalarOn 1 :=
  ⟨1, norm_one, by rw [map_one, one_smul]⟩

/-- Scalar action is closed under multiplication (a product of scalars is a scalar). -/
theorem IsScalarOn.mul {χ : Irr G} {a b : G} (ha : χ.IsScalarOn a) (hb : χ.IsScalarOn b) :
    χ.IsScalarOn (a * b) := by
  obtain ⟨ca, hca, hga⟩ := ha
  obtain ⟨cb, hcb, hgb⟩ := hb
  refine ⟨ca * cb, by rw [norm_mul, hca, hcb, mul_one], ?_⟩
  rw [map_mul, hga, hgb, smul_mul_smul_comm, mul_one]

/-- **Modulus criterion (hard direction).** If `χ` attains its maximal modulus `χ 1` at `g`,
then `g` acts as a scalar.  This is the equality case of the eigenvalue bound: `χ g` is a sum
of `χ 1` roots of unity of total modulus `χ 1`, forcing them all equal, i.e. the action of
`g` is scalar.  Engine: `Module.End.eq_smul_one_of_trace_eq_mul_finrank`. -/
theorem isScalarOn_of_norm_eq (χ : Irr G) {g : G} (heq : ‖χ g‖ = (χ 1).re) :
    χ.IsScalarOn g := by
  classical
  set N := χ.exists_simple'.choose with hNdef
  haveI hN : IsSimpleModule (MonoidAlgebra ℂ G) N := χ.exists_simple'.choose_spec.1
  haveI : Nontrivial N := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) N
  have hval : χ.toClassFunction = MonoidAlgebra.moduleCharacter G N :=
    χ.exists_simple'.choose_spec.2
  have hχg : χ g = LinearMap.trace ℂ N (MonoidAlgebra.actionEnd N g) := by
    have := congrArg (fun φ : ClassFunction G => φ g) hval
    simpa [MonoidAlgebra.moduleCharacter_apply] using this
  have hχ1 : χ 1 = (Module.finrank ℂ N : ℂ) := by
    have := congrArg (fun φ : ClassFunction G => φ 1) hval
    simpa [MonoidAlgebra.moduleCharacter_one] using this
  have hre : (χ 1).re = (Module.finrank ℂ N : ℝ) := by rw [hχ1, Complex.natCast_re]
  have hd0 : Module.finrank ℂ N ≠ 0 := by
    obtain ⟨deg, hdeg0, hdeg⟩ := χ.exists_degree
    have hcast : (Module.finrank ℂ N : ℂ) = (deg : ℂ) := by rw [← hχ1, hdeg]
    have : Module.finrank ℂ N = deg := by exact_mod_cast hcast
    rw [this]; exact hdeg0.ne'
  have hdCne : (Module.finrank ℂ N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  set lam : ℂ := χ g / (Module.finrank ℂ N : ℂ) with hlamdef
  have hlamnorm : ‖lam‖ = 1 := by
    rw [hlamdef, norm_div, Complex.norm_natCast, heq, hre,
      div_self (by exact_mod_cast hd0 : (Module.finrank ℂ N : ℝ) ≠ 0)]
  have htrace : LinearMap.trace ℂ N (MonoidAlgebra.actionEnd N g)
      = lam * (Module.finrank ℂ N : ℂ) := by
    rw [← hχg, hlamdef, div_mul_cancel₀ _ hdCne]
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hpow1 : (MonoidAlgebra.actionEnd N g) ^ orderOf g = 1 := by
    rw [← MonoidAlgebra.ofModule'_eq_actionEnd, ← map_pow, pow_orderOf_eq_one, map_one]
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / orderOf g)) (orderOf g) :=
    Complex.isPrimitiveRoot_exp (orderOf g) hn
  have hscalar := Module.End.eq_smul_one_of_trace_eq_mul_finrank hn hpow1 hζ hlamnorm htrace
  exact ⟨lam, hlamnorm, by rw [MonoidAlgebra.ofModule'_eq_actionEnd]; exact hscalar⟩

/-- **Central criterion (Schur).** A central group element acts as a scalar: `single z 1`
is central in `ℂ[G]`, so by Schur's lemma (`centralScalarHom`) it acts as a scalar on the
simple module, and being of finite order the scalar is a root of unity. -/
theorem isScalarOn_of_mem_center (χ : Irr G) {z : G} (hz : z ∈ Subgroup.center G) :
    χ.IsScalarOn z := by
  classical
  set N := χ.exists_simple'.choose with hNdef
  haveI hN : IsSimpleModule (MonoidAlgebra ℂ G) N := χ.exists_simple'.choose_spec.1
  have hval : χ.toClassFunction = MonoidAlgebra.moduleCharacter G N :=
    χ.exists_simple'.choose_spec.2
  -- `single z 1` is central in the group algebra.
  have hzc : (MonoidAlgebra.single z (1 : ℂ)) ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
    rw [MonoidAlgebra.mem_center_iff]
    intro g h
    have hcz : ∀ w : G, w * z = z * w := Subgroup.mem_center_iff.mp hz
    have hfix : h⁻¹ * z * h = z := by rw [hcz h⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    have hfix' : h * z * h⁻¹ = z := by rw [hcz h, mul_inv_cancel_right]
    have hcond : (z = h * g * h⁻¹) ↔ (z = g) := by
      constructor
      · intro he
        have hg' : h⁻¹ * z * h = g := by rw [he]; group
        rw [hfix] at hg'; exact hg'
      · intro he
        rw [← he]; exact hfix'.symm
    simp only [MonoidAlgebra.single_apply, hcond]
  set c : ℂ := MonoidAlgebra.centralScalarHom N ⟨MonoidAlgebra.single z 1, hzc⟩ with hcdef
  -- The action of `z` is scalar multiplication by `c`.
  have hlhs : LinearMap.restrictScalars ℂ (MonoidAlgebra.centralAction hzc N)
      = MonoidAlgebra.actionEnd N z := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [LinearMap.restrictScalars_apply, MonoidAlgebra.centralAction_coe,
      MonoidAlgebra.actionEnd_apply, Submodule.coe_smul, smul_eq_mul]
  have hact : MonoidAlgebra.actionEnd N z = c • (1 : Module.End ℂ N) := by
    rw [← hlhs, MonoidAlgebra.restrictScalars_centralAction, Module.End.one_eq_id]
  -- `c` is a root of unity.
  have hfr : (Module.finrank ℂ N : ℂ) ≠ 0 := by
    obtain ⟨deg, hdeg0, hdeg⟩ := χ.exists_degree
    have hfd : χ 1 = (Module.finrank ℂ N : ℂ) := by
      have := congrArg (fun φ : ClassFunction G => φ 1) hval
      simpa [MonoidAlgebra.moduleCharacter_one] using this
    rw [← hfd, hdeg]; exact Nat.cast_ne_zero.mpr hdeg0.ne'
  have hord : orderOf z ≠ 0 := (orderOf_pos z).ne'
  have hcpow : c ^ orderOf z = 1 := by
    have h1 : (MonoidAlgebra.actionEnd N z) ^ orderOf z = 1 := by
      rw [← MonoidAlgebra.ofModule'_eq_actionEnd, ← map_pow, pow_orderOf_eq_one, map_one]
    rw [hact, ← Algebra.algebraMap_eq_smul_one, ← map_pow] at h1
    have h2 := congrArg (LinearMap.trace ℂ N) h1
    rw [Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one, smul_eq_mul] at h2
    exact mul_right_cancel₀ hfr (by rw [one_mul]; exact h2)
  exact ⟨c, Complex.norm_eq_one_of_pow_eq_one hcpow hord, by
    rw [MonoidAlgebra.ofModule'_eq_actionEnd]; exact hact⟩

/-! ### The character center -/

/-- **The center of an irreducible character** `Z(χ) = {g | ‖χ g‖ = χ 1}` (MathComp:
`cfcenter`).  It is a subgroup: the identity and inverses are immediate (`χ` is a character,
so `χ g⁻¹ = conj (χ g)`), and closure under multiplication is the scalar behaviour of `χ` on
its center. -/
def cfcenter (χ : Irr G) : Subgroup G where
  carrier := {g | ‖χ g‖ = (χ 1).re}
  one_mem' := norm_apply_eq_re_one_of_isScalarOn χ (isScalarOn_one χ)
  mul_mem' {a b} ha hb :=
    norm_apply_eq_re_one_of_isScalarOn χ
      ((isScalarOn_of_norm_eq χ ha).mul (isScalarOn_of_norm_eq χ hb))
  inv_mem' {a} ha := by
    have hval : χ.toClassFunction
        = MonoidAlgebra.moduleCharacter G χ.exists_simple'.choose :=
      χ.exists_simple'.choose_spec.2
    have hinv : χ a⁻¹ = starRingEnd ℂ (χ a) := by
      have hval' : ∀ x : G, χ x
          = (Representation.ofModule' (k := ℂ) (G := G) χ.exists_simple'.choose).character x :=
        fun x => by
          have := congrArg (fun φ : ClassFunction G => φ x) hval
          simpa [MonoidAlgebra.moduleCharacter_eq_ofModule'_character] using this
      rw [hval', hval', Representation.char_inv]
    change ‖χ a⁻¹‖ = (χ 1).re
    rw [hinv, RCLike.norm_conj]
    exact ha

@[simp]
theorem mem_cfcenter_iff (χ : Irr G) {g : G} : g ∈ χ.cfcenter ↔ ‖χ g‖ = (χ 1).re :=
  Iff.rfl

/-- Every group-central element lies in the character center: it acts as a scalar (Schur),
so `χ` attains its maximal modulus there. -/
theorem norm_apply_eq_of_mem_center (χ : Irr G) {z : G} (hz : z ∈ Subgroup.center G) :
    ‖χ z‖ = (χ 1).re :=
  norm_apply_eq_re_one_of_isScalarOn χ (isScalarOn_of_mem_center χ hz)

/-! ### The Schur degree bound -/

/-- **Counting core of the Schur bound.** For any subgroup `H` on which the irreducible
character `χ` has constant modulus `χ 1`, `χ(1)² ≤ |G : H|`.  Proof: `∑_{g ∈ H} |χ g|² =
|H| · χ(1)²` is bounded by `∑_{g ∈ G} |χ g|² = |G|` (first orthogonality), and Lagrange
`|H| · |G:H| = |G|` divides through. -/
theorem sq_re_le_index_of_forall_norm_eq (χ : Irr G) (H : Subgroup G)
    (hH : ∀ g ∈ H, ‖χ g‖ = (χ 1).re) :
    (χ 1).re ^ 2 ≤ (H.index : ℝ) := by
  classical
  -- `∑_g |χ g|² = |G|`.
  have hnorm : ⟪χ.toClassFunction, χ.toClassFunction⟫_[G] = 1 := by
    rw [Irr.cfInner_eq]; simp
  have hsumC : ∑ g : G, χ g * starRingEnd ℂ (χ g) = (Fintype.card G : ℂ) := by
    have h := hnorm
    rw [ClassFunction.cfInner_def] at h
    have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    calc ∑ g : G, χ g * starRingEnd ℂ (χ g)
        = (Fintype.card G : ℂ) * ((Fintype.card G : ℂ)⁻¹ * ∑ g : G, χ g * starRingEnd ℂ (χ g)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
      _ = (Fintype.card G : ℂ) * 1 := by
          rw [show (Fintype.card G : ℂ)⁻¹ * ∑ g : G, χ g * starRingEnd ℂ (χ g)
              = ⟪χ.toClassFunction, χ.toClassFunction⟫_[G] from
            (ClassFunction.cfInner_def _ _).symm, hnorm]
      _ = (Fintype.card G : ℂ) := mul_one _
  have hsumR : ∑ g : G, Complex.normSq (χ g) = (Fintype.card G : ℝ) := by
    have hcast : ((∑ g : G, Complex.normSq (χ g) : ℝ) : ℂ) = (Fintype.card G : ℂ) := by
      push_cast
      rw [← hsumC]
      exact Finset.sum_congr rfl fun g _ => (Complex.mul_conj (χ g)).symm
    exact_mod_cast hcast
  -- Restrict the sum to `H`.
  set S := Finset.univ.filter (fun g => g ∈ H) with hSdef
  have hle : ∑ g ∈ S, Complex.normSq (χ g) ≤ ∑ g : G, Complex.normSq (χ g) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun g _ _ => Complex.normSq_nonneg _)
  have hScard : S.card = Nat.card H := by
    rw [hSdef, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hSsum : ∑ g ∈ S, Complex.normSq (χ g) = (Nat.card H : ℝ) * (χ 1).re ^ 2 := by
    have hconst : ∀ g ∈ S, Complex.normSq (χ g) = (χ 1).re ^ 2 := by
      intro g hg
      rw [hSdef, Finset.mem_filter] at hg
      rw [Complex.normSq_eq_norm_sq, hH g hg.2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hScard, nsmul_eq_mul]
  -- Lagrange and cancellation.
  have hlag : (Nat.card H : ℝ) * (H.index : ℝ) = (Fintype.card G : ℝ) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hHpos : (0 : ℝ) < (Nat.card H : ℝ) := by exact_mod_cast Nat.card_pos
  have hchain : (Nat.card H : ℝ) * (χ 1).re ^ 2 ≤ (Nat.card H : ℝ) * (H.index : ℝ) := by
    rw [hlag, ← hSsum]
    exact hle.trans_eq hsumR
  exact le_of_mul_le_mul_left hchain hHpos

/-- **Schur degree bound** (MathComp: `irr1_bound`): the square of the degree of an
irreducible character is at most the index of its center, `χ(1)² ≤ |G : Z(χ)|`. -/
theorem irr1_bound (χ : Irr G) : (χ 1).re ^ 2 ≤ (χ.cfcenter.index : ℝ) :=
  χ.sq_re_le_index_of_forall_norm_eq χ.cfcenter fun _ hg => hg

end Irr
