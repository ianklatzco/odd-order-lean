/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Trace
import OddOrder.Mathlib.GroupTheory.AbelemRepr

/-!
# The Wielandt fixpoint order formula

Port of `wielandt_fixpoint.v` (odd-order repository).  The exported result is the
**solvable Wielandt fixpoint order formula** (Coq `solvable_Wielandt_fixpoint`), the
prerequisite for B & G Section 3 (`Frobenius_Wielandt_fixpoint`, Peterfalvi (9.1))
and Peterfalvi Section 9: for a family of subgroups `A i ≤ G` with weights
`m n : ι → ℕ` balanced on every element of `G`, and `G` acting coprimely on a
solvable group `V`,

`∏ i, |C_V(A i)| ^ (m i * |A i|) = ∏ i, |C_V(A i)| ^ (n i * |A i|)`.

We provide the external-action form `solvable_wielandt_fixpoint`
(`MulDistribMulAction G V`, the project's coprime-action convention) and the
internal form `Subgroup.solvable_wielandt_fixpoint_internal`, which mirrors the Coq
statement verbatim (subgroups `G V : Subgroup gT`, `G ≤ 'N(V)`, centralizer
intersections `'C_V(A i)`).

## The route, versus the Coq proof

The Coq proof runs: strong induction on `|V|` reducing to `V` minimal normal
elementary abelian `p`; then, to prove the resulting exponent identity mod `p ^ e`
for every `e`, it lifts `V` to a *homocyclic* group `W` of exponent `p ^ e` with
compatible `G`-action (`iso_quotient_homocyclic_sdprod`, built on the homocyclic
decomposition `coprime_act_abelian_pgroup_structure`), and computes the trace of
`∑ (a ∈ A i)` acting on `W` in two ways.

This port keeps the outer induction and the trace computation but replaces the
group-theoretic middle third by its module-theoretic content, which is where the
Coq auxiliary machinery (homocyclic groups, `Ω`/`℧` calculus, `'Z_q`-matrix rows)
collapses to standard Mathlib material:

* "homocyclic of exponent `p ^ e` and rank `dim V`" becomes "finite **free**
  `ZMod (p ^ e)`-module"; the lifting theorem becomes
  `Representation.exists_wielandt_lift`: a simple `(ZMod p)[G]`-module `V` (with
  `p ∤ |G|`) is `W ⧸ p•W` for a free `(ZMod (p ^ e))[G]`-module direct summand `W`
  of the regular module.  Freeness is by idempotent lifting along the nilpotent
  kernel of `(ZMod (p ^ e))[G] →+* (ZMod p)[G]`
  (`exists_isIdempotentElem_eq_of_ker_isNilpotent`, with the complement downstairs
  from Maschke) plus "finitely generated projective over a local ring is free"
  (`Module.free_of_flat_of_isLocalRing`; `ZMod (p ^ e)` is local).
* the Coq trace computation via the decomposition `W = [W, A] × C_W(A)` is
  replaced by the averaging idempotent `Representation.averageMap` (available in
  module language since `|A|` is invertible mod `p ^ e`): the trace of
  `∑ (a ∈ A), ρ a` is `|A| * rank C_W(A)`, and `rank C_W(A) = dim C_V(A)` because
  fixed points lift along `W → V` with kernel `p • C_W(A)`.
* the homocyclic decomposition `coprime_act_abelian_pgroup_structure` is thereby
  **bypassed entirely** (it was used only to locate the free summand of the
  regular module; projectivity does that job); it is not ported.  See
  `docs/NAME_MAP.md`.

## Main statements

* `Representation.exists_wielandt_lift` : the lifting theorem (module form of Coq
  `iso_quotient_homocyclic_sdprod`).
* `Representation.wielandt_trace_sum_eq` : the elementary abelian case, as an
  identity between weighted sums of fixed-space dimensions (the Coq proof's
  `\sum_(i | ...) rC i * k i * #|A i|` step).
* `solvable_wielandt_fixpoint` : the order formula, external action form.
* `Subgroup.solvable_wielandt_fixpoint_internal` : the order formula, internal
  form (Coq `solvable_Wielandt_fixpoint`, statement-faithful).
-/

open scoped MonoidAlgebra

/-!
### `ZMod (p ^ e)` is local, and its `p`-torsion line

The two facts about the coefficient ring `R := ZMod (p ^ e)` that drive the
counting arguments: `R` is a local ring (so finitely generated projective
`R`-modules are free), and the `p`-torsion `{x : R | p * x = 0}` has exactly `p`
elements (so the `p`-torsion of a free module of rank `r` has `p ^ r` elements).
MathComp handles both through the `'Z_q`-cyclic group calculus of `abelian.v`.
-/

section ZModPrimePow

variable {p e : ℕ}

private theorem ZMod.isUnit_of_not_prime_dvd_val (hp : p.Prime) [NeZero (p ^ e)]
    {a : ZMod (p ^ e)} (ha : ¬ p ∣ a.val) : IsUnit a := by
  rw [← ZMod.natCast_rightInverse a]
  exact (ZMod.isUnit_iff_coprime _ _).mpr
    (Nat.Coprime.pow_right e ((hp.coprime_iff_not_dvd.mpr ha).symm))

/-- `ZMod (p ^ e)` is a local ring for `p` prime and `e > 0`: every element is a
unit or a multiple of `p`, and `1` is not a multiple of `p`. -/
theorem ZMod.isLocalRing_prime_pow (hp : p.Prime) (he : e ≠ 0) :
    IsLocalRing (ZMod (p ^ e)) := by
  haveI : Fact (1 < p ^ e) := ⟨Nat.one_lt_pow he hp.one_lt⟩
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases hdvd : p ∣ a.val
  · refine Or.inr (ZMod.isUnit_of_not_prime_dvd_val hp fun hdvd' => hp.one_lt.ne' ?_)
    have hsum : p ∣ (a + (1 - a)).val := by
      rw [ZMod.val_add]
      exact (Nat.dvd_mod_iff (dvd_pow_self p he)).mpr (Nat.dvd_add hdvd hdvd')
    rw [add_sub_cancel, ZMod.val_one] at hsum
    exact (Nat.dvd_one.mp hsum)
  · exact Or.inl (ZMod.isUnit_of_not_prime_dvd_val hp hdvd)

/-- The `p`-torsion of `ZMod (p ^ e)` has exactly `p` elements (`e > 0`): it is the
image of `ZMod p` under `c ↦ c * p ^ (e - 1)`. -/
theorem ZMod.natCard_pTorsion_prime_pow (hp : p.Prime) (he : e ≠ 0) :
    Nat.card {x : ZMod (p ^ e) // (p : ZMod (p ^ e)) * x = 0} = p := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpow : p ^ (e - 1) * p = p ^ e := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he)]
  have hcast : ∀ c : ZMod p,
      (p : ZMod (p ^ e)) * ((c.val * p ^ (e - 1) : ℕ) : ZMod (p ^ e)) = 0 := by
    intro c
    have : ((p * (c.val * p ^ (e - 1)) : ℕ) : ZMod (p ^ e)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact ⟨c.val, by rw [← hpow]; ring⟩
    rwa [Nat.cast_mul] at this
  set f : ZMod p → {x : ZMod (p ^ e) // (p : ZMod (p ^ e)) * x = 0} :=
    fun c => ⟨((c.val * p ^ (e - 1) : ℕ) : ZMod (p ^ e)), hcast c⟩ with hf
  have hinj : Function.Injective f := by
    intro c₁ c₂ hcc
    have h1 : (c₁.val * p ^ (e - 1)) ≡ (c₂.val * p ^ (e - 1)) [MOD p ^ e] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp (congrArg Subtype.val hcc)
    have hlt : ∀ c : ZMod p, c.val * p ^ (e - 1) < p ^ e := by
      intro c
      calc c.val * p ^ (e - 1) < p * p ^ (e - 1) :=
            (Nat.mul_lt_mul_right (Nat.pow_pos hp.pos)).mpr (ZMod.val_lt _)
        _ = p ^ e := by rw [mul_comm, hpow]
    have := h1.eq_of_lt_of_lt (hlt c₁) (hlt c₂)
    exact ZMod.val_injective p
      (Nat.eq_of_mul_eq_mul_right (Nat.pow_pos hp.pos) this)
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hdvd : p ^ e ∣ p * x.val := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_rightInverse x]
      exact hx
    have hdvd' : p ^ (e - 1) ∣ x.val := by
      have h1 : p * p ^ (e - 1) ∣ p * x.val := by
        rwa [mul_comm p (p ^ (e - 1)), hpow]
      exact (Nat.mul_dvd_mul_iff_left hp.pos).mp h1
    obtain ⟨c, hc⟩ := hdvd'
    have hclt : c < p := by
      by_contra hle
      have : p ^ e ≤ x.val := by
        calc p ^ e = p ^ (e - 1) * p := hpow.symm
          _ ≤ p ^ (e - 1) * c := Nat.mul_le_mul_left _ (le_of_not_gt hle)
          _ = x.val := hc.symm
      exact absurd (ZMod.val_lt x) (not_lt.mpr this)
    refine ⟨(c : ZMod p), ?_⟩
    have hcval : ((c : ZMod p)).val = c := ZMod.val_cast_of_lt hclt
    refine Subtype.ext ?_
    change ((((c : ZMod p)).val * p ^ (e - 1) : ℕ) : ZMod (p ^ e)) = x
    rw [hcval, mul_comm c, ← hc, ZMod.natCast_rightInverse x]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm.trans (Nat.card_zmod p)

end ZModPrimePow

/-!
### Free direct summands and the averaging trace formula

Over a local ring, the range of an idempotent endomorphism of a finite free module
is free (this replaces the homocyclicity bookkeeping of the Coq proof), and the
trace of `∑ (a : A), ρ a` for a representation `ρ` of a finite group `A` with
`|A|` invertible is `|A| * rank (invariants)` — via Mathlib's averaging projection
`Representation.averageMap`, which replaces the Coq's `W = [W, A] × C_W(A)`
decomposition (`coprime_abelian_cent_dprod`) and its commutator-reindexing trace
computation.
-/

section FreeSummand

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The range of an idempotent endomorphism of a projective module is projective
(it is a direct summand). -/
theorem Module.projective_range_of_comp_self_eq [Module.Projective R M]
    (f : M →ₗ[R] M) (hf : f ∘ₗ f = f) :
    Module.Projective R ↥(LinearMap.range f) := by
  refine Module.Projective.of_split (LinearMap.range f).subtype f.rangeRestrict ?_
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨y, hy⟩ := x.2
  have h1 : f (f y) = f y := LinearMap.congr_fun hf y
  calc f (x : M) = f (f y) := by rw [hy]
    _ = f y := h1
    _ = (x : M) := hy

/-- **Ranges of idempotents are free** over a local ring: the range of an
idempotent endomorphism of a finite free module over a local ring is free.  This
stands in for the homocyclic factors of MathComp's
`coprime_act_abelian_pgroup_structure`. -/
theorem Module.free_range_of_comp_self_eq (hR : IsLocalRing R) [Module.Free R M]
    [Finite M] (f : M →ₗ[R] M) (hf : f ∘ₗ f = f) :
    Module.Free R ↥(LinearMap.range f) := by
  haveI := hR
  haveI := Module.projective_range_of_comp_self_eq f hf
  exact Module.free_of_flat_of_isLocalRing

/-- The kernel of an idempotent endomorphism is the range of the complementary
idempotent. -/
theorem LinearMap.ker_eq_range_one_sub_of_comp_self_eq (f : M →ₗ[R] M)
    (hf : f ∘ₗ f = f) : LinearMap.ker f = LinearMap.range (1 - f) := by
  ext x
  constructor
  · intro hx
    refine ⟨x, ?_⟩
    rw [LinearMap.sub_apply, Module.End.one_apply, LinearMap.mem_ker.mp hx, sub_zero]
  · rintro ⟨y, rfl⟩
    have h1 : f (f y) = f y := LinearMap.congr_fun hf y
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_sub, h1,
      sub_self]

/-- The kernel of an idempotent endomorphism of a finite free module over a local
ring is free. -/
theorem Module.free_ker_of_comp_self_eq (hR : IsLocalRing R) [Module.Free R M]
    [Finite M] (f : M →ₗ[R] M) (hf : f ∘ₗ f = f) :
    Module.Free R ↥(LinearMap.ker f) := by
  rw [LinearMap.ker_eq_range_one_sub_of_comp_self_eq f hf]
  refine Module.free_range_of_comp_self_eq hR _ ?_
  have h1 : (1 - f) * (1 - f) = 1 - f := by
    have hff : f * f = f := hf
    rw [mul_sub, sub_mul, sub_mul, one_mul, mul_one, hff]
    abel
  exact h1

end FreeSummand

section AveragingTrace

variable {R : Type*} [CommRing R] {H : Type*} [Group H] [Fintype H]
  [Invertible (Fintype.card H : R)]
  {M : Type*} [AddCommGroup M] [Module R M]

namespace Representation

variable (ρ : Representation R H M)

/-- The averaging map, written as an explicit smul-of-sum. -/
theorem averageMap_eq_smul_sum :
    ρ.averageMap = ⅟(Fintype.card H : R) • ∑ h : H, ρ h := by
  rw [averageMap, GroupAlgebra.average, map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun h _ => ρ.asAlgebraHom_of h

/-- The averaging map is idempotent. -/
theorem averageMap_comp_self : ρ.averageMap ∘ₗ ρ.averageMap = ρ.averageMap :=
  LinearMap.ext fun x => ρ.averageMap_id _ (ρ.averageMap_invariant x)

/-- The range of the averaging map is the invariant submodule. -/
theorem range_averageMap : LinearMap.range ρ.averageMap = ρ.invariants := by
  refine le_antisymm ?_ fun x hx => ⟨x, ρ.averageMap_id x hx⟩
  rintro _ ⟨x, rfl⟩
  exact ρ.averageMap_invariant x

/-- The sum of a representation of a finite group over all group elements is the
cardinality times the averaging projection. -/
theorem sum_eq_card_smul_averageMap :
    ∑ h : H, ρ h = (Fintype.card H : R) • ρ.averageMap := by
  rw [averageMap_eq_smul_sum, smul_smul, mul_invOf_self, one_smul]

/-- **The averaging trace formula**: over a local ring in which `|H|` is
invertible, the trace of `∑ (h : H), ρ h` on a finite free module is
`|H| * rank (invariants)`.

This is the module-theoretic replacement for the trace computation in the last
third of the Coq proof of `solvable_Wielandt_fixpoint` (the
`[~: W, Ai1] \x 'C_W(Ai1)` block-matrix argument): on the invariants each `ρ h`
is the identity, contributing the rank; the complement is the range of the
complementary idempotent, where the summed projection has trace zero. -/
theorem trace_sum_eq_card_mul_finrank_invariants (hR : IsLocalRing R)
    [Module.Free R M] [Finite M] :
    LinearMap.trace R M (∑ h : H, ρ h)
      = (Fintype.card H : R) * (Module.finrank R ↥ρ.invariants : R) := by
  have hproj : LinearMap.IsProj ρ.invariants ρ.averageMap :=
    ρ.isProj_averageMap
  haveI hfree : Module.Free R ↥ρ.invariants := by
    have h := Module.free_range_of_comp_self_eq hR _ ρ.averageMap_comp_self
    rwa [ρ.range_averageMap] at h
  haveI : Module.Free R ↥(LinearMap.ker ρ.averageMap) :=
    Module.free_ker_of_comp_self_eq hR _ ρ.averageMap_comp_self
  rw [ρ.sum_eq_card_smul_averageMap, map_smul, hproj.trace, smul_eq_mul]

end Representation

end AveragingTrace

/-!
### The regular-module lift of a simple `(ZMod p)[G]`-module

The module-theoretic content of Coq `iso_quotient_homocyclic_sdprod`: a simple
`(ZMod p)[G]`-module `V` (`p ∤ |G|`) is realized as `W ⧸ p • W` for a *free*
`ZMod (p ^ e)`-module `W` carrying a `G`-representation, together with the
matching of fixed-point data that the trace argument consumes.  `W` is a direct
summand `S * ε` of the regular module `S := (ZMod (p ^ e))[G]`, where `ε` lifts
(along the nilpotent-kernel reduction `S →+* (ZMod p)[G]`) the idempotent given by
a Maschke complement of the kernel of `(ZMod p)[G] → V`.
-/

section Lift

variable {R : Type*} [CommRing R] {G : Type*} [Group G]

open MonoidAlgebra in
/-- The representation of `G` by left multiplication on a left submodule of its
monoid algebra `R[G]` (MathComp: the action of `G` on an invariant factor of the
regular module `'rV['Z_q]_#|G|` in `wielandt_fixpoint.v`). -/
noncomputable def MonoidAlgebra.submoduleRepr
    (W : Submodule (MonoidAlgebra R G) (MonoidAlgebra R G)) :
    Representation R G ↥W where
  toFun g :=
    { toFun := fun w => ⟨MonoidAlgebra.single g 1 * (w : MonoidAlgebra R G),
        by simpa [smul_eq_mul] using W.smul_mem (MonoidAlgebra.single g 1) w.2⟩
      map_add' := fun x y => Subtype.ext (by simp [mul_add])
      map_smul' := fun c x => Subtype.ext (by simp) }
  map_one' := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    change MonoidAlgebra.single 1 1 * (w : MonoidAlgebra R G) = (w : MonoidAlgebra R G)
    rw [← MonoidAlgebra.one_def, one_mul]
  map_mul' g h := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    change MonoidAlgebra.single (g * h) 1 * (w : MonoidAlgebra R G)
      = MonoidAlgebra.single g 1 * (MonoidAlgebra.single h 1 * (w : MonoidAlgebra R G))
    rw [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul]

@[simp]
theorem MonoidAlgebra.coe_submoduleRepr_apply
    (W : Submodule (MonoidAlgebra R G) (MonoidAlgebra R G)) (g : G) (w : ↥W) :
    ((MonoidAlgebra.submoduleRepr W g w : ↥W) : MonoidAlgebra R G)
      = MonoidAlgebra.single g 1 * (w : MonoidAlgebra R G) :=
  rfl

namespace Representation

/-- **Fixed points match along the lift** (abstract form): given a surjective
additive map `φ` from a finite free `ZMod (p ^ e)`-module `W` with a
`ZMod (p ^ e)`-representation of `A` to a `ZMod p`-module `V` with a
`ZMod p`-representation of `A`, compatible with scalars via
`ZMod (p ^ e) → ZMod p`, equivariant, and with kernel `p • W`, the fixed space of
`V` has order `p ^ rank (fixed space of W)`.

This packages the fixed-point half of the Coq proof of
`solvable_Wielandt_fixpoint` (`rCW : 'r('C_W(Ai1)) = rC i` there, proved via
`coprime_quotient_cent`); here it is the coprime averaging projection plus the
purity of the direct summand `C_W(A)`. -/
private theorem card_invariants_eq_pow_finrank_of_lift {p e : ℕ} (hp : p.Prime)
    (he : e ≠ 0) {A : Type*} [Group A] [Finite A] (hA : ¬ p ∣ Nat.card A)
    {W : Type*} [AddCommGroup W] [Module (ZMod (p ^ e)) W]
    [Module.Free (ZMod (p ^ e)) W] [Finite W]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρW : Representation (ZMod (p ^ e)) A W) (ρV : Representation (ZMod p) A V)
    (φ : W →+ V) (hφsurj : Function.Surjective φ)
    (hφsmul : ∀ (c : ZMod (p ^ e)) (w : W),
      φ (c • w) = ZMod.castHom (dvd_pow_self p he) (ZMod p) c • φ w)
    (hφequiv : ∀ (a : A) (w : W), φ (ρW a w) = ρV a (φ w))
    (hφker : ∀ w : W, φ w = 0 ↔ ∃ u : W, w = (p : ZMod (p ^ e)) • u) :
    Nat.card ↥ρV.invariants = p ^ Module.finrank (ZMod (p ^ e)) ↥ρW.invariants := by
  classical
  set red : ZMod (p ^ e) →+* ZMod p := ZMod.castHom (dvd_pow_self p he) (ZMod p)
    with hreddef
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have hloc : IsLocalRing (ZMod (p ^ e)) := ZMod.isLocalRing_prime_pow hp he
  haveI : Fintype A := Fintype.ofFinite A
  -- `|A|` is invertible in `R`
  have hcop : (Nat.card A).Coprime (p ^ e) :=
    Nat.Coprime.pow_right e ((hp.coprime_iff_not_dvd.mpr hA).symm)
  haveI : Invertible ((Fintype.card A : ZMod (p ^ e))) :=
    (ZMod.unitOfCoprime _ hcop).invertible.copy _
      (by rw [ZMod.coe_unitOfCoprime, Nat.card_eq_fintype_card])
  -- `red` kills `p` and inverts `|A|`
  have hred_p : red ((p : ℕ) : ZMod (p ^ e)) = 0 := by
    rw [map_natCast red, ZMod.natCast_self]
  have hred_inv : red (⅟(Fintype.card A : ZMod (p ^ e))) * ((Fintype.card A : ℕ) : ZMod p) = 1 := by
    rw [← map_natCast red (Fintype.card A), ← map_mul, invOf_mul_self, map_one]
  -- the two fixed spaces and the averaging projection upstairs
  set I : Submodule (ZMod (p ^ e)) W := ρW.invariants with hIdef
  set J : Submodule (ZMod p) V := ρV.invariants with hJdef
  set avg : W →ₗ[ZMod (p ^ e)] W := ρW.averageMap with havgdef
  haveI : Module.Free (ZMod (p ^ e)) ↥I := by
    have h := Module.free_range_of_comp_self_eq hloc _ ρW.averageMap_comp_self
    rwa [ρW.range_averageMap] at h
  -- `φ` maps `I` to `J`, giving `ψ`
  have hφI : ∀ w : W, w ∈ I → φ w ∈ J := by
    intro w hw a
    rw [← hφequiv a w, hw a]
  set ψ : ↥I →+ ↥J :=
    AddMonoidHom.mk' (fun w => ⟨φ (w : W), hφI _ w.2⟩)
      (fun x y => Subtype.ext (by simp)) with hψdef
  -- `φ` of the averaging projection of a lift of a fixed point is that point
  have hφavg : ∀ (w : W) (v : V), v ∈ J → φ w = v → φ (avg w) = v := by
    intro w v hv hwv
    have h1 : avg w = ⅟(Fintype.card A : ZMod (p ^ e)) • ∑ a : A, ρW a w := by
      rw [havgdef, ρW.averageMap_eq_smul_sum]
      simp [LinearMap.sum_apply]
    rw [h1, hφsmul, map_sum]
    have h2 : ∀ a : A, φ (ρW a w) = v := fun a => by rw [hφequiv, hwv, hv a]
    rw [Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul (ZMod p), smul_smul, hred_inv, one_smul]
  -- `ψ` is surjective
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨v, hv⟩
    obtain ⟨w, hw⟩ := hφsurj v
    refine ⟨⟨avg w, ρW.averageMap_invariant w⟩, Subtype.ext ?_⟩
    exact hφavg w v hv hw
  -- the kernel of `ψ` is the range of multiplication by `p` on `I`
  set mI : ↥I →+ ↥I := DistribSMul.toAddMonoidHom ↥I ((p : ℕ) : ZMod (p ^ e)) with hmIdef
  have hker_eq : ψ.ker = mI.range := by
    ext w
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro hw
      have hφw : φ (w : W) = 0 := by
        have := congrArg Subtype.val hw
        simpa [hψdef] using this
      obtain ⟨u, hu⟩ := (hφker _).mp hφw
      have huI : avg u ∈ I := ρW.averageMap_invariant u
      refine ⟨⟨avg u, huI⟩, ?_⟩
      refine Subtype.ext ?_
      have h1 : (w : W) = ((p : ℕ) : ZMod (p ^ e)) • u := hu
      have h2 : avg (w : W) = (w : W) := ρW.averageMap_id _ w.2
      calc (mI ⟨avg u, huI⟩ : W) = ((p : ℕ) : ZMod (p ^ e)) • avg u := rfl
        _ = avg (((p : ℕ) : ZMod (p ^ e)) • u) := (map_smul avg _ u).symm
        _ = avg (w : W) := by rw [← h1]
        _ = (w : W) := h2
    · rintro ⟨u, rfl⟩
      refine Subtype.ext ?_
      have h1 : ((mI u : ↥I) : W) = ((p : ℕ) : ZMod (p ^ e)) • (u : W) := rfl
      have h2 : φ ((mI u : ↥I) : W) = 0 := by
        rw [h1, hφsmul, hreddef]
        rw [show (ZMod.castHom (dvd_pow_self p he) (ZMod p))
          ((p : ℕ) : ZMod (p ^ e)) = 0 from hred_p]
        rw [zero_smul]
      simpa [hψdef] using h2
  -- counting: `|J| = |ker mI|`
  have hcard_I₁ : Nat.card ↥I = Nat.card ↥J * Nat.card ψ.ker := by
    have h1 : Nat.card ↥I = Nat.card (↥I ⧸ ψ.ker) * Nat.card ψ.ker :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker
    have h2 : Nat.card (↥I ⧸ ψ.ker) = Nat.card ψ.range :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv
    have h3 : ψ.range = ⊤ := by
      rwa [AddMonoidHom.range_eq_top]
    have h4 : Nat.card ψ.range = Nat.card ↥J := by
      rw [h3]
      exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
    rw [h1, h2, h4]
  have hcard_I₂ : Nat.card ↥I = Nat.card (↥I ⧸ mI.ker) * Nat.card mI.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup mI.ker
  have hcard_ranges : Nat.card ψ.ker = Nat.card (↥I ⧸ mI.ker) := by
    rw [hker_eq]
    exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivRange mI).toEquiv).symm
  have hJ_eq_ker : Nat.card ↥J = Nat.card mI.ker := by
    have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
    have h5 : Nat.card ↥J * Nat.card ψ.ker = Nat.card mI.ker * Nat.card ψ.ker := by
      rw [← hcard_I₁, hcard_I₂, hcard_ranges]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h5
  -- counting the `p`-torsion of the free module `I`
  set b := Module.Free.chooseBasis (ZMod (p ^ e)) ↥I with hbdef
  have hcard_ker : Nat.card mI.ker = p ^ Module.finrank (ZMod (p ^ e)) ↥I := by
    have hmem : ∀ w : ↥I, w ∈ mI.ker ↔ ∀ j, (p : ZMod (p ^ e)) * b.equivFun w j = 0 := by
      intro w
      have h0 : w ∈ mI.ker ↔ (p : ZMod (p ^ e)) • w = 0 := Iff.rfl
      rw [h0]
      constructor
      · intro h j
        have h2 : b.equivFun ((p : ZMod (p ^ e)) • w) = 0 := by rw [h, map_zero]
        rw [map_smul] at h2
        have h3 := congrFun h2 j
        simpa [smul_eq_mul] using h3
      · intro h
        have h2 : b.equivFun ((p : ZMod (p ^ e)) • w) = 0 := by
          rw [map_smul]
          funext j
          simpa [smul_eq_mul] using h j
        have h3 : b.equivFun ((p : ZMod (p ^ e)) • w) = b.equivFun 0 := by rw [h2, map_zero]
        exact b.equivFun.injective h3
    set E : mI.ker ≃ (Module.Free.ChooseBasisIndex (ZMod (p ^ e)) ↥I →
        {x : ZMod (p ^ e) // (p : ZMod (p ^ e)) * x = 0}) :=
      { toFun := fun w j => ⟨b.equivFun (w : ↥I) j, (hmem _).mp w.2 j⟩
        invFun := fun v => ⟨b.equivFun.symm fun j => (v j : ZMod (p ^ e)), (hmem _).mpr (by
          intro j
          rw [LinearEquiv.apply_symm_apply]
          exact (v j).2)⟩
        left_inv := fun w => Subtype.ext (b.equivFun.symm_apply_apply _)
        right_inv := fun v => funext fun j => Subtype.ext (by
          change b.equivFun (b.equivFun.symm _) j = _
          rw [LinearEquiv.apply_symm_apply]) }
    rw [Nat.card_congr E, Nat.card_pi, Finset.prod_const,
      ZMod.natCard_pTorsion_prime_pow hp he, Finset.card_univ,
      Module.finrank_eq_card_chooseBasisIndex]
  rw [hJ_eq_ker, hcard_ker]

end Representation

private theorem MonoidAlgebra.ext_coeff {R M : Type*} [Semiring R]
    {x y : MonoidAlgebra R M} (h : x.coeff = y.coeff) : x = y := by
  rw [← MonoidAlgebra.ofCoeff_coeff x, ← MonoidAlgebra.ofCoeff_coeff y, h]

namespace Representation

/-- **The Wielandt lifting theorem**, module form of Coq
`iso_quotient_homocyclic_sdprod` (with the `Variant`
`is_iso_quotient_homocyclic_sdprod` packaging): a simple `(ZMod p)[G]`-module `V`
with `p ∤ |G|` lifts, for every `e ≠ 0`, to a **free** `ZMod (p ^ e)`-module
direct summand `W` of the regular module of `G` over `ZMod (p ^ e)` — free =
"homocyclic of exponent `p ^ e`", the summand `W` = the Coq `U ≤ L`, the regular
module = the Coq `'rV['Z_q]_#|G|` — such that for *every* subgroup `A ≤ G` the
fixed space of `V` under `A` has order `p ^ rank (fixed space of W under A)`.

Statement-shape note: the Coq packages `W ⋊ G` with a morphism `f` with
`'ker f = 'Mho^1(W)`, `f @* W = V`, `f @* G1 = G`; here the reduction map, its
kernel `p • W` and the `G`-equivariance live inside the proof, and the conclusion
exports exactly the fixed-point data consumed by `solvable_Wielandt_fixpoint`
(the `rCW`/`rW_V` step there).  The auxiliary homocyclic decomposition
`coprime_act_abelian_pgroup_structure` is not needed on this route: freeness of
the summand comes from idempotent lifting plus projectivity over the local ring
`ZMod (p ^ e)`. -/
theorem exists_wielandt_lift {p : ℕ} (hp : p.Prime) {e : ℕ} (he : e ≠ 0)
    {G : Type*} [Group G] [Finite G] (hG : ¬ p ∣ Nat.card G)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) G V)
    (hsimple : IsSimpleModule (MonoidAlgebra (ZMod p) G) ρ.asModule) :
    ∃ W : Submodule (MonoidAlgebra (ZMod (p ^ e)) G) (MonoidAlgebra (ZMod (p ^ e)) G),
      Module.Free (ZMod (p ^ e)) ↥W ∧
        ∀ A : Subgroup G,
          Nat.card ↥(Representation.invariants (ρ.comp A.subtype))
            = p ^ Module.finrank (ZMod (p ^ e))
                (Representation.invariants
                  ((MonoidAlgebra.submoduleRepr W).comp A.subtype)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fintype G := Fintype.ofFinite G
  have hloc : IsLocalRing (ZMod (p ^ e)) := ZMod.isLocalRing_prime_pow hp he
  set red : ZMod (p ^ e) →+* ZMod p := ZMod.castHom (dvd_pow_self p he) (ZMod p)
    with hreddef
  set F : MonoidAlgebra (ZMod (p ^ e)) G →+* MonoidAlgebra (ZMod p) G :=
    MonoidAlgebra.mapRingHom G red with hFdef
  -- `F` computes coefficientwise as `red`
  have hFcoeff : ∀ (x : MonoidAlgebra (ZMod (p ^ e)) G) (g : G),
      (F x).coeff g = red (x.coeff g) := fun x g => rfl
  -- `F` is surjective
  have hF_surj : Function.Surjective F := by
    intro t
    obtain ⟨s₀, hs₀⟩ := Finsupp.mapRange_surjective (red : ZMod (p ^ e) → ZMod p)
      (map_zero red) (ZMod.castHom_surjective _) t.coeff
    refine ⟨MonoidAlgebra.ofCoeff s₀, MonoidAlgebra.ext_coeff (Finsupp.ext fun g => ?_)⟩
    have h1 := DFunLike.congr_fun hs₀ g
    rw [Finsupp.mapRange_apply] at h1
    rw [hFcoeff, MonoidAlgebra.coeff_ofCoeff]
    exact h1
  -- division by `p` in the kernel of `red`
  have hdiv : ∀ c : ZMod (p ^ e), red c = 0 →
      c = (p : ZMod (p ^ e)) * ((c.val / p : ℕ) : ZMod (p ^ e)) := by
    intro c hc
    have h2 : ((c.val : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_val]
      exact hc
    have h1 : p ∣ c.val := (ZMod.natCast_eq_zero_iff _ _).mp h2
    calc c = ((c.val : ℕ) : ZMod (p ^ e)) := (ZMod.natCast_rightInverse c).symm
      _ = ((p * (c.val / p) : ℕ) : ZMod (p ^ e)) := by rw [Nat.mul_div_cancel' h1]
      _ = (p : ZMod (p ^ e)) * ((c.val / p : ℕ) : ZMod (p ^ e)) := by push_cast; ring
  -- elements of the kernel of `F` are multiples of `p`, hence nilpotent
  have hkerF_smul : ∀ x : MonoidAlgebra (ZMod (p ^ e)) G, F x = 0 →
      ∃ y, x = (p : ZMod (p ^ e)) • y := by
    intro x hx
    have hcoeff : ∀ g : G, red (x.coeff g) = 0 := by
      intro g
      rw [← hFcoeff, hx, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    refine ⟨MonoidAlgebra.ofCoeff (x.coeff.mapRange
      (fun c => ((c.val / p : ℕ) : ZMod (p ^ e))) (by simp)), ?_⟩
    refine MonoidAlgebra.ext_coeff (Finsupp.ext fun g => ?_)
    rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, MonoidAlgebra.coeff_ofCoeff,
      Finsupp.mapRange_apply, smul_eq_mul]
    exact hdiv _ (hcoeff g)
  have hkerF_nil : ∀ x ∈ RingHom.ker F, IsNilpotent x := by
    intro x hx
    obtain ⟨y, hy⟩ := hkerF_smul x (RingHom.mem_ker.mp hx)
    refine ⟨e, ?_⟩
    rw [hy, smul_pow]
    have h0 : (p : ZMod (p ^ e)) ^ e = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [h0, zero_smul]
  -- the simple module downstairs is a quotient of the regular module,
  -- with a Maschke complement of the kernel
  haveI := hsimple
  haveI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra (ZMod p) G) _
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : ρ.asModule)
  set θ := LinearMap.toSpanSingleton (MonoidAlgebra (ZMod p) G) ρ.asModule v₀ with hθdef
  have hθ_surj : Function.Surjective θ :=
    IsSimpleModule.toSpanSingleton_surjective (MonoidAlgebra (ZMod p) G) hv₀
  haveI : NeZero ((Nat.card G : ZMod p)) :=
    ⟨fun h0 => hG ((ZMod.natCast_eq_zero_iff _ _).mp h0)⟩
  obtain ⟨C, hC⟩ := MonoidAlgebra.Submodule.exists_isCompl (LinearMap.ker θ)
  set π := C.projection (LinearMap.ker θ) hC.symm with hπdef
  set ebar := π 1 with hebar
  have hπ_mul : ∀ x, π x = x * ebar := by
    intro x
    have h1 : π (x • (1 : MonoidAlgebra (ZMod p) G)) = x • π 1 := map_smul π x 1
    rw [smul_eq_mul, mul_one] at h1
    rw [h1, smul_eq_mul]
  have hebar_mem : ebar ∈ C := Submodule.projection_apply_mem hC.symm 1
  have hebar_idem : IsIdempotentElem ebar := by
    have h1 : π ebar = ebar := Submodule.projection_apply_of_mem_left hC.symm hebar_mem
    have h2 : ebar * ebar = ebar := by rw [← hπ_mul ebar]; exact h1
    exact h2
  have hθ_mul_ebar : ∀ x, θ (x * ebar) = θ x := by
    intro x
    have h2 : π (π x) = π x :=
      Submodule.projection_apply_of_mem_left hC.symm
        (Submodule.projection_apply_mem hC.symm x)
    have h3 : π (x - π x) = 0 := by rw [map_sub, h2, sub_self]
    have hmemK : x - π x ∈ LinearMap.ker θ :=
      (Submodule.projection_apply_eq_zero_iff hC.symm).mp h3
    have h4 : θ (x - π x) = 0 := LinearMap.mem_ker.mp hmemK
    rw [map_sub, sub_eq_zero] at h4
    rw [← hπ_mul x]
    exact h4.symm
  -- lift the idempotent along the nilpotent kernel
  obtain ⟨ε, hε_idem, hFε⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent F hkerF_nil
    ebar (RingHom.mem_range.mpr (hF_surj ebar)) hebar_idem
  -- the lifted summand
  set W : Submodule (MonoidAlgebra (ZMod (p ^ e)) G) (MonoidAlgebra (ZMod (p ^ e)) G) :=
    LinearMap.range (LinearMap.toSpanSingleton (MonoidAlgebra (ZMod (p ^ e)) G)
      (MonoidAlgebra (ZMod (p ^ e)) G) ε) with hWdef
  have hW_mem : ∀ w, w ∈ W ↔ w * ε = w := by
    intro w
    constructor
    · rintro ⟨x, rfl⟩
      rw [LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_assoc, hε_idem.eq]
    · intro hw
      exact ⟨w, by rw [LinearMap.toSpanSingleton_apply, smul_eq_mul, hw]⟩
  -- finiteness and freeness of the summand
  haveI hSfin : Finite (G →₀ ZMod (p ^ e)) :=
    Finite.of_equiv (G → ZMod (p ^ e)) Finsupp.equivFunOnFinite.symm
  haveI : Finite (MonoidAlgebra (ZMod (p ^ e)) G) := hSfin
  set iW : ↥W →ₗ[ZMod (p ^ e)] MonoidAlgebra (ZMod (p ^ e)) G :=
    LinearMap.restrictScalars (ZMod (p ^ e)) W.subtype with hiWdef
  set sW : MonoidAlgebra (ZMod (p ^ e)) G →ₗ[ZMod (p ^ e)] ↥W :=
    { toFun := fun x => ⟨x * ε, (hW_mem _).mpr (by rw [mul_assoc, hε_idem.eq])⟩
      map_add' := fun x y => Subtype.ext (by simp [add_mul])
      map_smul' := fun c x => Subtype.ext (by simp) } with hsWdef
  haveI : Module.Projective (ZMod (p ^ e)) ↥W :=
    Module.Projective.of_split iW sW
      (LinearMap.ext fun w => Subtype.ext ((hW_mem _).mp w.2))
  haveI : Module.Free (ZMod (p ^ e)) ↥W := by
    haveI := hloc
    exact Module.free_of_flat_of_isLocalRing
  -- the equivariant reduction `φ : W → V` with kernel `p • W`
  set φ₀ : ↥W → V := fun w =>
    ρ.asModuleEquiv (θ (F (w : MonoidAlgebra (ZMod (p ^ e)) G))) with hφ₀def
  have hφ₀_add : ∀ x y : ↥W, φ₀ (x + y) = φ₀ x + φ₀ y := by
    intro x y
    rw [hφ₀def]
    simp only [Submodule.coe_add, map_add]
  set φ : ↥W →+ V := AddMonoidHom.mk' φ₀ hφ₀_add with hφdef
  have hφ_apply : ∀ w : ↥W,
      φ w = ρ.asModuleEquiv (θ (F (w : MonoidAlgebra (ZMod (p ^ e)) G))) := fun _ => rfl
  -- single-smul computes through `θ` and `asModuleEquiv`
  have hsingle_smul : ∀ (g : G) (c : ZMod p) (y : MonoidAlgebra (ZMod p) G),
      ρ.asModuleEquiv (θ (MonoidAlgebra.single g c * y))
        = c • ρ g (ρ.asModuleEquiv (θ y)) := by
    intro g c y
    rw [← smul_eq_mul, map_smul, ρ.asModuleEquiv_map_smul, ρ.asAlgebraHom_single,
      LinearMap.smul_apply]
  -- scalar compatibility
  have hφ_smul : ∀ (c : ZMod (p ^ e)) (w : ↥W), φ (c • w) = red c • φ w := by
    intro c w
    have hcoe2 : ((c • w : ↥W) : MonoidAlgebra (ZMod (p ^ e)) G)
        = MonoidAlgebra.single (1 : G) c * (w : MonoidAlgebra (ZMod (p ^ e)) G) := by
      have h0 : ((c • w : ↥W) : MonoidAlgebra (ZMod (p ^ e)) G) = c • (w : _) := rfl
      rw [h0, Algebra.smul_def]
      congr 1
    rw [hφ_apply, hφ_apply, hcoe2, map_mul]
    have hFsingle : F (MonoidAlgebra.single (1 : G) c)
        = MonoidAlgebra.single (1 : G) (red c) := MonoidAlgebra.mapRingHom_single red 1 c
    rw [hFsingle, hsingle_smul, map_one, Module.End.one_apply]
  -- equivariance
  have hφ_equiv : ∀ (g : G) (w : ↥W),
      φ (MonoidAlgebra.submoduleRepr W g w) = ρ g (φ w) := by
    intro g w
    rw [hφ_apply, hφ_apply, MonoidAlgebra.coe_submoduleRepr_apply, map_mul]
    have hFsingle : F (MonoidAlgebra.single g (1 : ZMod (p ^ e)))
        = MonoidAlgebra.single g (1 : ZMod p) := by
      rw [MonoidAlgebra.mapRingHom_single, map_one]
    rw [hFsingle, hsingle_smul]
    rw [one_smul]
  -- surjectivity
  have hφ_surj : Function.Surjective φ := by
    intro v
    obtain ⟨x, hx⟩ := hθ_surj (ρ.asModuleEquiv.symm v)
    obtain ⟨y, hy⟩ := hF_surj x
    refine ⟨sW y, ?_⟩
    have h1 : ((sW y : ↥W) : MonoidAlgebra (ZMod (p ^ e)) G) = y * ε := rfl
    rw [hφ_apply, h1, map_mul, hFε, hθ_mul_ebar, hy, hx, LinearEquiv.apply_symm_apply]
  -- kernel is `p • W`
  have hred_p : red ((p : ℕ) : ZMod (p ^ e)) = 0 := by
    rw [map_natCast red, ZMod.natCast_self]
  have hφ_ker : ∀ w : ↥W, φ w = 0 ↔
      ∃ u : ↥W, w = (p : ZMod (p ^ e)) • u := by
    intro w
    constructor
    · intro hw
      have hFw_ker : F (w : MonoidAlgebra (ZMod (p ^ e)) G) ∈ LinearMap.ker θ := by
        rw [LinearMap.mem_ker]
        have h1 : ρ.asModuleEquiv (θ (F (w : MonoidAlgebra (ZMod (p ^ e)) G))) = 0 := hw
        have h2 : ρ.asModuleEquiv (θ (F (w : MonoidAlgebra (ZMod (p ^ e)) G)))
            = ρ.asModuleEquiv 0 := by rw [h1, map_zero]
        exact ρ.asModuleEquiv.injective h2
      have hFw_C : F (w : MonoidAlgebra (ZMod (p ^ e)) G) ∈ C := by
        have h1 : (w : MonoidAlgebra (ZMod (p ^ e)) G) * ε = w := (hW_mem _).mp w.2
        have h2 : F (w : MonoidAlgebra (ZMod (p ^ e)) G)
            = F (w : MonoidAlgebra (ZMod (p ^ e)) G) * ebar := by
          rw [← hFε, ← map_mul, h1]
        rw [h2, ← hπ_mul]
        exact Submodule.projection_apply_mem hC.symm _
      have hFw0 : F (w : MonoidAlgebra (ZMod (p ^ e)) G) = 0 :=
        (Submodule.disjoint_def.mp hC.disjoint) _ hFw_ker hFw_C
      obtain ⟨y, hy⟩ := hkerF_smul _ hFw0
      refine ⟨sW y, Subtype.ext ?_⟩
      have hcoe : ((((p : ZMod (p ^ e)) • sW y) : ↥W) : MonoidAlgebra (ZMod (p ^ e)) G)
          = (p : ZMod (p ^ e)) • (y * ε) := rfl
      rw [hcoe, ← smul_mul_assoc, ← hy]
      exact ((hW_mem _).mp w.2).symm
    · rintro ⟨u, rfl⟩
      rw [hφ_smul]
      rw [show red ((p : ℕ) : ZMod (p ^ e)) = 0 from hred_p, zero_smul]
  -- conclude, subgroup by subgroup
  refine ⟨W, inferInstance, fun A => ?_⟩
  have hA : ¬ p ∣ Nat.card ↥A := fun hdvd =>
    hG (hdvd.trans (Subgroup.card_subgroup_dvd_card A))
  exact card_invariants_eq_pow_finrank_of_lift hp he hA
    ((MonoidAlgebra.submoduleRepr W).comp A.subtype) (ρ.comp A.subtype)
    φ hφ_surj (fun c w => hφ_smul c w) (fun a w => hφ_equiv (↑a) w)
    (fun w => hφ_ker w)

end Representation

end Lift

/-!
### The elementary abelian case, as a weighted dimension-sum identity

The Coq proof of `solvable_Wielandt_fixpoint`, after reducing to `V` minimal
normal elementary abelian `p`, proves
`∑ i, rC i * m i * #|A i| = ∑ i, rC i * n i * #|A i|` (with
`rC i = logn p #|'C_V(A i)|`) by checking it mod `p ^ e` for every `e`: both
sides are the trace of one operator `∑ i, k i • ∑ (a ∈ A i), rW a` on the lifted
module `W`, computed via `gamma i` there.  This section is that argument.
-/

section ModuleCase

open Finset in
/-- **The Wielandt weighted dimension-sum identity** (the elementary abelian core
of Coq `solvable_Wielandt_fixpoint`): for a simple `(ZMod p)[G]`-module `V` with
`p ∤ |G|`, subgroups `A i ≤ G` and weights `m n : ι → ℕ` with
`∑ (i | a ∈ A i), m i = ∑ (i | a ∈ A i), n i` for every `a : G`,

`∑ i, m i * |A i| * dim C_V(A i) = ∑ i, n i * |A i| * dim C_V(A i)`. -/
theorem Representation.wielandt_trace_sum_eq {p : ℕ} (hp : p.Prime)
    {G : Type*} [Group G] [Finite G] (hG : ¬ p ∣ Nat.card G)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) G V)
    (hsimple : IsSimpleModule (MonoidAlgebra (ZMod p) G) ρ.asModule)
    {ι : Type*} [Fintype ι] (A : ι → Subgroup G) (m n : ι → ℕ)
    [∀ (a : G) (i : ι), Decidable (a ∈ A i)]
    (hbal : ∀ a : G, ∑ i with a ∈ A i, m i = ∑ i with a ∈ A i, n i) :
    ∑ i, m i * Nat.card (A i) * Module.finrank (ZMod p)
        (Representation.invariants (ρ.comp (A i).subtype))
      = ∑ i, n i * Nat.card (A i) * Module.finrank (ZMod p)
        (Representation.invariants (ρ.comp (A i).subtype)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set d : ι → ℕ := fun i =>
    Module.finrank (ZMod p) (Representation.invariants (ρ.comp (A i).subtype)) with hd
  -- it suffices to prove the identity mod `p ^ e` for every `e ≠ 0`
  suffices h : ∀ e : ℕ, e ≠ 0 →
      ((∑ i, m i * Nat.card (A i) * d i : ℕ) : ZMod (p ^ e))
        = ((∑ i, n i * Nat.card (A i) * d i : ℕ) : ZMod (p ^ e)) by
    set X := ∑ i, m i * Nat.card (A i) * d i with hX
    set Y := ∑ i, n i * Nat.card (A i) * d i with hY
    have he : X + Y + 1 ≠ 0 := by omega
    haveI : NeZero (p ^ (X + Y + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hXlt : X < p ^ (X + Y + 1) :=
      lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
        (Nat.pow_le_pow_right hp.pos (by omega))
    have hYlt : Y < p ^ (X + Y + 1) :=
      lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
        (Nat.pow_le_pow_right hp.pos (by omega))
    have h1 := congrArg ZMod.val (h (X + Y + 1) he)
    rwa [ZMod.val_cast_of_lt hXlt, ZMod.val_cast_of_lt hYlt] at h1
  intro e he
  obtain ⟨W, hWfree, hWcard⟩ := ρ.exists_wielandt_lift hp he hG hsimple
  haveI := hWfree
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have hloc : IsLocalRing (ZMod (p ^ e)) := ZMod.isLocalRing_prime_pow hp he
  haveI : Fintype G := Fintype.ofFinite G
  haveI hSfin : Finite (G →₀ ZMod (p ^ e)) :=
    Finite.of_equiv (G → ZMod (p ^ e)) Finsupp.equivFunOnFinite.symm
  haveI : Finite (MonoidAlgebra (ZMod (p ^ e)) G) := hSfin
  set ρW := MonoidAlgebra.submoduleRepr W with hρWdef
  -- the two dimension families agree (comparing the two `p`-power counts)
  have hrank : ∀ i, p ^ d i = p ^ Module.finrank (ZMod (p ^ e))
      (Representation.invariants (ρW.comp (A i).subtype)) := by
    intro i
    have h2 : Nat.card (Representation.invariants (ρ.comp (A i).subtype))
        = p ^ d i := by
      have h3 := Module.natCard_eq_pow_finrank (K := ZMod p)
        (V := ↥(Representation.invariants (ρ.comp (A i).subtype)))
      rwa [Nat.card_zmod] at h3
    rw [← hWcard (A i)]
    exact h2.symm
  have hd_eq : ∀ i, d i = Module.finrank (ZMod (p ^ e))
      (Representation.invariants (ρW.comp (A i).subtype)) :=
    fun i => Nat.pow_right_injective hp.two_le (hrank i)
  -- trace of the `A i`-sum, by the averaging trace formula
  have htrace : ∀ i, LinearMap.trace (ZMod (p ^ e)) ↥W
      (∑ g ∈ Finset.univ.filter (· ∈ A i), ρW g)
      = (Nat.card (A i) : ZMod (p ^ e)) * (d i : ZMod (p ^ e)) := by
    intro i
    haveI : Fintype ↥(A i) := Fintype.ofFinite _
    have hA : ¬ p ∣ Nat.card ↥(A i) := fun hdvd =>
      hG (hdvd.trans (Subgroup.card_subgroup_dvd_card _))
    have hcop : (Nat.card ↥(A i)).Coprime (p ^ e) :=
      Nat.Coprime.pow_right e ((hp.coprime_iff_not_dvd.mpr hA).symm)
    haveI : Invertible ((Fintype.card ↥(A i) : ZMod (p ^ e))) :=
      (ZMod.unitOfCoprime _ hcop).invertible.copy _
        (by rw [ZMod.coe_unitOfCoprime, Nat.card_eq_fintype_card])
    have h1 := Representation.trace_sum_eq_card_mul_finrank_invariants
      (ρW.comp (A i).subtype) hloc
    have h2 : ∑ g ∈ Finset.univ.filter (· ∈ A i), ρW g
        = ∑ a : ↥(A i), (ρW.comp (A i).subtype) a := by
      refine Finset.sum_subtype _ (fun g => ?_) (fun g => ρW g)
      simp
    rw [h2, h1, Nat.card_eq_fintype_card, hd_eq i]
  -- both weighted sums are traces of one operator
  have hcast : ∀ k : ι → ℕ,
      ((∑ i, k i * Nat.card (A i) * d i : ℕ) : ZMod (p ^ e))
        = LinearMap.trace (ZMod (p ^ e)) ↥W
            (∑ i, k i • ∑ g ∈ Finset.univ.filter (· ∈ A i), ρW g) := by
    intro k
    rw [map_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, htrace i, nsmul_eq_mul]
    push_cast
    ring
  -- the exchange: reorder the double sum and apply the balance hypothesis
  have hswap : ∀ k : ι → ℕ,
      (∑ i, k i • ∑ g ∈ Finset.univ.filter (· ∈ A i), ρW g)
        = ∑ g : G, (∑ i with g ∈ A i, k i) • ρW g := by
    intro k
    calc ∑ i, k i • ∑ g ∈ Finset.univ.filter (· ∈ A i), ρW g
        = ∑ i, ∑ g ∈ Finset.univ.filter (· ∈ A i), k i • ρW g := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.smul_sum]
      _ = ∑ i, ∑ g : G, if g ∈ A i then k i • ρW g else 0 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_filter]
      _ = ∑ g : G, ∑ i, if g ∈ A i then k i • ρW g else 0 := Finset.sum_comm
      _ = ∑ g : G, (∑ i with g ∈ A i, k i) • ρW g := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.sum_filter, Finset.sum_smul]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hgi : g ∈ A i
          · simp [hgi]
          · simp [hgi]
  have hΘ : (∑ i, m i • ∑ g ∈ Finset.univ.filter (· ∈ A i), ρW g)
      = ∑ i, n i • ∑ g ∈ Finset.univ.filter (· ∈ A i), ρW g := by
    rw [hswap m, hswap n]
    exact Finset.sum_congr rfl fun g _ => by rw [hbal g]
  rw [hcast m, hcast n, hΘ]

end ModuleCase

/-!
### The order formula: group-level reduction

The strong induction of the Coq proof: quotient by a `G`-invariant normal
subgroup `B` of `V` splits every fixed-point order (the `factorCA_B` step of
`solvable_Wielandt_fixpoint`, via `coprime_quotient_cent` — here
`Subgroup.coprime_fixedPoints_quotient_eq`); when no such `B` exists, `V` is
elementary abelian and irreducible under `G`, and the module-level identity
applies.
-/

section GroupCase

/-- Restricting the actor to a subgroup preserves invariance of subgroups. -/
instance Subgroup.SMulInvariant.of_subgroup_actor {G V : Type*} [Group G] [Group V]
    [MulDistribMulAction G V] (H : Subgroup V) [H.SMulInvariant G] (A : Subgroup G) :
    H.SMulInvariant ↥A :=
  ⟨fun a _v hv => Subgroup.SMulInvariant.smul_mem (a : G) hv⟩

open MulAction in
/-- **Fixed-point orders factor through coprime quotients** (the `factorCA_B` step
in the Coq proof of `solvable_Wielandt_fixpoint`):
`#|C_V(A)| = #|C_B(A)| * #|C_{V/B}(A)|` for an `A`-invariant normal subgroup
`B ≤ V` with `|A|` coprime to `|B|`, `B` solvable. -/
private theorem card_fixedPoints_eq_card_mul_card {A V : Type*} [Group A] [Finite A]
    [Group V] [Finite V] [MulDistribMulAction A V] (B : Subgroup V) [B.Normal]
    [B.SMulInvariant A] [IsSolvable ↥B]
    (hco : (Nat.card A).Coprime (Nat.card ↥B)) :
    Nat.card (FixedPoints.subgroup A V)
      = Nat.card (FixedPoints.subgroup A ↥B)
          * Nat.card (FixedPoints.subgroup A (V ⧸ B)) := by
  classical
  set f₀ : (FixedPoints.subgroup A V) →* V ⧸ B :=
    (QuotientGroup.mk' B).comp (FixedPoints.subgroup A V).subtype with hf₀def
  -- the range of `f₀` is the fixed subgroup of the quotient (coprime lifting)
  have hrange : f₀.range = FixedPoints.subgroup A (V ⧸ B) := by
    rw [← coprime_fixedPoints_quotient_eq (A := A) (N := B) hco]
    ext x
    constructor
    · rintro ⟨⟨v, hv⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  -- the kernel of `f₀` is (equivalent to) the fixed subgroup of `B`
  have hmem1 : ∀ x : ↥(FixedPoints.subgroup A V), x ∈ f₀.ker ↔ ((x : V) ∈ B) := by
    intro x
    rw [MonoidHom.mem_ker]
    change (((x : V) : V ⧸ B) = 1) ↔ _
    exact QuotientGroup.eq_one_iff _
  have hker : Nat.card f₀.ker = Nat.card (FixedPoints.subgroup A ↥B) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨((x : ↥(FixedPoints.subgroup A V)) : V), (hmem1 _).mp x.2⟩,
          fun a => Subtype.ext (by
            rw [Subgroup.coe_smul]
            exact (x : ↥(FixedPoints.subgroup A V)).2 a)⟩
        invFun := fun b => ⟨⟨((b : ↥B) : V), fun a => by
            have h1 : ((a • (b : ↥B) : ↥B) : V) = (((b : ↥B) : ↥B) : V) :=
              congrArg _ (b.2 a)
            rwa [Subgroup.coe_smul] at h1⟩,
          (hmem1 _).mpr (b : ↥B).2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun b => Subtype.ext (Subtype.ext rfl) }
  -- Lagrange plus the first isomorphism theorem
  have h1 : Nat.card (FixedPoints.subgroup A V)
      = Nat.card ((FixedPoints.subgroup A V) ⧸ f₀.ker) * Nat.card f₀.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup f₀.ker
  have h2 : Nat.card ((FixedPoints.subgroup A V) ⧸ f₀.ker) = Nat.card f₀.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f₀).toEquiv
  rw [h1, h2, hrange, hker, mul_comm]

variable {p : ℕ} {V : Type*} [Group V]

/-- The subgroup ↔ submodule dictionary preserves cardinality. -/
private theorem card_toSubmodule (h : IsElementaryAbelian p V) (K : Subgroup V) :
    Nat.card ↥(h.toSubmodule K) = Nat.card ↥K :=
  Nat.card_congr
    ⟨fun x => ⟨(x : h.Vec).toMul, (h.mem_toSubmodule).mp x.2⟩,
      fun k => ⟨h.toVec (k : V), by
        rw [h.mem_toSubmodule, IsElementaryAbelian.Vec.toMul_toVec]; exact k.2⟩,
      fun x => Subtype.ext (IsElementaryAbelian.Vec.toVec_toMul _),
      fun k => Subtype.ext (IsElementaryAbelian.Vec.toMul_toVec _)⟩

open MulAction in
/-- The fixed-point subgroup corresponds to the invariant submodule under the
abelem dictionary. -/
private theorem toSubmodule_fixedPoints_eq (h : IsElementaryAbelian p V)
    {G : Type*} [Group G] [MulDistribMulAction G V] (A : Subgroup G) :
    h.toSubmodule (FixedPoints.subgroup ↥A V)
      = Representation.invariants ((h.repr G).comp A.subtype) := by
  ext x
  rw [IsElementaryAbelian.mem_toSubmodule, Representation.mem_invariants]
  constructor
  · intro hx a
    have h0 : ((h.repr G).comp A.subtype) a x = h.repr G (a : G) x := rfl
    rw [h0]
    refine IsElementaryAbelian.Vec.toMul_injective ?_
    rw [IsElementaryAbelian.toMul_repr_apply]
    exact hx a
  · intro hx a
    have h1 : h.repr G (a : G) x = x := hx a
    have h2 := congrArg IsElementaryAbelian.Vec.toMul h1
    rw [IsElementaryAbelian.toMul_repr_apply] at h2
    exact h2

end GroupCase

section Main

open MulAction

private theorem solvable_wielandt_fixpoint_aux {G : Type*} [Group G] [Finite G]
    {ι : Type*} [Fintype ι] (A : ι → Subgroup G) (m n : ι → ℕ)
    [∀ (a : G) (i : ι), Decidable (a ∈ A i)]
    (hbal : ∀ a : G, ∑ i with a ∈ A i, m i = ∑ i with a ∈ A i, n i) :
    ∀ c : ℕ, ∀ (V : Type v) [Group V] [Finite V] [MulDistribMulAction G V],
      Nat.card V ≤ c → (Nat.card V).Coprime (Nat.card G) → IsSolvable V →
      ∏ i, Nat.card (FixedPoints.subgroup ↥(A i) V) ^ (m i * Nat.card (A i))
        = ∏ i, Nat.card (FixedPoints.subgroup ↥(A i) V) ^ (n i * Nat.card (A i)) := by
  intro c
  induction c with
  | zero =>
    intro V _ _ _ hle _ _
    have h0 := Nat.card_pos (α := V)
    omega
  | succ c IH =>
    intro V _ _ _ hle hco hsol
    by_cases hB : ∃ B : Subgroup V, B.Normal ∧ B.SMulInvariant G ∧ B ≠ ⊥ ∧ B ≠ ⊤
    · -- a proper nontrivial invariant normal subgroup: factor and recurse
      obtain ⟨B, hBn, hBi, hBbot, hBtop⟩ := hB
      haveI := hBn
      haveI := hBi
      have hcardB_lt : Nat.card ↥B < Nat.card V := by
        refine lt_of_le_of_ne
          (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card B)) ?_
        exact fun hEq => hBtop (Subgroup.eq_top_of_card_eq B hEq)
      have hcardQ_lt : Nat.card (V ⧸ B) < Nat.card V := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup B]
        have h1 : 1 < Nat.card ↥B := (Subgroup.one_lt_card_iff_ne_bot B).mpr hBbot
        exact lt_mul_of_one_lt_right Nat.card_pos h1
      have hcoB : (Nat.card ↥B).Coprime (Nat.card G) :=
        Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card B) hco
      have hcoQ : (Nat.card (V ⧸ B)).Coprime (Nat.card G) :=
        Nat.Coprime.coprime_dvd_left (Subgroup.card_quotient_dvd_card B) hco
      have hrecB := IH ↥B (Nat.le_of_lt_succ (lt_of_lt_of_le hcardB_lt hle)) hcoB
        inferInstance
      have hrecQ := IH (V ⧸ B) (Nat.le_of_lt_succ (lt_of_lt_of_le hcardQ_lt hle)) hcoQ
        inferInstance
      have hfact : ∀ i, Nat.card (FixedPoints.subgroup ↥(A i) V)
          = Nat.card (FixedPoints.subgroup ↥(A i) ↥B)
              * Nat.card (FixedPoints.subgroup ↥(A i) (V ⧸ B)) := by
        intro i
        refine card_fixedPoints_eq_card_mul_card B ?_
        refine Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card (A i)) ?_
        exact (Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card B) hco).symm
      calc ∏ i, Nat.card (FixedPoints.subgroup ↥(A i) V) ^ (m i * Nat.card (A i))
          = (∏ i, Nat.card (FixedPoints.subgroup ↥(A i) ↥B) ^ (m i * Nat.card (A i)))
              * ∏ i, Nat.card (FixedPoints.subgroup ↥(A i) (V ⧸ B))
                  ^ (m i * Nat.card (A i)) := by
            rw [← Finset.prod_mul_distrib]
            exact Finset.prod_congr rfl fun i _ => by rw [hfact i, mul_pow]
        _ = (∏ i, Nat.card (FixedPoints.subgroup ↥(A i) ↥B) ^ (n i * Nat.card (A i)))
              * ∏ i, Nat.card (FixedPoints.subgroup ↥(A i) (V ⧸ B))
                  ^ (n i * Nat.card (A i)) := by rw [hrecB, hrecQ]
        _ = ∏ i, Nat.card (FixedPoints.subgroup ↥(A i) V) ^ (n i * Nat.card (A i)) := by
            rw [← Finset.prod_mul_distrib]
            exact (Finset.prod_congr rfl fun i _ => by rw [hfact i, mul_pow]).symm
    · rcases eq_or_ne (Nat.card V) 1 with hV1 | hVne
      · -- `V` trivial: all factors are `1`
        haveI hsub : Subsingleton V := (Nat.card_eq_one_iff_unique.mp hV1).1
        have hone : ∀ i, Nat.card (FixedPoints.subgroup ↥(A i) V) = 1 := fun i =>
          Nat.card_of_subsingleton 1
        have h1 : ∀ k : ι → ℕ,
            ∏ i, Nat.card (FixedPoints.subgroup ↥(A i) V) ^ (k i * Nat.card (A i)) = 1 := by
          intro k
          refine Finset.prod_eq_one fun i _ => ?_
          rw [hone i, one_pow]
        rw [h1 m, h1 n]
      · -- no invariant normal subgroup: `V` is elementary abelian and irreducible
        have hBtop : ∀ B : Subgroup V, B.Normal → B.SMulInvariant G → B ≠ ⊥ → B = ⊤ := by
          intro B h1 h2 h3
          by_contra h4
          exact hB ⟨B, h1, h2, h3, h4⟩
        haveI hVnontriv : Nontrivial V :=
          Finite.one_lt_card_iff_nontrivial.mp (lt_of_le_of_ne Nat.card_pos (Ne.symm hVne))
        have hcommbot : commutator V = ⊥ := by
          by_contra hne
          have h1 : commutator V = ⊤ :=
            hBtop (commutator V) inferInstance inferInstance hne
          exact absurd h1 (IsSolvable.commutator_lt_top_of_nontrivial V).ne
        open scoped commutatorElement in
        have hmulcomm : ∀ a b : V, a * b = b * a := by
          intro a b
          have h1 : ⁅a, b⁆ ∈ (⁅(⊤ : Subgroup V), (⊤ : Subgroup V)⁆ : Subgroup V) :=
            Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
          have h2 : (⁅(⊤ : Subgroup V), (⊤ : Subgroup V)⁆ : Subgroup V) = commutator V := rfl
          rw [h2, hcommbot, Subgroup.mem_bot,
            commutatorElement_eq_one_iff_mul_comm] at h1
          exact h1
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hVne
        haveI : Fact p.Prime := ⟨hp⟩
        set Ω : Subgroup V :=
          { carrier := {v | v ^ p = 1}
            one_mem' := one_pow p
            mul_mem' := fun {a b} ha hb => by
              rw [Set.mem_setOf_eq] at ha hb ⊢
              rw [Commute.mul_pow (hmulcomm a b), ha, hb, one_mul]
            inv_mem' := fun {a} ha => by
              rw [Set.mem_setOf_eq] at ha ⊢
              rw [inv_pow, ha, inv_one] } with hΩdef
        have hΩmem : ∀ v : V, v ∈ Ω ↔ v ^ p = 1 := fun v => Iff.rfl
        have hΩn : Ω.Normal := by
          refine ⟨fun x hx g => ?_⟩
          rw [hΩmem] at hx ⊢
          rw [conj_pow, hx, mul_one, mul_inv_cancel]
        have hΩi : Ω.SMulInvariant G := by
          refine ⟨fun a v hv => ?_⟩
          rw [hΩmem] at hv ⊢
          rw [← smul_pow', hv, smul_one]
        have hΩbot : Ω ≠ ⊥ := by
          obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpdvd
          intro h0
          have hxΩ : x ∈ Ω := by rw [hΩmem, ← hx]; exact pow_orderOf_eq_one x
          rw [h0, Subgroup.mem_bot] at hxΩ
          rw [hxΩ, orderOf_one] at hx
          exact hp.ne_one hx.symm
        have hEl : IsElementaryAbelian p V :=
          ⟨hmulcomm, fun v => (hΩmem v).mp ((hBtop Ω hΩn hΩi hΩbot).symm ▸ Subgroup.mem_top v)⟩
        have hpG : ¬ p ∣ Nat.card G := by
          intro hdvd
          have h1 : p ∣ Nat.gcd (Nat.card V) (Nat.card G) := Nat.dvd_gcd hpdvd hdvd
          rw [Nat.Coprime] at hco
          rw [hco] at h1
          exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
        have hirr : (hEl.repr G).IsIrreducible := by
          rw [hEl.isIrreducible_repr_iff G]
          refine ⟨hVnontriv, fun K hKinv hKbot => ?_⟩
          have hKn : K.Normal := ⟨fun x hx g => by
            rw [hmulcomm g x, mul_assoc, mul_inv_cancel, mul_one]; exact hx⟩
          exact hBtop K hKn hKinv hKbot
        have hsimplemod :
            IsSimpleModule (MonoidAlgebra (ZMod p) G) (hEl.repr G).asModule :=
          (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr
        haveI : Finite hEl.Vec := Finite.of_equiv V hEl.toVec
        have hsum := Representation.wielandt_trace_sum_eq hp hpG (hEl.repr G)
          hsimplemod A m n hbal
        have hcard : ∀ i, Nat.card (FixedPoints.subgroup ↥(A i) V)
            = p ^ Module.finrank (ZMod p)
                (Representation.invariants ((hEl.repr G).comp (A i).subtype)) := by
          intro i
          rw [← card_toSubmodule hEl (FixedPoints.subgroup ↥(A i) V),
            toSubmodule_fixedPoints_eq hEl (A i)]
          have h3 := Module.natCard_eq_pow_finrank (K := ZMod p)
            (V := ↥(Representation.invariants ((hEl.repr G).comp (A i).subtype)))
          rwa [Nat.card_zmod] at h3
        calc ∏ i, Nat.card (FixedPoints.subgroup ↥(A i) V) ^ (m i * Nat.card (A i))
            = p ^ ∑ i, m i * Nat.card (A i) * Module.finrank (ZMod p)
                (Representation.invariants ((hEl.repr G).comp (A i).subtype)) := by
              rw [← Finset.prod_pow_eq_pow_sum]
              refine Finset.prod_congr rfl fun i _ => ?_
              rw [hcard i, ← pow_mul]
              congr 1
              ring
          _ = p ^ ∑ i, n i * Nat.card (A i) * Module.finrank (ZMod p)
                (Representation.invariants ((hEl.repr G).comp (A i).subtype)) := by
              rw [hsum]
          _ = ∏ i, Nat.card (FixedPoints.subgroup ↥(A i) V) ^ (n i * Nat.card (A i)) := by
              rw [← Finset.prod_pow_eq_pow_sum]
              refine (Finset.prod_congr rfl fun i _ => ?_).symm
              rw [hcard i, ← pow_mul]
              congr 1
              ring

open MulAction in
/-- **The solvable Wielandt fixpoint order formula** (Coq
`solvable_Wielandt_fixpoint`), external-action form: let `G` act coprimely on a
finite solvable group `V` (the project's `MulDistribMulAction` convention), let
`A : ι → Subgroup G` be a finite family with weights `m n : ι → ℕ` such that
`∑ (i | a ∈ A i), m i = ∑ (i | a ∈ A i), n i` for every `a : G`.  Then

`∏ i, #|C_V(A i)| ^ (m i * #|A i|) = ∏ i, #|C_V(A i)| ^ (n i * #|A i|)`,

where `C_V(A i)` is the fixed-point subgroup `FixedPoints.subgroup ↥(A i) V`.

See `Subgroup.solvable_wielandt_fixpoint_internal` for the internal (subgroups of
a common ambient group) form, which mirrors the Coq statement. -/
theorem solvable_wielandt_fixpoint {G : Type*} [Group G] [Finite G]
    {V : Type*} [Group V] [Finite V] [MulDistribMulAction G V]
    {ι : Type*} [Fintype ι] (A : ι → Subgroup G) (m n : ι → ℕ)
    [∀ (a : G) (i : ι), Decidable (a ∈ A i)]
    (hco : (Nat.card V).Coprime (Nat.card G)) (hsol : IsSolvable V)
    (hbal : ∀ a : G, ∑ i with a ∈ A i, m i = ∑ i with a ∈ A i, n i) :
    ∏ i, Nat.card (FixedPoints.subgroup ↥(A i) V) ^ (m i * Nat.card (A i))
      = ∏ i, Nat.card (FixedPoints.subgroup ↥(A i) V) ^ (n i * Nat.card (A i)) :=
  solvable_wielandt_fixpoint_aux A m n hbal (Nat.card V) V le_rfl hco hsol

end Main

/-!
### The internal form

The statement-faithful port of Coq `solvable_Wielandt_fixpoint`: everything lives
in one ambient group `gT`, the action is conjugation of `G ≤ 'N(V)` on `V`
(Task 1's `normalizerMulDistribMulAction` convention), and the fixed points are
the centralizer intersections `'C_V(A i) = centralizer (A i) ⊓ V`.
-/

section Internal

open MulAction

variable {gT : Type*} [Group gT] {G V : Subgroup gT}

/-- Fixed points of the conjugation action of `(A.subgroupOf G)` on `V` are the
elements of `V` centralizing `A` (for `A ≤ G ≤ 'N(V)`). -/
private theorem mem_fixedPoints_subgroupOf_iff
    (hnorm : G ≤ Subgroup.normalizer (V : Set gT)) {A : Subgroup gT} (hA : A ≤ G)
    (v : ↥V) :
    letI := Subgroup.normalizerMulDistribMulAction hnorm
    (v ∈ FixedPoints.subgroup ↥(A.subgroupOf G) ↥V
      ↔ (v : gT) ∈ Subgroup.centralizer (A : Set gT)) := by
  letI := Subgroup.normalizerMulDistribMulAction hnorm
  rw [FixedPoints.mem_subgroup, Subgroup.mem_centralizer_iff]
  have hsmul : ∀ (a : ↥(A.subgroupOf G)),
      ((a • v : ↥V) : gT) = ((a : ↥G) : gT) * (v : gT) * ((a : ↥G) : gT)⁻¹ :=
    fun a => Subgroup.conjAction_smul_coe hnorm (a : ↥G) v
  constructor
  · intro hfix x hx
    have h1 := congrArg Subtype.val (hfix ⟨⟨x, hA hx⟩, Subgroup.mem_subgroupOf.mpr hx⟩)
    rw [hsmul] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  · intro hcent a
    refine Subtype.ext ?_
    rw [hsmul]
    exact mul_inv_eq_iff_eq_mul.mpr
      (hcent ((a : ↥G) : gT) (Subgroup.mem_subgroupOf.mp a.2))

/-- Cardinality form of `mem_fixedPoints_subgroupOf_iff`:
`#|C_V(A)| = #|'C(A) ⊓ V|`. -/
private theorem card_fixedPoints_subgroupOf
    (hnorm : G ≤ Subgroup.normalizer (V : Set gT)) {A : Subgroup gT} (hA : A ≤ G) :
    letI := Subgroup.normalizerMulDistribMulAction hnorm
    Nat.card (FixedPoints.subgroup ↥(A.subgroupOf G) ↥V)
      = Nat.card ↥(Subgroup.centralizer (A : Set gT) ⊓ V) := by
  letI := Subgroup.normalizerMulDistribMulAction hnorm
  refine Nat.card_congr
    { toFun := fun v => ⟨((v : ↥V) : gT), Subgroup.mem_inf.mpr
        ⟨(mem_fixedPoints_subgroupOf_iff hnorm hA _).mp v.2, (v : ↥V).2⟩⟩
      invFun := fun w => ⟨⟨(w : gT), (Subgroup.mem_inf.mp w.2).2⟩,
        (mem_fixedPoints_subgroupOf_iff hnorm hA _).mpr (Subgroup.mem_inf.mp w.2).1⟩
      left_inv := fun v => Subtype.ext (Subtype.ext rfl)
      right_inv := fun w => Subtype.ext rfl }

open MulAction in
/-- **The solvable Wielandt fixpoint order formula, internal form** (Coq
`solvable_Wielandt_fixpoint`, statement-faithful): let `V, G ≤ gT` with
`G ≤ 'N(V)`, `#|V|` coprime to `#|G|` and `V` solvable; let `A : ι → Subgroup gT`
be a finite family with `A i ≤ G` whenever `0 < m i + n i`, and suppose
`∑ (i | a ∈ A i), m i = ∑ (i | a ∈ A i), n i` for every `a ∈ G`.  Then

`∏ i, #|'C_V(A i)| ^ (m i * #|A i|) = ∏ i, #|'C_V(A i)| ^ (n i * #|A i|)`.

Consumers: BGsection3's `Frobenius_Wielandt_fixpoint` (Peterfalvi (9.1)) and
PFsection9. -/
theorem Subgroup.solvable_wielandt_fixpoint_internal {gT : Type*} [Group gT]
    [Finite gT] {ι : Type*} [Fintype ι] (A : ι → Subgroup gT) (m n : ι → ℕ)
    [∀ (a : gT) (i : ι), Decidable (a ∈ A i)] {G V : Subgroup gT}
    (hA : ∀ i, 0 < m i + n i → A i ≤ G)
    (hnorm : G ≤ Subgroup.normalizer (V : Set gT))
    (hco : (Nat.card V).Coprime (Nat.card G)) (hsol : IsSolvable ↥V)
    (hbal : ∀ a ∈ G, ∑ i with a ∈ A i, m i = ∑ i with a ∈ A i, n i) :
    ∏ i, Nat.card ↥(Subgroup.centralizer (A i : Set gT) ⊓ V) ^ (m i * Nat.card (A i))
      = ∏ i, Nat.card ↥(Subgroup.centralizer (A i : Set gT) ⊓ V)
          ^ (n i * Nat.card (A i)) := by
  letI := Subgroup.normalizerMulDistribMulAction hnorm
  letI : ∀ (a : ↥G) (i : ι), Decidable (a ∈ (A i).subgroupOf G) :=
    fun a i => decidable_of_iff ((a : gT) ∈ A i) Subgroup.mem_subgroupOf.symm
  have hbal' : ∀ a : ↥G, ∑ i with a ∈ (A i).subgroupOf G, m i
      = ∑ i with a ∈ (A i).subgroupOf G, n i := by
    intro a
    have hfilter : ∀ (k : ι → ℕ), (∑ i with a ∈ (A i).subgroupOf G, k i)
        = ∑ i with (a : gT) ∈ A i, k i := fun k =>
      Finset.sum_congr (Finset.filter_congr fun i _ => by
        simp [Subgroup.mem_subgroupOf]) fun _ _ => rfl
    rw [hfilter m, hfilter n]
    exact hbal (a : gT) a.2
  have hmain := solvable_wielandt_fixpoint (G := ↥G) (V := ↥V)
    (fun i => (A i).subgroupOf G) m n hco hsol hbal'
  have hfactor : ∀ (k : ι → ℕ), (∀ i, k i ≠ 0 → A i ≤ G) →
      ∏ i, Nat.card ↥(Subgroup.centralizer (A i : Set gT) ⊓ V)
          ^ (k i * Nat.card (A i))
        = ∏ i, Nat.card (FixedPoints.subgroup ↥((A i).subgroupOf G) ↥V)
            ^ (k i * Nat.card ((A i).subgroupOf G)) := by
    intro k hk
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases eq_or_ne (k i) 0 with h0 | h0
    · rw [h0, zero_mul, zero_mul, pow_zero, pow_zero]
    · have hAG := hk i h0
      rw [card_fixedPoints_subgroupOf hnorm hAG,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv]
  rw [hfactor m fun i hi => hA i (by omega), hfactor n fun i hi => hA i (by omega)]
  exact hmain

/-- Smoke test: the exact instantiation shape used by BGsection3's
`Frobenius_Wielandt_fixpoint` (Peterfalvi (9.1)).  There the index type is the
finType of *all* subgroups of `gT` with `A := id`, the weight `m` is `#|K|` at
`⊥` and `1` at `G` (Coq: `[fun A => 0%N with 1%G |-> #|K|, G |-> 1%N]`), and `n`
is the indicator of `K |: orbit 'JG K R` (the `K`-conjugates of `R` together
with `K`); the balance hypothesis is the Frobenius partition.  The example
checks that `Subgroup.solvable_wielandt_fixpoint_internal` accepts this family
and weight shape; deriving the balance from `IsFrobenius` is BGsection3 (M4)
material. -/
example {gT : Type*} [Group gT] [Finite gT] (G K R M : Subgroup gT)
    (hnorm : G ≤ Subgroup.normalizer (M : Set gT))
    (hco : (Nat.card M).Coprime (Nat.card G)) (hsol : IsSolvable ↥M) : True := by
  classical
  haveI : Finite (Subgroup gT) :=
    Finite.of_injective (fun H : Subgroup gT => (H : Set gT)) SetLike.coe_injective
  letI : Fintype (Subgroup gT) := Fintype.ofFinite _
  -- the BGsection3 weight functions
  set m : Subgroup gT → ℕ :=
    fun B => if B = ⊥ then Nat.card K else if B = G then 1 else 0 with hm
  set n : Subgroup gT → ℕ :=
    fun B => if B = K ∨ ∃ x ∈ K, B = R.map (MulAut.conj x).toMonoidHom then 1 else 0
    with hn
  have smoke : (∀ B : Subgroup gT, 0 < m B + n B → B ≤ G) →
      (∀ a ∈ G, ∑ B with a ∈ B, m B = ∑ B with a ∈ B, n B) →
      ∏ B : Subgroup gT,
          Nat.card ↥(Subgroup.centralizer (B : Set gT) ⊓ M) ^ (m B * Nat.card B)
        = ∏ B : Subgroup gT,
            Nat.card ↥(Subgroup.centralizer (B : Set gT) ⊓ M) ^ (n B * Nat.card B) :=
    fun hA hbal =>
      Subgroup.solvable_wielandt_fixpoint_internal (fun B => B) m n hA hnorm hco hsol hbal
  trivial

end Internal
