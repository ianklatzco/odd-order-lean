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

end Lift
