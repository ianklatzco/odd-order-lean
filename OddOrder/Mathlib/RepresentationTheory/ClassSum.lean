/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import OddOrder.Mathlib.RepresentationTheory.ClassFunction
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.StdBasis

/-!
# Class sums, the center basis, and structure constants

This file is Task 3 of the M2 character-theory plan: it makes the class-sum elements of the
group algebra `MonoidAlgebra ℂ G` explicit, identifies them with a basis of the center, and
computes the structure constants of the center in this basis — the integrality workhorse
consumed by the central-character argument (Task 4). Corresponds to the `gring` (group-ring)
structure-constant material of MathComp's `mxrepresentation.v`/`character.v`; exact Coq lemma
names are noted where used, with "exact name unconfirmed" flagged where the Coq checkout was
not available to verify against.

**Deviation from the plan.** The M2 plan files this material inside `CharacterArith.lean`
(Tasks 1, 3, 4); it is split into this standalone file instead, per the parallel-work
isolation protocol (a sibling task implements `Induced.lean` concurrently) and the plan's
own "split further if any exceeds ~1200 lines" clause.

## Main definitions

* `MonoidAlgebra.classSum (c : ConjClasses G) : MonoidAlgebra ℂ G`: the class sum
  `∑ x ∈ c.carrier, single x 1`, built via an indicator function (mirroring
  `ClassFunction.lean`'s private `centralOfClassFunction`). MathComp: `gring` class-sum basis
  vectors (exact name unconfirmed).
* `MonoidAlgebra.classSumBasis`, a `Basis (ConjClasses G) ℂ` of the center (as a subtype of
  `MonoidAlgebra ℂ G`): the class sums form a basis, transported from the indicator basis of
  `ClassFunction G` along `MonoidAlgebra.centerEquivClassFunction`.
* `MonoidAlgebra.classMulCoeff (c d e : ConjClasses G) : ℕ`: the structure constant counting
  solutions `x * y = z` with `x ∈ c.carrier`, `y ∈ d.carrier`, for a representative
  `z = e.out`; well-defined independent of the representative by `classMulCoeff_eq`.

## Main results

* `MonoidAlgebra.classSum_mem_center`: class sums are central.
* `MonoidAlgebra.classSumBasis_coe`: `classSumBasis c` is literally `classSum c` (as an
  element of the group algebra).
* `MonoidAlgebra.classMulCoeff_eq`: representative-independence of `classMulCoeff`, via the
  conjugation bijection between solution sets for any two representatives of the same class.
* `MonoidAlgebra.classSum_mul`: the **structure-constant formula**
  `classSum c * classSum d = ∑ e, (classMulCoeff c d e : ℕ) • classSum e`. MathComp: `gring`
  structure constants (exact name unconfirmed).
* `MonoidAlgebra.classSum_mk_one`: sanity check, `classSum (ConjClasses.mk 1) = 1`.

## Design notes

* **Route for `classSum_mul`.** Computed coefficientwise via `Finsupp.ext`, using
  `MonoidAlgebra.mul_apply_antidiagonal` (the convolution formula restricted to a Finset of
  solution pairs) rather than expanding `classSum` as a sum of `single`s — this keeps every
  step a plain `Finset.sum` manipulation over `G × G`, never a `Finsupp.sum`.
* **Representative-independence.** For representatives `z, e.out` of the same class `e`,
  conjugation by a witness `k` (with `k * e.out * k⁻¹ = z`) gives a bijection
  `(x, y) ↦ (k*x*k⁻¹, k*y*k⁻¹)` between the two solution sets: it preserves the carriers of
  `c` and `d` (`ConjClasses.conj_mem_carrier_iff`) and transports the defining equation via
  injectivity of conjugation.
-/

noncomputable section

open Finset Module
open scoped ClassFunction

universe u

variable {G : Type u} [Group G]

/-! ### Conjugation and carriers -/

/-- Conjugating an element by `k` does not change which conjugacy class it belongs to: this
is the invariance fact behind centrality of class sums and the well-definedness of the
structure constants. -/
theorem ConjClasses.conj_mem_carrier_iff (c : ConjClasses G) (k g : G) :
    k * g * k⁻¹ ∈ c.carrier ↔ g ∈ c.carrier := by
  have hmk : ConjClasses.mk (k * g * k⁻¹) = ConjClasses.mk g :=
    ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨k, rfl⟩).symm
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mem_carrier_iff_mk_eq, hmk]

/-! ### The class sum -/

section ClassSum

variable [Fintype G]

variable (G) in
open scoped Classical in
/-- The **class sum** of a conjugacy class `c`: the group-algebra element
`∑ x ∈ c.carrier, single x 1`, built via an indicator function (as in `ClassFunction.lean`'s
`centralOfClassFunction`) to keep coefficient-level lemmas `rfl`-adjacent. MathComp: `gring`
class-sum basis vectors (exact name unconfirmed). -/
def MonoidAlgebra.classSum (c : ConjClasses G) : MonoidAlgebra ℂ G :=
  Finsupp.equivFunOnFinite.symm fun g => if g ∈ c.carrier then (1 : ℂ) else 0

open scoped Classical in
@[simp]
theorem MonoidAlgebra.classSum_apply (c : ConjClasses G) (g : G) :
    MonoidAlgebra.classSum G c g = if g ∈ c.carrier then (1 : ℂ) else 0 :=
  rfl

open scoped Classical in
/-- The single-sum characterization of the class sum: `∑ x ∈ c.carrier, single x 1`, phrased
as a sum over the Finset `{x | x ∈ c.carrier}` of `G`. -/
theorem MonoidAlgebra.classSum_eq_sum_single (c : ConjClasses G) :
    MonoidAlgebra.classSum G c
      = ∑ x ∈ Finset.univ.filter (· ∈ c.carrier), MonoidAlgebra.single x (1 : ℂ) := by
  rw [← Finsupp.univ_sum_single (MonoidAlgebra.classSum G c), Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [MonoidAlgebra.classSum_apply]
  by_cases h : g ∈ c.carrier
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    change (MonoidAlgebra.single g (0 : ℂ) : MonoidAlgebra ℂ G) = 0
    exact MonoidAlgebra.single_zero g

/-- Class sums are central: their coefficient function is constant on conjugacy classes,
since `c.carrier` is a union of conjugacy classes (namely, it *is* one). -/
theorem MonoidAlgebra.classSum_mem_center (c : ConjClasses G) :
    MonoidAlgebra.classSum G c ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
  rw [MonoidAlgebra.mem_center_iff]
  intro g h
  simp only [MonoidAlgebra.classSum_apply]
  rw [ConjClasses.conj_mem_carrier_iff]

open scoped Classical in
/-- Sanity check: the class sum of the trivial conjugacy class is the identity of the group
algebra — the conjugacy class of `1` is the singleton `{1}`, since conjugates of `1` are
always `1`. -/
theorem MonoidAlgebra.classSum_mk_one : MonoidAlgebra.classSum G (ConjClasses.mk (1 : G)) = 1 := by
  have hcarrier : ∀ x : G, x ∈ (ConjClasses.mk (1 : G)).carrier ↔ x = 1 := by
    intro x
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    constructor
    · rintro ⟨k, hk⟩
      have : x = k⁻¹ * (k * x * k⁻¹) * k := by group
      rw [this, hk]; group
    · rintro rfl
      exact ⟨1, by group⟩
  ext x
  rw [MonoidAlgebra.classSum_apply, hcarrier, MonoidAlgebra.one_def]
  simp [Finsupp.single_apply, eq_comm]

end ClassSum

/-! ### The class sums as a basis of the center -/

section ClassSumBasis

variable [Fintype G]

variable (G) in
/-- The indicator basis of `ClassFunction G`, transported from the standard basis of
`ConjClasses G → ℂ` along `ClassFunction.equivFunConjClasses`. -/
def MonoidAlgebra.classFunctionIndicatorBasis : Basis (ConjClasses G) ℂ (ClassFunction G) :=
  (Pi.basisFun ℂ (ConjClasses G)).map ClassFunction.equivFunConjClasses.symm

open scoped Classical in
theorem MonoidAlgebra.classFunctionIndicatorBasis_apply (c : ConjClasses G) (g : G) :
    MonoidAlgebra.classFunctionIndicatorBasis G c g = if g ∈ c.carrier then (1 : ℂ) else 0 := by
  change (ClassFunction.equivFunConjClasses.symm
    (Pi.basisFun ℂ (ConjClasses G) c)) g = _
  rw [Pi.basisFun_apply]
  change (Pi.single c (1 : ℂ) : ConjClasses G → ℂ) (ConjClasses.mk g) = _
  simp [Pi.single_apply, ConjClasses.mem_carrier_iff_mk_eq]

variable (G) in
/-- The class sums form a basis of the center of the group algebra, transported from
`classFunctionIndicatorBasis` along `MonoidAlgebra.centerEquivClassFunction`. MathComp:
`gring` basis of the group-ring center (exact name unconfirmed). -/
def MonoidAlgebra.classSumBasis :
    Basis (ConjClasses G) ℂ ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G)) :=
  (MonoidAlgebra.classFunctionIndicatorBasis G).map
    (MonoidAlgebra.centerEquivClassFunction G).symm

@[simp]
theorem MonoidAlgebra.classSumBasis_coe (c : ConjClasses G) :
    (MonoidAlgebra.classSumBasis G c : MonoidAlgebra ℂ G) = MonoidAlgebra.classSum G c := by
  have hb : MonoidAlgebra.classSumBasis G c
      = (MonoidAlgebra.centerEquivClassFunction G).symm
          (MonoidAlgebra.classFunctionIndicatorBasis G c) :=
    Basis.map_apply _ _ _
  rw [hb]
  ext g
  change (Finsupp.equivFunOnFinite.symm
    (MonoidAlgebra.classFunctionIndicatorBasis G c : ClassFunction G)) g = _
  rw [Finsupp.coe_equivFunOnFinite_symm, MonoidAlgebra.classFunctionIndicatorBasis_apply,
    MonoidAlgebra.classSum_apply]

end ClassSumBasis

/-! ### Structure constants -/

section StructureConstants

/-- Conjugation by a fixed `k`, acting on both coordinates of `G × G`: the bijection used to
transport solution sets `{(x, y) : x * y = z}` between different representatives `z` of the
same conjugacy class. -/
private def conjProdEquiv (k : G) : G × G ≃ G × G :=
  (MulAut.conj k).toEquiv.prodCongr (MulAut.conj k).toEquiv

private theorem conjProdEquiv_apply (k : G) (p : G × G) :
    conjProdEquiv k p = (k * p.1 * k⁻¹, k * p.2 * k⁻¹) := by
  simp [conjProdEquiv, Equiv.prodCongr_apply, Prod.map, MulAut.conj_apply]

variable (G) in
/-- The **structure constant**: the number of ways to write a fixed representative `e.out`
of the class `e` as `x * y` with `x ∈ c.carrier`, `y ∈ d.carrier`. Independent of the choice
of representative, by `classMulCoeff_eq`. MathComp: `gring` structure constants (exact name
unconfirmed). -/
def MonoidAlgebra.classMulCoeff (c d e : ConjClasses G) : ℕ :=
  Nat.card {p : G × G // p.1 ∈ c.carrier ∧ p.2 ∈ d.carrier ∧ p.1 * p.2 = e.out}

/-- **Well-definedness of `classMulCoeff`**: the solution count for `z` agrees with the one
computed via the canonical representative `e.out`, for any `z ∈ e.carrier`. Proved by
conjugating a solution set for `e.out` into one for `z` along a witness of `IsConj e.out z`. -/
theorem MonoidAlgebra.classMulCoeff_eq {c d e : ConjClasses G} {z : G} (hz : z ∈ e.carrier) :
    MonoidAlgebra.classMulCoeff G c d e =
      Nat.card {p : G × G // p.1 ∈ c.carrier ∧ p.2 ∈ d.carrier ∧ p.1 * p.2 = z} := by
  have hout : e.out ∈ e.carrier := ConjClasses.mem_carrier_iff_mk_eq.mpr e.out_eq
  have hconj : IsConj e.out z :=
    ConjClasses.mk_eq_mk_iff_isConj.mp
      ((ConjClasses.mem_carrier_iff_mk_eq.mp hout).trans
        (ConjClasses.mem_carrier_iff_mk_eq.mp hz).symm)
  obtain ⟨k, hk⟩ := isConj_iff.mp hconj
  refine Nat.card_congr (Equiv.subtypeEquiv (conjProdEquiv k) fun a => ?_)
  rw [conjProdEquiv_apply]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(ConjClasses.conj_mem_carrier_iff c k a.1).mpr h1,
      (ConjClasses.conj_mem_carrier_iff d k a.2).mpr h2, ?_⟩
    change k * a.1 * k⁻¹ * (k * a.2 * k⁻¹) = z
    rw [show k * a.1 * k⁻¹ * (k * a.2 * k⁻¹) = k * (a.1 * a.2) * k⁻¹ by group, h3, hk]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(ConjClasses.conj_mem_carrier_iff c k a.1).mp h1,
      (ConjClasses.conj_mem_carrier_iff d k a.2).mp h2, ?_⟩
    have h3' : k * (a.1 * a.2) * k⁻¹ = z := by
      rw [show k * (a.1 * a.2) * k⁻¹ = k * a.1 * k⁻¹ * (k * a.2 * k⁻¹) by group]
      exact h3
    rw [← hk, ← MulAut.conj_apply, ← MulAut.conj_apply] at h3'
    exact (MulAut.conj k).injective h3'

open scoped Classical in
variable [Fintype G] in
/-- **Structure-constant formula for the product of two class sums.** MathComp: `gring`
structure constants (exact name unconfirmed). -/
theorem MonoidAlgebra.classSum_mul (c d : ConjClasses G) :
    MonoidAlgebra.classSum G c * MonoidAlgebra.classSum G d
      = ∑ e : ConjClasses G, MonoidAlgebra.classMulCoeff G c d e • MonoidAlgebra.classSum G e := by
  classical
  ext z
  set s : Finset (G × G) := Finset.univ.filter (fun p : G × G => p.1 * p.2 = z) with hs
  have hmem : ∀ {p : G × G}, p ∈ s ↔ p.1 * p.2 = z := by
    intro p; simp [hs]
  rw [MonoidAlgebra.mul_apply_antidiagonal (MonoidAlgebra.classSum G c)
    (MonoidAlgebra.classSum G d) z s hmem]
  have hterm : ∀ p : G × G, MonoidAlgebra.classSum G c p.1 * MonoidAlgebra.classSum G d p.2
      = if p.1 ∈ c.carrier ∧ p.2 ∈ d.carrier then (1 : ℂ) else 0 := by
    intro p
    rw [MonoidAlgebra.classSum_apply, MonoidAlgebra.classSum_apply]
    by_cases h1 : p.1 ∈ c.carrier <;> by_cases h2 : p.2 ∈ d.carrier <;> simp [h1, h2]
  rw [Finset.sum_congr rfl fun p _ => hterm p, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  -- the LHS is now the cardinality of the solution set for `z`
  have hfilter_eq : s.filter (fun p : G × G => p.1 ∈ c.carrier ∧ p.2 ∈ d.carrier)
      = Finset.univ.filter
          (fun p : G × G => p.1 ∈ c.carrier ∧ p.2 ∈ d.carrier ∧ p.1 * p.2 = z) := by
    rw [hs, Finset.filter_filter]
    congr 1
    ext p
    tauto
  have hcardL : ((s.filter (fun p : G × G => p.1 ∈ c.carrier ∧ p.2 ∈ d.carrier)).card : ℂ)
      = (Nat.card {p : G × G // p.1 ∈ c.carrier ∧ p.2 ∈ d.carrier ∧ p.1 * p.2 = z} : ℂ) := by
    rw [hfilter_eq, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcardL]
  -- the RHS: only the class of `z` contributes to the sum over `e`
  have hRHS : (∑ e : ConjClasses G,
      MonoidAlgebra.classMulCoeff G c d e • MonoidAlgebra.classSum G e) z
      = (MonoidAlgebra.classMulCoeff G c d (ConjClasses.mk z) : ℂ) := by
    have hterm2 : ∀ e : ConjClasses G,
        (MonoidAlgebra.classMulCoeff G c d e • MonoidAlgebra.classSum G e) z
          = if e = ConjClasses.mk z then (MonoidAlgebra.classMulCoeff G c d e : ℂ) else 0 := by
      intro e
      rw [MonoidAlgebra.smul_apply, MonoidAlgebra.classSum_apply, nsmul_eq_mul]
      by_cases h : z ∈ e.carrier
      · rw [if_pos h, mul_one, if_pos (ConjClasses.mem_carrier_iff_mk_eq.mp h).symm]
      · rw [if_neg h, mul_zero,
          if_neg fun heq : e = ConjClasses.mk z => h (heq ▸ ConjClasses.mem_carrier_mk)]
    have hsum_apply : (∑ e : ConjClasses G,
        MonoidAlgebra.classMulCoeff G c d e • MonoidAlgebra.classSum G e) z
        = ∑ e : ConjClasses G,
            (MonoidAlgebra.classMulCoeff G c d e • MonoidAlgebra.classSum G e) z :=
      map_sum (Finsupp.applyAddHom z)
        (fun e => MonoidAlgebra.classMulCoeff G c d e • MonoidAlgebra.classSum G e) Finset.univ
    rw [hsum_apply, Finset.sum_congr rfl fun e _ => hterm2 e,
      Finset.sum_ite_eq' Finset.univ (ConjClasses.mk z)
        fun e => (MonoidAlgebra.classMulCoeff G c d e : ℂ)]
    simp
  rw [hRHS,
    MonoidAlgebra.classMulCoeff_eq (c := c) (d := d) (e := ConjClasses.mk z)
      ConjClasses.mem_carrier_mk]

end StructureConstants
