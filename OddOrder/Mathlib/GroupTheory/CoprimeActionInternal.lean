/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import OddOrder.Mathlib.GroupTheory.CoprimeAction

/-!
# Internal coprime actions: the conjugation dictionary

The coprime-action suite of `OddOrder.Mathlib.GroupTheory.CoprimeAction` is stated
*externally*: an abstract group `A` acts on a group via `[MulDistribMulAction A G]`.
The Bender–Glauberman sections (MathComp's `BGsection1`–`16`) consume the *internal*
form: `H A : Subgroup G` with `A ≤ normalizer (H : Set G)` (MathComp `A \subset 'N(H)`),
where the action is conjugation, the fixed points are `'C_H(A)` and the action
commutator is `[~: H, A]`.  This file is the dictionary between the two languages,
plus the internal restatements of the suite.  Everything here is transport: no new
group theory is proved.

## Shape decisions (binding for downstream BG files)

* **The conjugation action** is `Subgroup.normalizerMulDistribMulAction hA :
  MulDistribMulAction A H` (from `CoprimeAction.lean`), for
  `hA : A ≤ normalizer (H : Set G)`.  It is data depending on `hA`, hence never an
  instance; statements that mention it bind it with `letI`, and the internal
  corollaries below are phrased so that their statements do not mention the action
  at all.
* **Fixed points**: `FixedPoints.subgroup A H = (centralizer (A : Set G) ⊓ H).subgroupOf H`
  (`fixedPoints_conjAction_eq`), i.e. MathComp's `'C_H(A)` is spelled
  `centralizer (A : Set G) ⊓ H : Subgroup G`.  Membership and `map H.subtype` forms
  are provided.
* **Action commutator**: `actionCommutator A (⊤ : Subgroup H) = ⁅H, A⁆.subgroupOf H`
  (`actionCommutator_conjAction_eq`), the commutator computed in `G`; note
  `⁅H, A⁆ ≤ H` automatically (`commutator_le_of_le_normalizer`).
* **Internal invariance**: the canonical spelling of "`P` is `A`-invariant" is
  `A ≤ normalizer (P : Set G)` (MathComp `A \subset 'N(P)`).  Bridges:
  `subgroupOf_smulInvariant_iff` (to the external `SMulInvariant` class of
  `P.subgroupOf H` under the conjugation action) and
  `le_normalizer_iff_forall_map_conj_eq` (to the
  `∀ a ∈ A, P.map (MulAut.conj a).toMonoidHom = P` spelling).

## Main results (internal forms of the coprime suite)

With `hA : A ≤ normalizer (H : Set G)` and `(Nat.card A).Coprime (Nat.card H)`
(coprimality on `Nat.card N` for the quotient statement):

* `coprime_cent_prod_internal` : `⁅H, A⁆ ⊔ (centralizer ↑A ⊓ H) = H` for solvable
  `H`, and `coprime_cent_prod_set_internal` for the setwise-product form
  `↑⁅H, A⁆ * ↑(centralizer ↑A ⊓ H) = ↑H`.  MathComp: `coprime_cent_prod`
  (`[~: G, A] * 'C_G(A) = G`), B&G 1.6(a).
* `coprime_commutator_eq_internal` : `⁅⁅H, A⁆, A⁆ = ⁅H, A⁆` for solvable `H`.
  MathComp: `coprime_commGid`, B&G 1.6(b).
* `coprime_fixedPoints_quotient_surjective_internal` /
  `coprime_fixedPoints_quotient_eq_internal` : for `N ≤ H` with `H ≤ 'N(N)`,
  `A ≤ 'N(N)`, `N` solvable and `|N|` coprime to `|A|`, every `A`-fixed point of
  `H ⧸ N` lifts to an element of `centralizer ↑A ⊓ H`; equivalently
  `'C_H(A)` surjects onto `'C_{H/N}(A)`.  MathComp: `coprime_quotient_cent`
  (`'C_G(A) / H = 'C_(G / H)(A / H)`), B&G 1.5(d).
* `coprime_hall_exists_internal` / `coprime_hall_trans_internal` : `A`-invariant
  Hall π-subgroups of a solvable `H` exist, and are conjugate under an element of
  `centralizer ↑A ⊓ H`.  A Hall π-subgroup *of `H`* is spelled `P ≤ H` with
  `(P.subgroupOf H).IsHall π`.  MathComp: `coprime_Hall_exists`,
  `coprime_Hall_trans`, B&G 1.5(a), 1.5(c).

The smoke-test `example`s at the end of the file elaborate the exact statement
shapes used at MathComp usage sites (BGsection1's `coprime_cent_prod` rewrites,
BGsection13's `coprime_Hall_exists`/`_trans` destructuring) and are kept as
documentation.
-/

open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G] {H A : Subgroup G}

/-!
### The conjugation-action dictionary
-/

/-- Under the conjugation action of `A ≤ 'N(H)` on `H`, the action of `a` on `h` is
conjugation in the ambient group. -/
@[simp]
theorem conjAction_smul_coe (hA : A ≤ normalizer (H : Set G)) (a : A) (h : H) :
    letI := normalizerMulDistribMulAction hA
    ((a • h : H) : G) = (a : G) * h * (a : G)⁻¹ :=
  rfl

/-- If `A` normalizes `H` then `⁅H, A⁆ ≤ H` (the commutator computed in the ambient
group).  This is Mathlib's `Subgroup.le_normalizer_iff_commutator_le_left`, restated
in the shape used throughout this file. -/
theorem commutator_le_of_le_normalizer (hA : A ≤ normalizer (H : Set G)) : ⁅H, A⁆ ≤ H :=
  le_normalizer_iff_commutator_le_left.mp hA

/-- Pulling a subgroup of `H` back and forth along `H.subtype` is the identity. -/
theorem map_subtype_subgroupOf (K : Subgroup H) : (K.map H.subtype).subgroupOf H = K := by
  rw [← comap_subtype]
  exact comap_map_eq_self_of_injective H.subtype_injective K

/-!
#### Invariance bridges

The canonical internal spelling of "`P` is `A`-invariant" is
`A ≤ normalizer (P : Set G)`.  The lemmas below translate it to the external
`Subgroup.SMulInvariant` class (for the conjugation action on an overgroup `H` of
`P`) and to the conjugation-map spelling.
-/

/-- A subgroup normalized by `A` is `SMulInvariant` for the conjugation action, viewed
inside any acted-on overgroup `H`.  (No `P ≤ H` is needed: `P.subgroupOf H` only sees
`P ⊓ H`.) -/
theorem smulInvariant_subgroupOf_of_le_normalizer (hA : A ≤ normalizer (H : Set G))
    {P : Subgroup G} (hAP : A ≤ normalizer (P : Set G)) :
    letI := normalizerMulDistribMulAction hA
    (P.subgroupOf H).SMulInvariant A := by
  letI := normalizerMulDistribMulAction hA
  refine ⟨fun a g hg => ?_⟩
  rw [mem_subgroupOf] at hg ⊢
  rw [conjAction_smul_coe hA]
  exact (mem_set_normalizer_iff.mp (hAP a.2) (g : G)).mp hg

/-- Converse of `smulInvariant_subgroupOf_of_le_normalizer` for `P ≤ H`:
external invariance of `P.subgroupOf H` under the conjugation action means `A`
normalizes `P`. -/
theorem le_normalizer_of_subgroupOf_smulInvariant (hA : A ≤ normalizer (H : Set G))
    {P : Subgroup G} (hPH : P ≤ H)
    (hinv : letI := normalizerMulDistribMulAction hA; (P.subgroupOf H).SMulInvariant A) :
    A ≤ normalizer (P : Set G) := by
  letI := normalizerMulDistribMulAction hA
  rw [le_set_normalizer_iff]
  intro a ha p hp
  have h1 : (⟨p, hPH hp⟩ : H) ∈ P.subgroupOf H := by rwa [mem_subgroupOf]
  have h2 := hinv.smul_mem (⟨a, ha⟩ : A) h1
  rwa [mem_subgroupOf, conjAction_smul_coe hA] at h2

/-- The invariance bridge, iff form: for `P ≤ H`, external `SMulInvariant` of
`P.subgroupOf H` under the conjugation action is the internal `A ≤ 'N(P)`.
MathComp: the `[acts A, on H | 'JG]`/`A \subset 'N(H)` interchange. -/
theorem subgroupOf_smulInvariant_iff (hA : A ≤ normalizer (H : Set G)) {P : Subgroup G}
    (hPH : P ≤ H) :
    letI := normalizerMulDistribMulAction hA
    ((P.subgroupOf H).SMulInvariant A ↔ A ≤ normalizer (P : Set G)) :=
  ⟨fun h => le_normalizer_of_subgroupOf_smulInvariant hA hPH h,
    fun h => smulInvariant_subgroupOf_of_le_normalizer hA h⟩

/-- The internal invariance spelling `A ≤ 'N(P)` in terms of the standing
conjugation-map convention `P.map (MulAut.conj a).toMonoidHom = P`. -/
theorem le_normalizer_iff_forall_map_conj_eq {P : Subgroup G} :
    A ≤ normalizer (P : Set G) ↔ ∀ a ∈ A, P.map (MulAut.conj a).toMonoidHom = P := by
  simp only [SetLike.le_def, mem_normalizer_iff_map_conj_eq, MulEquiv.toMonoidHom_eq_coe]

/-!
#### Fixed points of the conjugation action
-/

/-- Membership in the fixed points of the conjugation action is centralizing `A`.
MathComp: `x \in 'C_H(A)` (given `x \in H`). -/
theorem mem_fixedPoints_conjAction_iff (hA : A ≤ normalizer (H : Set G)) {h : H} :
    letI := normalizerMulDistribMulAction hA
    (h ∈ FixedPoints.subgroup A H ↔ (h : G) ∈ centralizer (A : Set G)) := by
  letI := normalizerMulDistribMulAction hA
  rw [FixedPoints.mem_subgroup, mem_centralizer_iff]
  constructor
  · intro hfix x hx
    have key := congrArg Subtype.val (hfix ⟨x, hx⟩)
    rw [conjAction_smul_coe hA] at key
    exact mul_inv_eq_iff_eq_mul.mp key
  · intro hcomm a
    refine Subtype.ext ?_
    rw [conjAction_smul_coe hA]
    exact mul_inv_eq_iff_eq_mul.mpr (hcomm (a : G) a.2)

/-- **Fixed points of the conjugation action** are the centralizer intersection:
`'C_H(A) = 'C(A) :&: H`, as subgroups of `H`.  MathComp: the definitional identity
`'C_H(A) = 'C(A) :&: H` together with `gacentJ`/`afixJ` (fixed points of the
conjugation action are the centralizer). -/
theorem fixedPoints_conjAction_eq (hA : A ≤ normalizer (H : Set G)) :
    letI := normalizerMulDistribMulAction hA
    FixedPoints.subgroup A H = (centralizer (A : Set G) ⊓ H).subgroupOf H := by
  letI := normalizerMulDistribMulAction hA
  ext h
  rw [mem_fixedPoints_conjAction_iff hA, mem_subgroupOf, mem_inf, and_iff_left h.2]

/-- `map H.subtype` form of `fixedPoints_conjAction_eq`: the fixed points, viewed in
the ambient group, are `centralizer ↑A ⊓ H`. -/
theorem fixedPoints_conjAction_map_subtype (hA : A ≤ normalizer (H : Set G)) :
    letI := normalizerMulDistribMulAction hA
    (FixedPoints.subgroup A H).map H.subtype = centralizer (A : Set G) ⊓ H := by
  letI := normalizerMulDistribMulAction hA
  rw [fixedPoints_conjAction_eq hA, map_subgroupOf_eq_of_le inf_le_right]

/-!
#### The action commutator of the conjugation action
-/

open scoped commutatorElement in
/-- **The action commutator of the conjugation action** is the subgroup commutator,
relative form: for `K ≤ H` (as a subgroup of `H`), the action commutator of `K`,
viewed in the ambient group, is `⁅K, A⁆` computed in `G`.  The generators match up
via `g⁻¹ * (a • g) = ⁅g⁻¹, a⁆`. -/
theorem actionCommutator_conjAction_map_subtype (hA : A ≤ normalizer (H : Set G))
    (K : Subgroup H) :
    letI := normalizerMulDistribMulAction hA
    (K.actionCommutator A).map H.subtype = ⁅K.map H.subtype, A⁆ := by
  letI := normalizerMulDistribMulAction hA
  refine le_antisymm ?_ ?_
  · rw [map_le_iff_le_comap, actionCommutator_le]
    intro a g hg
    rw [mem_comap]
    have key : H.subtype (g⁻¹ * a • g) = ⁅(g : G)⁻¹, (a : G)⁆ := by
      simp only [subtype_apply, coe_mul, coe_inv, conjAction_smul_coe hA,
        commutatorElement_def, inv_inv]
      group
    rw [key]
    exact commutator_mem_commutator (inv_mem (mem_map_of_mem H.subtype hg)) a.2
  · rw [commutator_le]
    rintro x ⟨g, hg, rfl⟩ y hy
    have key : ⁅H.subtype g, y⁆
        = H.subtype ((g⁻¹)⁻¹ * ((⟨y, hy⟩ : A) • g⁻¹)) := by
      simp only [subtype_apply, coe_mul, coe_inv, conjAction_smul_coe hA,
        commutatorElement_def, inv_inv]
      group
    rw [key]
    exact mem_map_of_mem H.subtype
      (inv_mul_smul_mem_actionCommutator (⟨y, hy⟩ : A) (K.inv_mem hg))

/-- **The full action commutator of the conjugation action** is `⁅H, A⁆` (computed in
`G`, where it lands inside `H` by `commutator_le_of_le_normalizer`), as a subgroup of
`H`.  MathComp: `[~: H, A]` and its internal-action reading. -/
theorem actionCommutator_conjAction_eq (hA : A ≤ normalizer (H : Set G)) :
    letI := normalizerMulDistribMulAction hA
    actionCommutator A (⊤ : Subgroup H) = ⁅H, A⁆.subgroupOf H := by
  letI := normalizerMulDistribMulAction hA
  refine map_injective H.subtype_injective ?_
  rw [actionCommutator_conjAction_map_subtype hA, ← MonoidHom.range_eq_map, range_subtype,
    map_subgroupOf_eq_of_le (commutator_le_of_le_normalizer hA)]

end Subgroup

/-!
### The coprime suite, internal forms

Each statement below is a thin transport of the corresponding external theorem in
`CoprimeAction.lean` along the dictionary above; the statements themselves do not
mention the action.
-/

open Subgroup

section CoprimeInternal

variable {G : Type*} [Group G] {H A : Subgroup G}

/-- **Commutator-centralizer product, internal form** (B&G 1.6(a)): if `A` normalizes
the finite solvable subgroup `H` and `|A|` is coprime to `|H|`, then
`H = ⁅H, A⁆ * C_H(A)`, stated as a join (see `coprime_cent_prod_set_internal` for the
setwise product).  MathComp: `coprime_cent_prod` (`[~: G, A] * 'C_G(A) = G`). -/
theorem coprime_cent_prod_internal [Finite G] [IsSolvable H]
    (hA : A ≤ normalizer (H : Set G)) (hco : (Nat.card A).Coprime (Nat.card H)) :
    ⁅H, A⁆ ⊔ centralizer (A : Set G) ⊓ H = H := by
  letI := normalizerMulDistribMulAction hA
  have h := congrArg (map H.subtype) (coprime_cent_prod (A := A) (G := H) hco)
  rwa [Subgroup.map_sup, actionCommutator_conjAction_map_subtype hA,
    fixedPoints_conjAction_map_subtype hA, ← MonoidHom.range_eq_map, range_subtype] at h

/-- Setwise-product form of `coprime_cent_prod_internal`, matching MathComp's
`[~: G, A] * 'C_G(A) = G` verbatim (the join is a product because `C_H(A)` normalizes
`⁅H, A⁆`). -/
theorem coprime_cent_prod_set_internal [Finite G] [IsSolvable H]
    (hA : A ≤ normalizer (H : Set G)) (hco : (Nat.card A).Coprime (Nat.card H)) :
    ((⁅H, A⁆ : Subgroup G) : Set G) * ((centralizer (A : Set G) ⊓ H : Subgroup G) : Set G)
      = (H : Set G) := by
  rw [← coe_mul_of_right_le_normalizer_left _ _
      (inf_le_right.trans (normalizer_commutator_ge_left H A)),
    coprime_cent_prod_internal hA hco]

/-- **Coprime actions are commutator-stable, internal form** (B&G 1.6(b)): if `A`
normalizes the finite solvable subgroup `H` coprimely, then `⁅⁅H, A⁆, A⁆ = ⁅H, A⁆`.
MathComp: `coprime_commGid` (`[~: G, A, A] = [~: G, A]`). -/
theorem coprime_commutator_eq_internal [Finite G] [IsSolvable H]
    (hA : A ≤ normalizer (H : Set G)) (hco : (Nat.card A).Coprime (Nat.card H)) :
    ⁅⁅H, A⁆, A⁆ = ⁅H, A⁆ := by
  letI := normalizerMulDistribMulAction hA
  have h := congrArg (map H.subtype) (coprime_commutator_eq (A := A) (G := H) hco)
  rwa [actionCommutator_conjAction_map_subtype hA, actionCommutator_conjAction_map_subtype hA,
    ← MonoidHom.range_eq_map, range_subtype] at h

/-- **Fixed points lift along coprime quotients, internal form** (B&G 1.5(d)): let
`N ≤ H` be subgroups with `H ≤ 'N(N)` and `A ≤ 'N(H)`, `A ≤ 'N(N)`, `N` finite
solvable of order coprime to `|A|`.  Then every `A`-fixed point of `H ⧸ N` (for the
induced conjugation action) lifts to an element of `H` centralizing `A`.
MathComp: `coprime_quotient_cent`, surjectivity direction of
`'C_G(A) / H = 'C_(G / H)(A / H)`. -/
theorem coprime_fixedPoints_quotient_surjective_internal [Finite A]
    (hA : A ≤ normalizer (H : Set G)) {N : Subgroup G} [Finite N] [IsSolvable N]
    (hNH : N ≤ H) (hHN : H ≤ normalizer (N : Set G)) (hAN : A ≤ normalizer (N : Set G))
    (hco : (Nat.card A).Coprime (Nat.card N)) :
    letI := normalizerMulDistribMulAction hA
    haveI : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
    haveI : (N.subgroupOf H).SMulInvariant A :=
      smulInvariant_subgroupOf_of_le_normalizer hA hAN
    ∀ x ∈ FixedPoints.subgroup A (H ⧸ N.subgroupOf H),
      ∃ h : H, (h : G) ∈ centralizer (A : Set G)
        ∧ (QuotientGroup.mk h : H ⧸ N.subgroupOf H) = x := by
  letI := normalizerMulDistribMulAction hA
  haveI : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  haveI : (N.subgroupOf H).SMulInvariant A := smulInvariant_subgroupOf_of_le_normalizer hA hAN
  haveI : Finite (N.subgroupOf H) := Finite.of_equiv _ (subgroupOfEquivOfLe hNH).symm.toEquiv
  haveI : IsSolvable (N.subgroupOf H) :=
    solvable_of_surjective (f := (subgroupOfEquivOfLe hNH).symm.toMonoidHom)
      (subgroupOfEquivOfLe hNH).symm.surjective
  intro x hx
  have hco' : (Nat.card A).Coprime (Nat.card (N.subgroupOf H)) := by
    rwa [card_subgroupOf hNH]
  obtain ⟨h, hfix, hmk⟩ := coprime_fixedPoints_quotient_surjective hco' hx
  exact ⟨h, (mem_fixedPoints_conjAction_iff hA).mp hfix, hmk⟩

/-- **Fixed points of a coprime quotient, internal form**, subgroup-equality version:
under the hypotheses of `coprime_fixedPoints_quotient_surjective_internal`,
`'C_H(A)` surjects onto the fixed points of `H ⧸ N`, i.e.
`(C(A) ⊓ H) N / N = C_{H ⧸ N}(A)`.  MathComp: `coprime_quotient_cent`
(`'C_G(A) / H = 'C_(G / H)(A / H)`). -/
theorem coprime_fixedPoints_quotient_eq_internal [Finite A]
    (hA : A ≤ normalizer (H : Set G)) {N : Subgroup G} [Finite N] [IsSolvable N]
    (hNH : N ≤ H) (hHN : H ≤ normalizer (N : Set G)) (hAN : A ≤ normalizer (N : Set G))
    (hco : (Nat.card A).Coprime (Nat.card N)) :
    letI := normalizerMulDistribMulAction hA
    haveI : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
    haveI : (N.subgroupOf H).SMulInvariant A :=
      smulInvariant_subgroupOf_of_le_normalizer hA hAN
    ((centralizer (A : Set G) ⊓ H).subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H))
      = FixedPoints.subgroup A (H ⧸ N.subgroupOf H) := by
  letI := normalizerMulDistribMulAction hA
  haveI : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  haveI : (N.subgroupOf H).SMulInvariant A := smulInvariant_subgroupOf_of_le_normalizer hA hAN
  haveI : Finite (N.subgroupOf H) := Finite.of_equiv _ (subgroupOfEquivOfLe hNH).symm.toEquiv
  haveI : IsSolvable (N.subgroupOf H) :=
    solvable_of_surjective (f := (subgroupOfEquivOfLe hNH).symm.toMonoidHom)
      (subgroupOfEquivOfLe hNH).symm.surjective
  have hco' : (Nat.card A).Coprime (Nat.card (N.subgroupOf H)) := by
    rwa [card_subgroupOf hNH]
  rw [← fixedPoints_conjAction_eq hA]
  exact coprime_fixedPoints_quotient_eq hco'

/-- **Existence of `A`-invariant Hall subgroups, internal form** (B&G 1.5(a)): if `A`
normalizes the finite solvable subgroup `H` coprimely, then for every `π` there is a
Hall π-subgroup `P` of `H` with `A ≤ 'N(P)`.  MathComp: `coprime_Hall_exists`. -/
theorem coprime_hall_exists_internal (π : Set ℕ) [Finite G] [IsSolvable H]
    (hA : A ≤ normalizer (H : Set G)) (hco : (Nat.card A).Coprime (Nat.card H)) :
    ∃ P : Subgroup G, P ≤ H ∧ (P.subgroupOf H).IsHall π ∧ A ≤ normalizer (P : Set G) := by
  letI := normalizerMulDistribMulAction hA
  obtain ⟨P₀, hP₀, hP₀inv⟩ := coprime_hall_exists (A := A) (G := H) π hco
  refine ⟨P₀.map H.subtype, map_subtype_le P₀, ?_, ?_⟩
  · rwa [map_subtype_subgroupOf]
  · refine le_normalizer_of_subgroupOf_smulInvariant hA (map_subtype_le P₀) ?_
    rwa [map_subtype_subgroupOf]

/-- **Conjugacy of `A`-invariant Hall subgroups, internal form** (B&G 1.5(c)): two
`A`-invariant Hall π-subgroups of a finite solvable `H` normalized coprimely by `A`
are conjugate by an element of `'C_H(A)`.  MathComp: `coprime_Hall_trans`
(`exists2 x, x \in 'C_G(A) & H1 :=: H2 :^ x`). -/
theorem coprime_hall_trans_internal {π : Set ℕ} [Finite G] [IsSolvable H]
    (hA : A ≤ normalizer (H : Set G)) (hco : (Nat.card A).Coprime (Nat.card H))
    {P Q : Subgroup G} (hPH : P ≤ H) (hP : (P.subgroupOf H).IsHall π)
    (hPA : A ≤ normalizer (P : Set G)) (hQH : Q ≤ H) (hQ : (Q.subgroupOf H).IsHall π)
    (hQA : A ≤ normalizer (Q : Set G)) :
    ∃ g ∈ centralizer (A : Set G) ⊓ H, Q = P.map (MulAut.conj g).toMonoidHom := by
  letI := normalizerMulDistribMulAction hA
  obtain ⟨c, hc, hconj⟩ := coprime_hall_trans (A := A) (G := H) hco hP
    (smulInvariant_subgroupOf_of_le_normalizer hA hPA) hQ
    (smulInvariant_subgroupOf_of_le_normalizer hA hQA)
  exact ⟨(c : G), mem_inf.mpr ⟨(mem_fixedPoints_conjAction_iff hA).mp hc, c.2⟩,
    eq_map_conj_of_subgroupOf_eq_map_conj hPH hQH hconj⟩

/-!
### Smoke tests: BGsection statement shapes

Kept as documentation that the internal forms elaborate in the shapes the BG
sections consume.
-/

-- BGsection1, proof of 1.10/1.11 (`rewrite -(coprime_cent_prod nGA) ... mul_subG`):
-- to bound `H`, bound the two factors of `H = [~: H, A] * 'C_H(A)`.
example [Finite G] [IsSolvable H] (hA : A ≤ normalizer (H : Set G))
    (hco : (Nat.card A).Coprime (Nat.card H)) {X : Subgroup G}
    (h1 : ⁅H, A⁆ ≤ X) (h2 : centralizer (A : Set G) ⊓ H ≤ X) : H ≤ X := by
  rw [← coprime_cent_prod_internal hA hco]
  exact sup_le h1 h2

-- BGsection1, proof of 1.8 (`-{1}(coprime_cent_prod _ coGA) ... mulSg`): every
-- element of `H` factors as a commutator part times a centralizing part.
example [Finite G] [IsSolvable H] (hA : A ≤ normalizer (H : Set G))
    (hco : (Nat.card A).Coprime (Nat.card H)) {g : G} (hg : g ∈ H) :
    ∃ x ∈ ⁅H, A⁆, ∃ c ∈ centralizer (A : Set G) ⊓ H, x * c = g := by
  rw [← SetLike.mem_coe, ← coprime_cent_prod_set_internal hA hco, Set.mem_mul] at hg
  obtain ⟨x, hx, c, hc, hxc⟩ := hg
  exact ⟨x, hx, c, hc, hxc⟩

-- BGsection13 (`have [S sylS nSE] := coprime_Hall_exists q nMsE coMsE solMs` and
-- `have [x cE'x ->] := coprime_Hall_trans ...`): destructure an invariant Hall
-- subgroup, and conjugate two of them by a fixed element.
example [Finite G] [IsSolvable H] (hA : A ≤ normalizer (H : Set G))
    (hco : (Nat.card A).Coprime (Nat.card H)) (q : ℕ) {T : Subgroup G} (hTH : T ≤ H)
    (hT : (T.subgroupOf H).IsHall {q}) (hTA : A ≤ normalizer (T : Set G)) :
    ∃ S ≤ H, ∃ x ∈ centralizer (A : Set G) ⊓ H, S = T.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨S, hSH, hS, hSA⟩ := coprime_hall_exists_internal {q} hA hco
  obtain ⟨x, hx, hconj⟩ := coprime_hall_trans_internal hA hco hTH hT hTA hSH hS hSA
  exact ⟨S, hSH, x, hx, hconj⟩

end CoprimeInternal
