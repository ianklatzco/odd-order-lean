/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.RepresentationTheory.Irreducible
import OddOrder.Mathlib.GroupTheory.CoprimeActionInternal

/-!
# Elementary abelian sections as `ZMod p`-representations

The dictionary between elementary abelian normal sections of a finite group
(multiplicative, subgroup language) and `ZMod p`-modules with a group action
(module language).  This is MathComp's `mxabelem` (D9 of the porting plan), realized
in *module* language: no matrices, no row vectors, no bases.  MathComp's `'rV(E)`
becomes the type synonym `h.Vec` of `Additive ↥V`, `abelem_repr` becomes a
`Representation (ZMod p) G h.Vec`, and `mx_irreducible` becomes
`Representation.IsIrreducible` / `IsSimpleModule` over the group algebra.

Placement note: the file lives in `GroupTheory/` (not `RepresentationTheory/`)
because it is the group-theoretic dictionary layer consumed by the Wielandt
fixed-point port and BGsection1–4, and it builds directly on the internal-action
transfer layer `CoprimeActionInternal.lean`; the representation theory it uses is
generic Mathlib material.

## Shape decisions (binding for downstream BG files)

* **The module carrier is a type synonym.**  `IsElementaryAbelian p H` is a `Prop`,
  so the module structure depends on the proof `h`.  Rather than `letI`-bound
  instances on `Additive H` (which stall typeclass resolution as soon as a class on
  `Submodule (ZMod p) (Additive H)` must be synthesized over local instances), we
  follow the `Representation.asModule` pattern: `h.Vec` is a type synonym of
  `Additive H` carrying *global* `AddCommGroup` and `Module (ZMod p)` instances
  keyed on `Vec`.  Statements consequently mention no `letI` at all.
* **One canonical Additive/Multiplicative spelling**: transport along the
  equivalence `h.toVec : H ≃ h.Vec` and its pointwise inverse `Vec.toMul`;
  membership lemmas are stated in the simp-normal form `x.toMul ∈ K`.  We never
  use `Multiplicative`.
* **The action**: a `MulDistribMulAction M H` induces a *global instance*
  `DistribMulAction M h.Vec` (Mathlib has no such transport for `Additive`; its
  `Representation.ofMulDistribMulAction` is `ℤ`-linear only), and with the
  `SMulCommClass M (ZMod p) h.Vec` instance, `Representation.ofDistribMulAction`
  yields `h.repr M : Representation (ZMod p) M h.Vec`.  Internal conjugation
  actions come in two flavours, composing with the existing conventions:
  the ambient group acting on a normal subgroup `V ⊴ G` goes through Mathlib's
  `ConjAct` instances, `hV.conjRepr := (hV.repr (ConjAct G)).comp toConjAct`;
  a subgroup actor `A ≤ 'N(V)` binds `letI := normalizerMulDistribMulAction hA`
  (Task 1's convention) and uses `hV.repr ↥A` directly.

## Main definitions and results

For `h : IsElementaryAbelian p H` (and, internally, a normal subgroup `V ⊴ G` with
`hV : IsElementaryAbelian p ↥V`):

* `IsElementaryAbelian.Vec` : the `ZMod p`-module underlying `H`, with
  `h.toVec : H ≃ h.Vec` (MathComp `abelem_rV`/`rVabelem`) and the scalar
  computation `h.smul_toVec : n • h.toVec v = h.toVec (v ^ n.val)`
  (MathComp `abelem_rV_X`-shaped).
* `IsElementaryAbelian.toSubmodule` : `Subgroup H ≃o Submodule (ZMod p) h.Vec`
  (MathComp: the subgroup ↔ subspace dictionary of `abelem_rV`).
* `IsElementaryAbelian.card_eq_pow_finrank` : `Nat.card H = p ^ finrank`
  (MathComp `dim_abelemE`).
* `IsElementaryAbelian.repr` / `IsElementaryAbelian.conjRepr` : the representation
  of an acting monoid / of `G` by conjugation (MathComp `abelem_repr`), computing
  as the action (`repr_apply_toVec`, `conjRepr_apply_coe` — MathComp `abelem_rV_J`).
* `IsElementaryAbelian.invariantSubgroupOrderIso` : `M`-invariant subgroups ≃o
  subrepresentations of `h.repr M`; internally,
  `Subgroup.smulInvariant_conjAct_iff` : `G`-invariant subgroups of `↥V` are the
  subgroups of `G` inside `V` that are normal in `G`.
* `IsElementaryAbelian.isIrreducible_repr_iff` (external) and
  `Subgroup.isMinNormal_iff_isIrreducible` /
  `Subgroup.isMinNormal_iff_isSimpleModule` (internal) : minimal
  (invariant/normal) ↔ irreducible (MathComp `abelem_mx_irrP`), in both the "no
  proper nontrivial invariant subgroup" and the `IsSimpleModule (ZMod p)[G]`
  (`Representation.asModule`) spellings, connected by
  `Representation.irreducible_iff_isSimpleModule_asModule`.
* `IsElementaryAbelian.conjRepr_ker` : the kernel is `'C_G(V)` (MathComp
  `rker_abelem`); `repr_ker_of_le_normalizer` for a subgroup actor `A ≤ 'N(V)`.
* `IsElementaryAbelian.conjQuotientRepr` (+ `conjQuotientRepr_injective`) : the
  induced faithful representation of `G ⧸ centralizer ↑V` (MathComp
  `abelem_mx_faithful` / `kquo_mx_faithful`).

The smoke-test `example`s at the end elaborate the exact statement shapes used at
MathComp usage sites (wielandt_fixpoint.v's `abelem_mx_irrP` destructuring,
BGsection1's `rker_abelem` rewrite, BGsection2's `abelem_rV_J` computation) and are
kept as documentation.
-/

namespace IsElementaryAbelian

variable {p : ℕ} {H : Type*} [Group H]

/-!
### The `ZMod p`-module structure

`IsElementaryAbelian` is a `Prop`, so the module structure depends on the proof
`h`; it is carried by the type synonym `h.Vec` (see the module docstring for why
this is a synonym with global instances rather than `letI`-bound instances on
`Additive H`).
-/

/-- The commutative-group structure on an elementary abelian group.  Reducible
non-instance (`h.Vec` below carries the packaged consequences); bind with `letI`
if needed directly. -/
abbrev commGroup (h : IsElementaryAbelian p H) : CommGroup H :=
  { ‹Group H› with mul_comm := h.1 }

/-- The `ZMod p`-module underlying an elementary abelian `p`-group `H`: a type
synonym of `Additive H` equipped with global `AddCommGroup` and
`Module (ZMod p)` instances (MathComp: the identification of a `p.-abelem` group
`E` with the row space `'rV(E)` over `'F_p` underlying `mxabelem`).  Translate
along `h.toVec : H ≃ h.Vec` and `Vec.toMul`. -/
@[nolint unusedArguments]
def Vec (_h : IsElementaryAbelian p H) := Additive H

/-- The defining equivalence of the type synonym `h.Vec`, multiplicative to
additive.  MathComp: `abelem_rV` (with `Vec.toMul` playing `rVabelem`). -/
def toVec (h : IsElementaryAbelian p H) : H ≃ h.Vec := Additive.ofMul

namespace Vec

variable {h : IsElementaryAbelian p H}

instance : AddCommGroup h.Vec :=
  letI := h.commGroup
  Additive.addCommGroup (α := H)

/-- The inverse of `IsElementaryAbelian.toVec`, additive to multiplicative.
MathComp: `rVabelem`. -/
def toMul (x : h.Vec) : H := Additive.toMul x

@[simp] theorem toMul_toVec (v : H) : (h.toVec v).toMul = v := rfl

@[simp] theorem toVec_toMul (x : h.Vec) : h.toVec x.toMul = x := rfl

@[simp] theorem toMul_zero : (0 : h.Vec).toMul = 1 := rfl

@[simp] theorem toMul_add (x y : h.Vec) : (x + y).toMul = x.toMul * y.toMul := rfl

@[simp] theorem toMul_neg (x : h.Vec) : (-x).toMul = x.toMul⁻¹ := rfl

theorem toVec_one (h : IsElementaryAbelian p H) : h.toVec 1 = 0 := rfl

theorem toVec_mul (h : IsElementaryAbelian p H) (v w : H) :
    h.toVec (v * w) = h.toVec v + h.toVec w := rfl

theorem toMul_injective : Function.Injective (toMul (h := h)) := fun x y hxy => by
  rw [← toVec_toMul (h := h) x, ← toVec_toMul (h := h) y, hxy]

@[simp] theorem toMul_eq_one_iff {x : h.Vec} : x.toMul = 1 ↔ x = 0 :=
  ⟨fun hx => toMul_injective (by rw [hx, toMul_zero]), fun hx => by rw [hx, toMul_zero]⟩

theorem toMul_nsmul (n : ℕ) (x : h.Vec) : (n • x).toMul = x.toMul ^ n :=
  _root_.toMul_nsmul n x

end Vec

instance (h : IsElementaryAbelian p H) : Module (ZMod p) h.Vec :=
  AddCommGroup.zmodModule fun x =>
    Vec.toMul_injective (by rw [Vec.toMul_nsmul, h.2, Vec.toMul_zero])

/-- The `ZMod p`-scalar action on an elementary abelian group computes as a power:
`n • h.toVec v = h.toVec (v ^ n.val)`.  MathComp: `abelem_rV_X` (scalar action ↔
group exponentiation). -/
theorem smul_toVec [NeZero p] (h : IsElementaryAbelian p H) (n : ZMod p) (v : H) :
    n • h.toVec v = h.toVec (v ^ n.val) := by
  conv_lhs => rw [← ZMod.natCast_rightInverse n, Nat.cast_smul_eq_nsmul]
  exact Vec.toMul_injective (by rw [Vec.toMul_nsmul, Vec.toMul_toVec, Vec.toMul_toVec])

/-- `Vec.toMul` form of `IsElementaryAbelian.smul_toVec`. -/
theorem Vec.toMul_zmod_smul [NeZero p] {h : IsElementaryAbelian p H} (n : ZMod p)
    (x : h.Vec) : (n • x).toMul = x.toMul ^ n.val := by
  conv_lhs => rw [← Vec.toVec_toMul (h := h) x]
  rw [h.smul_toVec, Vec.toMul_toVec]

/-!
### Subgroups as submodules
-/

/-- Subgroups of `H` are the additive subgroups of `h.Vec`: the synonym-typed
version of Mathlib's `Subgroup.toAddSubgroup` (which we cannot use directly:
its target `AddSubgroup (Additive H)` carries the instance `Additive.addGroup`,
not the `Vec`-keyed one). -/
def toAddSubgroup (h : IsElementaryAbelian p H) : Subgroup H ≃o AddSubgroup h.Vec where
  toFun K :=
    { carrier := {x : h.Vec | x.toMul ∈ K}
      add_mem' := fun hx hy => K.mul_mem hx hy
      zero_mem' := K.one_mem
      neg_mem' := fun hx => K.inv_mem hx }
  invFun S :=
    { carrier := {v : H | h.toVec v ∈ S}
      mul_mem' := fun hx hy => S.add_mem hx hy
      one_mem' := S.zero_mem
      inv_mem' := fun hx => S.neg_mem hx }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := ⟨fun hle _ hv => hle hv, fun hle _ hx => hle hx⟩

/-- **Subgroups of an elementary abelian group are its `ZMod p`-submodules**:
`IsElementaryAbelian.toAddSubgroup` composed with `AddSubgroup.toZModSubmodule`,
as one order isomorphism.  MathComp: the subgroup-of-`E` ↔ subspace-of-`'rV(E)`
dictionary carried by `abelem_rV`/`rVabelem`. -/
def toSubmodule (h : IsElementaryAbelian p H) :
    Subgroup H ≃o Submodule (ZMod p) h.Vec :=
  h.toAddSubgroup.trans (AddSubgroup.toZModSubmodule p)

@[simp]
theorem mem_toSubmodule (h : IsElementaryAbelian p H) {K : Subgroup H} {x : h.Vec} :
    x ∈ h.toSubmodule K ↔ x.toMul ∈ K :=
  Iff.rfl

@[simp]
theorem mem_toSubmodule_symm (h : IsElementaryAbelian p H)
    {W : Submodule (ZMod p) h.Vec} {v : H} :
    v ∈ h.toSubmodule.symm W ↔ h.toVec v ∈ W := by
  rw [show (v ∈ h.toSubmodule.symm W ↔
      h.toVec v ∈ h.toSubmodule (h.toSubmodule.symm W)) from Iff.rfl,
    h.toSubmodule.apply_symm_apply]

/-- **Order and dimension** of a finite elementary abelian `p`-group:
`|H| = p ^ dim H` for the `ZMod p`-dimension of the associated module.
MathComp: `dim_abelemE` (with `card_pgroup`). -/
theorem card_eq_pow_finrank [Finite H] (h : IsElementaryAbelian p H)
    (hp : p.Prime) : Nat.card H = p ^ Module.finrank (ZMod p) h.Vec := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite h.Vec := Finite.of_equiv H h.toVec
  calc Nat.card H = Nat.card h.Vec := Nat.card_congr h.toVec
    _ = Nat.card (ZMod p) ^ Module.finrank (ZMod p) h.Vec :=
        Module.natCard_eq_pow_finrank
    _ = p ^ Module.finrank (ZMod p) h.Vec := by rw [Nat.card_zmod]

/-!
### Group actions and the representation

A `MulDistribMulAction M H` transports to a `DistribMulAction M h.Vec`; Mathlib
has no `Additive`-transport instance for `MulDistribMulAction` (only the
`ℤ`-linear `Representation.ofMulDistribMulAction`), so we provide it here, keyed
on the synonym.  Together with the `SMulCommClass` instance this feeds
`Representation.ofDistribMulAction`.
-/

section Action

variable {M : Type*} [Monoid M] [MulDistribMulAction M H]

namespace Vec

variable {h : IsElementaryAbelian p H}

instance : DistribMulAction M h.Vec where
  smul m x := h.toVec (m • x.toMul)
  one_smul x := toMul_injective (one_smul M x.toMul)
  mul_smul m n x := toMul_injective (mul_smul m n x.toMul)
  smul_zero m := toMul_injective (smul_one m)
  smul_add m x y := toMul_injective (smul_mul' m x.toMul y.toMul)

@[simp] theorem toMul_smul (m : M) (x : h.Vec) : (m • x).toMul = m • x.toMul := rfl

/-- The `M`-action and the `ZMod p`-scalars on `h.Vec` commute: every additive map
is `ZMod p`-linear. -/
instance : SMulCommClass M (ZMod p) h.Vec :=
  ⟨fun m c x => ZMod.map_smul (DistribSMul.toAddMonoidHom h.Vec m) c x⟩

end Vec

variable (M) in
/-- **The abelem representation, external form** (MathComp `abelem_repr` with an
abstract actor): a monoid `M` acting on an elementary abelian `p`-group `H` by
`MulDistribMulAction` acts `ZMod p`-linearly on `h.Vec`. -/
def repr (h : IsElementaryAbelian p H) : Representation (ZMod p) M h.Vec :=
  Representation.ofDistribMulAction (ZMod p) M h.Vec

@[simp]
theorem repr_apply_toVec (h : IsElementaryAbelian p H) (m : M) (v : H) :
    h.repr M m (h.toVec v) = h.toVec (m • v) := rfl

@[simp]
theorem toMul_repr_apply (h : IsElementaryAbelian p H) (m : M) (x : h.Vec) :
    (h.repr M m x).toMul = m • x.toMul := rfl

/-- Elements of the kernel of the abelem representation are exactly the elements
acting trivially.  MathComp: `rker`-membership; see
`IsElementaryAbelian.conjRepr_ker` for the internal `rker_abelem` form. -/
theorem mem_ker_repr_iff (h : IsElementaryAbelian p H) {M : Type*} [Group M]
    [MulDistribMulAction M H] {m : M} :
    m ∈ (h.repr M).ker ↔ ∀ v : H, m • v = v := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hm v
    have h1 : h.repr M m (h.toVec v) = h.toVec v := by rw [hm]; rfl
    simpa using congrArg Vec.toMul h1
  · intro hm
    refine LinearMap.ext fun x => Vec.toMul_injective ?_
    rw [Module.End.one_apply, toMul_repr_apply, hm x.toMul]

/-!
#### Invariant subgroups and subrepresentations

The subgroup ↔ submodule dictionary `h.toSubmodule` restricts to a dictionary
between `M`-invariant subgroups (`Subgroup.SMulInvariant`, the external-action
convention of `CoprimeAction.lean`) and subrepresentations of `h.repr M`.
MathComp: the `mxmodule`/`subg` dictionary of `mxabelem`.
-/

variable (M)

/-- An `M`-invariant subgroup of `H`, as a subrepresentation of `h.repr M`. -/
def toSubrepresentation (h : IsElementaryAbelian p H) (K : Subgroup H)
    [K.SMulInvariant M] : Subrepresentation (h.repr M) where
  toSubmodule := h.toSubmodule K
  apply_mem_toSubmodule m v hv := by
    rw [h.mem_toSubmodule] at hv ⊢
    exact Subgroup.SMulInvariant.smul_mem m hv

@[simp]
theorem mem_toSubrepresentation (h : IsElementaryAbelian p H) {K : Subgroup H}
    [K.SMulInvariant M] {x : h.Vec} :
    x ∈ h.toSubrepresentation M K ↔ x.toMul ∈ K :=
  Iff.rfl

/-- The subgroup underlying a subrepresentation of `h.repr M` is `M`-invariant. -/
theorem smulInvariant_toSubmodule_symm (h : IsElementaryAbelian p H)
    (σ : Subrepresentation (h.repr M)) :
    (h.toSubmodule.symm σ.toSubmodule).SMulInvariant M := by
  refine ⟨fun m v hv => ?_⟩
  rw [h.mem_toSubmodule_symm] at hv ⊢
  exact σ.apply_mem_toSubmodule m hv

/-- **Invariant subgroups are subrepresentations**: `h.toSubmodule` restricts to an
order isomorphism between the `M`-invariant subgroups of `H` and the
subrepresentations of `h.repr M`.  MathComp: the `mxmodule` dictionary of
`mxabelem` (`abelem_rV_subg`-shaped). -/
def invariantSubgroupOrderIso (h : IsElementaryAbelian p H) :
    {K : Subgroup H // K.SMulInvariant M} ≃o Subrepresentation (h.repr M) where
  toFun K := haveI := K.2; h.toSubrepresentation M K.1
  invFun σ := ⟨h.toSubmodule.symm σ.toSubmodule, h.smulInvariant_toSubmodule_symm M σ⟩
  left_inv K := Subtype.ext (h.toSubmodule.symm_apply_apply K.1)
  right_inv σ :=
    Subrepresentation.toSubmodule_injective (h.toSubmodule.apply_symm_apply σ.toSubmodule)
  map_rel_iff' := ⟨fun hle _ hv => hle hv, fun hle _ hx => hle hx⟩

/-- **Minimal invariance is irreducibility, external form** (MathComp
`abelem_mx_irrP` with an abstract actor): the representation of `M` on an
elementary abelian `p`-group `H` is irreducible iff `H` is nontrivial and has no
nontrivial proper `M`-invariant subgroup.  See
`Subgroup.isMinNormal_iff_isIrreducible` for the internal (conjugation) form. -/
theorem isIrreducible_repr_iff [Fact p.Prime] (h : IsElementaryAbelian p H) :
    (h.repr M).IsIrreducible ↔
      Nontrivial H ∧ ∀ K : Subgroup H, K.SMulInvariant M → K ≠ ⊥ → K = ⊤ := by
  constructor
  · intro hirr
    haveI := hirr
    have hnt : Nontrivial H := by
      rcases subsingleton_or_nontrivial H with hs | hnt
      · haveI : Subsingleton h.Vec := h.toVec.symm.subsingleton
        exact absurd
          (Subrepresentation.toSubmodule_injective
            (Subsingleton.elim ((⊥ : Subrepresentation (h.repr M)).toSubmodule)
              ((⊤ : Subrepresentation (h.repr M)).toSubmodule)))
          bot_ne_top
      · exact hnt
    refine ⟨hnt, fun K hK hKbot => ?_⟩
    haveI := hK
    rcases hirr.eq_bot_or_eq_top (h.toSubrepresentation M K) with hs | hs
    · refine absurd (h.toSubmodule.injective ?_) hKbot
      rw [map_bot]
      exact congrArg Subrepresentation.toSubmodule hs
    · refine h.toSubmodule.injective ?_
      rw [map_top]
      exact congrArg Subrepresentation.toSubmodule hs
  · rintro ⟨hnt, hmin⟩
    haveI := hnt
    haveI : Nontrivial h.Vec := h.toVec.symm.nontrivial
    haveI hnt' : Nontrivial (Subrepresentation (h.repr M)) :=
      ⟨⊥, ⊤, fun hbt =>
        bot_ne_top (α := Submodule (ZMod p) h.Vec)
          (congrArg Subrepresentation.toSubmodule hbt)⟩
    refine { toNontrivial := hnt', eq_bot_or_eq_top := fun σ => ?_ }
    rcases eq_or_ne (h.toSubmodule.symm σ.toSubmodule) ⊥ with hKb | hKb
    · left
      refine Subrepresentation.toSubmodule_injective ?_
      have h1 := congrArg h.toSubmodule hKb
      rwa [h.toSubmodule.apply_symm_apply, map_bot] at h1
    · right
      have hKtop := hmin _ (h.smulInvariant_toSubmodule_symm M σ) hKb
      refine Subrepresentation.toSubmodule_injective ?_
      have h1 := congrArg h.toSubmodule hKtop
      rwa [h.toSubmodule.apply_symm_apply, map_top] at h1

end Action

end IsElementaryAbelian

/-!
### Precomposition with a surjection

A helper for the internal layer: precomposing a representation with a surjective
monoid homomorphism (here `toConjAct : G ≃* ConjAct G`) does not change the
subrepresentation lattice, hence not irreducibility.
-/

/-- Precomposition with a surjective monoid homomorphism preserves
irreducibility. -/
theorem Representation.isIrreducible_comp_iff {k G G' V : Type*} [Field k]
    [Monoid G] [Monoid G'] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (f : G' →* G) (hf : Function.Surjective f) :
    Representation.IsIrreducible (ρ.comp f) ↔ ρ.IsIrreducible := by
  refine OrderIso.isSimpleOrder_iff
    (⟨⟨fun τ => ⟨τ.toSubmodule, fun g v hv => ?_⟩,
      fun σ => ⟨σ.toSubmodule, fun g' v hv => σ.apply_mem_toSubmodule (f g') hv⟩,
      fun τ => rfl, fun σ => rfl⟩, Iff.rfl⟩ :
        Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ)
  obtain ⟨g', rfl⟩ := hf g
  exact τ.apply_mem_toSubmodule g' hv

/-!
### The internal (conjugation) dictionary

The consumer shape of BGsection1–4 and wielandt_fixpoint.v: the ambient group `G`
acts by conjugation on a normal elementary abelian subgroup `V ⊴ G`.  The action
goes through Mathlib's `ConjAct` instances (`Subgroup.conjMulDistribMulAction`),
so no new action data is needed; the representation of `G` itself is obtained by
precomposing with `toConjAct : G ≃* ConjAct G`.
-/

section Internal

variable {G : Type*} [Group G] {p : ℕ} {V : Subgroup G}

namespace Subgroup

/-- Under the conjugation action of `ConjAct G` on a normal subgroup `V ⊴ G`, the
invariant subgroups of `↥V` are exactly the subgroups of `G` inside `V` that are
normal in `G`.  MathComp: the `[acts G, on W | 'JG]`/normality interchange used
with `mxmodule` in the `abelem` dictionary. -/
theorem smulInvariant_conjAct_iff [V.Normal] {K : Subgroup ↥V} :
    K.SMulInvariant (ConjAct G) ↔ (K.map V.subtype).Normal := by
  constructor
  · intro hK
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨ConjAct.toConjAct g • v, hK.smul_mem _ hv, rfl⟩
  · intro hN
    refine ⟨fun c v hv => ?_⟩
    have hmem : ((c • v : ↥V) : G) ∈ K.map V.subtype := by
      rw [ConjAct.Subgroup.val_conj_smul, ConjAct.smul_def]
      exact hN.conj_mem _ (mem_map_of_mem V.subtype hv) (ConjAct.ofConjAct c)
    obtain ⟨w, hw, hwv⟩ := hmem
    rwa [show w = c • v from Subtype.ext hwv] at hw

/-- `Subgroup.smulInvariant_conjAct_iff` in `subgroupOf` form: for `W ≤ V`, the
subgroup `W.subgroupOf V` is `ConjAct G`-invariant iff `W ⊴ G`. -/
theorem subgroupOf_smulInvariant_conjAct_iff [V.Normal] {W : Subgroup G}
    (hWV : W ≤ V) : (W.subgroupOf V).SMulInvariant (ConjAct G) ↔ W.Normal := by
  rw [smulInvariant_conjAct_iff, map_subgroupOf_eq_of_le hWV]

end Subgroup

namespace IsElementaryAbelian

/-- **The abelem representation** (MathComp `abelem_repr`): a normal elementary
abelian `p`-subgroup `V ⊴ G` affords a `ZMod p`-linear representation of `G` on
`hV.Vec` by conjugation. -/
def conjRepr [V.Normal] (hV : IsElementaryAbelian p ↥V) :
    Representation (ZMod p) G hV.Vec :=
  (hV.repr (ConjAct G)).comp ConjAct.toConjAct.toMonoidHom

theorem conjRepr_def [V.Normal] (hV : IsElementaryAbelian p ↥V) :
    hV.conjRepr = (hV.repr (ConjAct G)).comp ConjAct.toConjAct.toMonoidHom :=
  rfl

/-- **The abelem representation is conjugation** (MathComp `abelem_rV_J`):
`hV.conjRepr g` sends (the vector of) `v` to (the vector of) `g * v * g⁻¹`. -/
@[simp]
theorem conjRepr_apply_coe [V.Normal] (hV : IsElementaryAbelian p ↥V) (g : G)
    (x : hV.Vec) : ((hV.conjRepr g x).toMul : G) = g * (x.toMul : G) * g⁻¹ :=
  rfl

end IsElementaryAbelian

namespace Subgroup

/-- **Minimal normal ↔ irreducible** (MathComp `abelem_mx_irrP`): a normal
elementary abelian `p`-subgroup `V ⊴ G` is a minimal normal subgroup of `G` iff
its conjugation representation `hV.conjRepr` is irreducible. -/
theorem isMinNormal_iff_isIrreducible [Fact p.Prime] [V.Normal]
    (hV : IsElementaryAbelian p ↥V) :
    V.IsMinNormal ↔ hV.conjRepr.IsIrreducible := by
  rw [IsElementaryAbelian.conjRepr_def,
    Representation.isIrreducible_comp_iff _ _ ConjAct.toConjAct.surjective,
    hV.isIrreducible_repr_iff (ConjAct G)]
  constructor
  · rintro ⟨-, hbot, hmin⟩
    refine ⟨(nontrivial_iff_ne_bot V).mpr hbot, fun K hK hKbot => ?_⟩
    have hKn : (K.map V.subtype).Normal := smulInvariant_conjAct_iff.mp hK
    have hKmapbot : K.map V.subtype ≠ ⊥ := fun hb =>
      hKbot (map_injective V.subtype_injective (by rwa [map_bot]))
    have hKV := hmin _ hKn (map_subtype_le K) hKmapbot
    have htop : (⊤ : Subgroup ↥V).map V.subtype = V := by
      rw [← MonoidHom.range_eq_map, range_subtype]
    exact map_injective V.subtype_injective (hKV.trans htop.symm)
  · rintro ⟨hnt, hmin⟩
    refine ⟨‹V.Normal›, (nontrivial_iff_ne_bot V).mp hnt, fun W hWn hWV hWbot => ?_⟩
    have hK : (W.subgroupOf V).SMulInvariant (ConjAct G) :=
      (subgroupOf_smulInvariant_conjAct_iff hWV).mpr hWn
    have hKbot : W.subgroupOf V ≠ ⊥ := fun hb => hWbot (by
      have h1 := congrArg (map V.subtype) hb
      rwa [map_subgroupOf_eq_of_le hWV, map_bot] at h1)
    exact le_antisymm hWV (subgroupOf_eq_top.mp (hmin _ hK hKbot))

/-- The `IsSimpleModule`-over-the-group-algebra spelling of
`Subgroup.isMinNormal_iff_isIrreducible`, via `Representation.asModule`.
MathComp: `abelem_mx_irrP` composed with the `mxsimple` reading. -/
theorem isMinNormal_iff_isSimpleModule [Fact p.Prime] [V.Normal]
    (hV : IsElementaryAbelian p ↥V) :
    V.IsMinNormal ↔
      IsSimpleModule (MonoidAlgebra (ZMod p) G) hV.conjRepr.asModule :=
  (isMinNormal_iff_isIrreducible hV).trans
    (Representation.irreducible_iff_isSimpleModule_asModule _)

end Subgroup

namespace IsElementaryAbelian

/-- **The kernel of the abelem representation is the centralizer** (MathComp
`rker_abelem`): `ker hV.conjRepr = 'C_G(V)`. -/
theorem conjRepr_ker [V.Normal] (hV : IsElementaryAbelian p ↥V) :
    hV.conjRepr.ker = Subgroup.centralizer (V : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg v hv
    have h1 : hV.conjRepr g (hV.toVec ⟨v, hv⟩) = hV.toVec ⟨v, hv⟩ := by rw [hg]; rfl
    have h2 : g * v * g⁻¹ = v := congrArg (fun x => ((Vec.toMul x : ↥V) : G)) h1
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  · intro hg
    refine LinearMap.ext fun x => Vec.toMul_injective (Subtype.ext ?_)
    change g * (x.toMul : G) * g⁻¹ = (x.toMul : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hg (x.toMul : G) x.toMul.2).symm

/-- **The kernel of the abelem representation, subgroup-actor form** (MathComp
`rker_abelem` at the BG usage sites, e.g. BGsection1's
`'C_A(E) = 'ker (reprGLm rP)`): for an actor `A ≤ 'N(V)` acting by conjugation
(Task 1's `normalizerMulDistribMulAction` convention), the kernel of `hV.repr ↥A`
is `'C(V) ∩ A`, as a subgroup of `A`. -/
theorem repr_ker_of_le_normalizer {A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (V : Set G)) (hV : IsElementaryAbelian p ↥V) :
    letI := Subgroup.normalizerMulDistribMulAction hA
    (hV.repr ↥A).ker = (Subgroup.centralizer (V : Set G)).subgroupOf A := by
  letI := Subgroup.normalizerMulDistribMulAction hA
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro ha v hv
    have h1 : hV.repr ↥A a (hV.toVec ⟨v, hv⟩) = hV.toVec ⟨v, hv⟩ := by rw [ha]; rfl
    have h2 : (a : G) * v * (a : G)⁻¹ = v :=
      congrArg (fun x => ((Vec.toMul x : ↥V) : G)) h1
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  · intro ha
    refine LinearMap.ext fun x => Vec.toMul_injective (Subtype.ext ?_)
    change (a : G) * (x.toMul : G) * (a : G)⁻¹ = (x.toMul : G)
    exact mul_inv_eq_iff_eq_mul.mpr (ha (x.toMul : G) x.toMul.2).symm

/-- The abelem representation descends to the quotient by its kernel: the induced
representation of `G ⧸ 'C_G(V)`.  MathComp: `abelem_repr` over the quotient
(`kquo_repr`). -/
def conjQuotientRepr [V.Normal] (hV : IsElementaryAbelian p ↥V) :
    Representation (ZMod p) (G ⧸ Subgroup.centralizer (V : Set G)) hV.Vec :=
  QuotientGroup.lift _ hV.conjRepr (le_of_eq hV.conjRepr_ker.symm)

@[simp]
theorem conjQuotientRepr_mk [V.Normal] (hV : IsElementaryAbelian p ↥V) (g : G) :
    hV.conjQuotientRepr (g : G ⧸ Subgroup.centralizer (V : Set G)) =
      hV.conjRepr g :=
  rfl

/-- **The quotient abelem representation is faithful** (MathComp
`abelem_mx_faithful` / `kquo_mx_faithful`). -/
theorem conjQuotientRepr_injective [V.Normal] (hV : IsElementaryAbelian p ↥V) :
    Function.Injective hV.conjQuotientRepr := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, ← hV.conjRepr_ker]
  exact hx

end IsElementaryAbelian

end Internal

/-!
### Smoke tests: BG/wielandt statement shapes

Kept as documentation that the dictionary elaborates in the shapes the BG sections
and the Wielandt fixed-point argument consume.
-/

section SmokeTests

variable {G : Type*} [Group G]

-- wielandt_fixpoint.v (`move/(abelem_mx_irrP abelV ntV nVG): (minV) => mx_irrV`):
-- destructure a minimal normal elementary abelian subgroup into an irreducible
-- (simple) module over the group algebra.
example {p : ℕ} [Fact p.Prime] {V : Subgroup G} [V.Normal]
    (hV : IsElementaryAbelian p ↥V) (hmin : V.IsMinNormal) :
    IsSimpleModule (MonoidAlgebra (ZMod p) G) hV.conjRepr.asModule :=
  (Subgroup.isMinNormal_iff_isSimpleModule hV).mp hmin

-- BGsection1, `logn_quotient_cent_abelem` (`'C_A(E) = 'ker (reprGLm rP)` with
-- `rP := abelem_repr abelE ntE nEA`): rewrite the centralizer of an elementary
-- abelian subgroup as the kernel of its abelem representation.
example {p : ℕ} {V A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (hV : IsElementaryAbelian p ↥V) :
    letI := Subgroup.normalizerMulDistribMulAction hA
    (Subgroup.centralizer (V : Set G)).subgroupOf A = (hV.repr ↥A).ker :=
  (hV.repr_ker_of_le_normalizer hA).symm

-- BGsection2 (`abelem_rV_J`, in the proof of `charf'_GL2_abelian`-adjacent
-- computations): the representation computes conjugation, definitionally.
example {p : ℕ} {V : Subgroup G} [V.Normal] (hV : IsElementaryAbelian p ↥V)
    (g : G) (v : ↥V) :
    ((hV.conjRepr g (hV.toVec v)).toMul : G) = g * v * g⁻¹ :=
  rfl

-- BGsection1/wielandt (`dim_abelemE` with `card_pgroup`): the order of an
-- elementary abelian subgroup is `p ^ dim`.
example {p : ℕ} [Finite G] {V : Subgroup G} (hV : IsElementaryAbelian p ↥V)
    (hp : p.Prime) :
    Nat.card ↥V = p ^ Module.finrank (ZMod p) hV.Vec :=
  hV.card_eq_pow_finrank hp

end SmokeTests
