/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import OddOrder.Mathlib.GroupTheory.Frobenius
import OddOrder.Mathlib.RepresentationTheory.VirtualChar

/-!
# Frobenius' kernel theorem (1901)

M3 Task 4: in a Frobenius configuration the kernel *exists*.  Given a finite group `G` and a
nontrivial proper subgroup `H` that is **malnormal** (`H ⊓ H^g = ⊥` for every `g ∉ H` — Task
3's spelling `H ⊓ H.map (MulAut.conj g).toMonoidHom = ⊥`), the set

`H.frobeniusKernelSet = {g | ∀ x, g ∈ H^x → g = 1}`

(`1` together with everything outside all conjugates of `H`) is a *normal subgroup* `K` with
`IsComplement' K H` and `Nat.card K = H.index`, packaged as `Subgroup.IsFrobenius K H`
(`Subgroup.exists_isFrobenius_of_malnormal`).  This is the theorem with no known
character-free proof; the argument here is the classical induced-character one
(Isaacs 7.2 / Peterfalvi 3.1).  The action form (a transitive action with nontrivial
one-point stabilizers and trivial two-point stabilizers has a normal "fixed-point-free plus
identity" subgroup) is derived as a corollary, `MulAction.exists_isFrobenius_stabilizer`.

Sits in a sibling file to `Frobenius.lean` (as that file's docstring announces): the
predicates there are character-free, while everything here runs through the M2 character
stack (`Induced.lean`, `VirtualChar.lean`, `CharacterArith.lean`).

## The proof

1. **Geometry of malnormality** (`Subgroup.mem_of_ne_one_mem_map_conj`): a nontrivial element
   of `H` lying in `H^x` forces `x ∈ H`.  Hence `H` is self-normalizing
   (`Subgroup.normalizer_eq_self_of_malnormal`), the conjugates of `H` are indexed by `G ⧸ H`
   and intersect pairwise in `1`, and a counting bijection
   `(G ⧸ H) × H^# ≃ G \ frobeniusKernelSet` gives
   `Nat.card (frobeniusKernelSet) = H.index` (`Subgroup.card_frobeniusKernelSet` — the
   cardinality form of MathComp's `Frobenius_partition`).
2. **Induced class functions on a malnormal subgroup**: `ind H φ` vanishes outside the
   conjugates of `H` (`ClassFunction.ind_apply_eq_zero_of_forall_notMem`), and on `H^#` the
   defining average collapses to `φ` itself (`ClassFunction.ind_apply_coe_of_malnormal`), so
   `res H (ind H φ) = φ` whenever `φ 1 = 0`
   (`ClassFunction.res_ind_eq_self_of_malnormal`).  Consequently induction is an **isometry
   on the class functions vanishing at `1`** (`ClassFunction.cfInner_ind_ind_of_malnormal`:
   `⟪ind α, ind β⟫_[G] = ⟪α, β⟫_[H]` for `α 1 = 0`).  This is the trivial-intersection seed
   of the Dade isometry: the future PFsection2 correspondent of MathComp's
   `normedTI_isometry`.
3. **The Frobenius system of irreducibles**: for each nonprincipal `θ : Irr H`, with
   `α_θ := θ - θ 1 • 1` (which vanishes at `1`),

   `Irr.frobeniusInd θ := ind H α_θ + θ 1 • 1  (= ind θ - θ 1 • ind 1 + θ 1 • 1)`

   takes the value `θ h` on `H^#`-conjugates, `θ 1` on all of `frobeniusKernelSet`, is a
   virtual character, and has norm `1` by the isometry:
   `⟪φ_θ, φ_θ⟫ = ⟪α_θ, α_θ⟫ + 2 θ 1 ⟪α_θ, 1⟫ + θ 1 ^ 2 = (1 + θ 1 ^ 2) - 2 θ 1 ^ 2 + θ 1 ^ 2 = 1`.
   Being positive at `1`, the norm-`1` classification (`vchar_norm1`) makes it an honest
   irreducible character `χ_θ` of `G` (`Irr.exists_coe_eq_frobeniusInd`).
4. **Kernel extraction**: `frobeniusKernelSet = ⋂_θ ker χ_θ`: one inclusion is the computed
   values; for the other, a nontrivial `h ∈ H` is separated from `1` by some nonprincipal
   `θ` (`Irr.exists_ne_one_apply_ne`, second orthogonality), and then `χ_θ (x h x⁻¹) = θ h ≠
   θ 1 = χ_θ 1`.  The intersection description supplies the multiplicative closure of the
   kernel set (everything else about it — `1 ∈`, inverses, conjugation-invariance — is
   direct), and the counting from step 1 supplies `IsComplement'`.

## Main declarations

* `Subgroup.frobeniusKernelSet H` — the kernel set.
* `ClassFunction.cfInner_ind_ind_of_malnormal` — TI-induction isometry on `1`-vanishing class
  functions (MathComp `normedTI_isometry`-correspondent, approximate).
* `Irr.frobeniusInd` — the Isaacs 7.2 virtual character `φ_θ`, with its value/norm lemmas.
* `Subgroup.exists_isFrobenius_of_malnormal` — **Frobenius' kernel theorem**, internal form.
* `MulAction.exists_isFrobenius_stabilizer` — the action-form corollary
  (`{g | ∀ x, g • x ≠ x} ∪ {1}` is a normal subgroup, Frobenius against every stabilizer).

## Design notes

* **Hypothesis spelling.** Malnormality is quantified as `∀ g ∉ H, H ⊓ H^g = ⊥`, matching the
  conjugation convention `H.map (MulAut.conj g).toMonoidHom` fixed in STATUS.md and the
  bridge lemmas of `Frobenius.lean` (which state the `K`-relative version `∀ g ∈ K^#, …`;
  the global version here implies it on the constructed kernel).
* **The kernel set is `{g | ∀ x, g ∈ H^x → g = 1}`** rather than the union form
  `{1} ∪ (⋃ₓ H^x)ᶜ`: the two agree (`Subgroup.mem_frobeniusKernelSet_iff`) because `1` lies
  in every conjugate, and the implication form gives the closure proofs and the value
  computations without case splits.
* **`K.Normal` needs no characters** — the kernel set is conjugation-invariant by
  construction.  Only `mul_mem` goes through the intersection-of-kernels description.
* MathComp's `frobenius.v` is not on this machine; per the M3 plan the correspondents cited
  here (`Frobenius_partition`, `normedTI_isometry`) are from the survey digest and the
  BG/PF usage sites, marked approximate in `docs/NAME_MAP.md`.
-/

noncomputable section

open Finset
open scoped ClassFunction

universe u

variable {G : Type u} [Group G]

/-!
### The geometry of a malnormal subgroup
-/

namespace Subgroup

variable {H : Subgroup G}

/-- Membership in a conjugate, unfolded: `g ∈ H^x ↔ x⁻¹ * g * x ∈ H` (project conjugation
spelling `H.map (MulAut.conj x).toMonoidHom` for `H^x = x H x⁻¹`). -/
theorem mem_map_conj_iff {x g : G} :
    g ∈ H.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * g * x ∈ H := by
  rw [mem_map_equiv, MulAut.conj_symm_apply]

/-- The collapse lemma of malnormality: a *nontrivial* element of `H` lying in the conjugate
`H^x` forces `x ∈ H`.  This is the engine behind self-normalization, the conjugate-partition
counting, and the collapse of induced-character sums. -/
theorem mem_of_ne_one_mem_map_conj
    (hmal : ∀ g ∉ H, H ⊓ H.map (MulAut.conj g).toMonoidHom = ⊥)
    {h x : G} (hh : h ∈ H) (hh1 : h ≠ 1)
    (hhx : h ∈ H.map (MulAut.conj x).toMonoidHom) : x ∈ H := by
  by_contra hx
  have hmem : h ∈ H ⊓ H.map (MulAut.conj x).toMonoidHom := mem_inf.mpr ⟨hh, hhx⟩
  rw [hmal x hx, mem_bot] at hmem
  exact hh1 hmem

/-- A nontrivial malnormal subgroup is self-normalizing.  (MathComp proves the corresponding
`'N_G(H) = H` inside the Frobenius structure theory.) -/
theorem normalizer_eq_self_of_malnormal
    (hmal : ∀ g ∉ H, H ⊓ H.map (MulAut.conj g).toMonoidHom = ⊥) (hbot : H ≠ ⊥) :
    normalizer (H : Set G) = H := by
  refine le_antisymm (fun g hg => ?_) le_normalizer
  obtain ⟨h, hhH, hh1⟩ := H.bot_or_exists_ne_one.resolve_left hbot
  refine mem_of_ne_one_mem_map_conj hmal hhH hh1 (mem_map_conj_iff.mpr ?_)
  exact (mem_normalizer_iff''.mp hg h).mp hhH

variable (H) in
/-- The **Frobenius kernel set** of `H`: the identity together with all elements lying
outside every conjugate of `H`, spelled as the implication
`{g | ∀ x, g ∈ H^x → g = 1}` (see `mem_frobeniusKernelSet_iff` for the union form).
Frobenius' kernel theorem (`exists_isFrobenius_of_malnormal`) upgrades this set to a normal
subgroup when `H` is malnormal. -/
def frobeniusKernelSet : Set G :=
  {g : G | ∀ x : G, g ∈ H.map (MulAut.conj x).toMonoidHom → g = 1}

/-- The kernel set is `{1}` together with the complement of the union of the conjugates. -/
theorem mem_frobeniusKernelSet_iff {g : G} :
    g ∈ H.frobeniusKernelSet ↔
      g = 1 ∨ ∀ x : G, g ∉ H.map (MulAut.conj x).toMonoidHom := by
  constructor
  · intro hg
    rcases eq_or_ne g 1 with rfl | hg1
    · exact Or.inl rfl
    · exact Or.inr fun x hx => hg1 (hg x hx)
  · rintro (rfl | hall)
    · exact fun _ _ => rfl
    · exact fun x hx => absurd hx (hall x)

theorem one_mem_frobeniusKernelSet : (1 : G) ∈ H.frobeniusKernelSet :=
  fun _ _ => rfl

/-- An element of the kernel set lying in `H` is trivial (apply the definition at the
conjugator `1`). -/
theorem eq_one_of_mem_frobeniusKernelSet_of_mem {g : G} (hg : g ∈ H.frobeniusKernelSet)
    (hgH : g ∈ H) : g = 1 :=
  hg 1 (mem_map_conj_iff.mpr (by simpa using hgH))

theorem inv_mem_frobeniusKernelSet {g : G} (hg : g ∈ H.frobeniusKernelSet) :
    g⁻¹ ∈ H.frobeniusKernelSet := by
  intro x hx
  have hginv : g ∈ H.map (MulAut.conj x).toMonoidHom := by
    have := (H.map (MulAut.conj x).toMonoidHom).inv_mem hx
    rwa [inv_inv] at this
  rw [hg x hginv, inv_one]

/-- The kernel set is invariant under conjugation — this is where normality of the kernel
comes from, with no character theory involved. -/
theorem conj_mem_frobeniusKernelSet {g : G} (hg : g ∈ H.frobeniusKernelSet) (y : G) :
    y * g * y⁻¹ ∈ H.frobeniusKernelSet := by
  intro x hx
  have hmem : g ∈ H.map (MulAut.conj (y⁻¹ * x)).toMonoidHom := by
    rw [mem_map_conj_iff] at hx ⊢
    have harg : (y⁻¹ * x)⁻¹ * g * (y⁻¹ * x) = x⁻¹ * (y * g * y⁻¹) * x := by group
    rw [harg]
    exact hx
  rw [hg _ hmem]
  group

/-!
### The conjugate partition: `|frobeniusKernelSet| = [G : H]`

The complement of the kernel set is parametrized by `(G ⧸ H) × H^#`: the coset `⟦x⟧` picks
the conjugate `H^x` (well-defined and injective by malnormality/self-normalization), and the
`H^#`-coordinate the element within it.  This is the cardinality form of MathComp's
`Frobenius_partition` (`G = K ∪ ⋃ (H^x)^#` as a partition). -/

/-- The counting half of the kernel theorem: for malnormal `H` the kernel set has exactly
`H.index` elements.  MathComp: `Frobenius_partition` (approximate: the Coq lemma states the
partition itself; this is the resulting count). -/
theorem card_frobeniusKernelSet [Finite G]
    (hmal : ∀ g ∉ H, H ⊓ H.map (MulAut.conj g).toMonoidHom = ⊥) :
    Nat.card H.frobeniusKernelSet = H.index := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype H := Fintype.ofFinite H
  -- the parametrization of the complement of the kernel set
  have hmem : ∀ (c : G ⧸ H) (h : {h : H // h ≠ 1}),
      Quotient.out c * (h.1 : G) * (Quotient.out c)⁻¹ ∉ H.frobeniusKernelSet := by
    intro c h hker
    have hin : Quotient.out c * (h.1 : G) * (Quotient.out c)⁻¹
        ∈ H.map (MulAut.conj (Quotient.out c)).toMonoidHom :=
      mem_map.mpr ⟨(h.1 : G), h.1.2, rfl⟩
    exact h.2 (Subtype.ext (conj_eq_one_iff.mp (hker _ hin)))
  set f : (G ⧸ H) × {h : H // h ≠ 1} → {g : G // g ∉ H.frobeniusKernelSet} :=
    fun p => ⟨Quotient.out p.1 * (p.2.1 : G) * (Quotient.out p.1)⁻¹, hmem p.1 p.2⟩ with hf
  have hinj : Function.Injective f := by
    rintro ⟨c, h⟩ ⟨d, h'⟩ heq
    have heq' : Quotient.out c * (h.1 : G) * (Quotient.out c)⁻¹
        = Quotient.out d * (h'.1 : G) * (Quotient.out d)⁻¹ := congrArg Subtype.val heq
    have hxH : (Quotient.out d)⁻¹ * Quotient.out c ∈ H := by
      refine mem_of_ne_one_mem_map_conj hmal h'.1.2
        (fun hc => h'.2 (Subtype.ext hc)) (mem_map.mpr ⟨(h.1 : G), h.1.2, ?_⟩)
      change (Quotient.out d)⁻¹ * Quotient.out c * (h.1 : G)
          * ((Quotient.out d)⁻¹ * Quotient.out c)⁻¹ = (h'.1 : G)
      calc (Quotient.out d)⁻¹ * Quotient.out c * (h.1 : G)
            * ((Quotient.out d)⁻¹ * Quotient.out c)⁻¹
          = (Quotient.out d)⁻¹
              * (Quotient.out c * (h.1 : G) * (Quotient.out c)⁻¹) * Quotient.out d := by
            group
        _ = (Quotient.out d)⁻¹
              * (Quotient.out d * (h'.1 : G) * (Quotient.out d)⁻¹) * Quotient.out d := by
            rw [heq']
        _ = (h'.1 : G) := by group
    have hcd : c = d := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d, QuotientGroup.eq]
      have := H.inv_mem hxH
      rwa [mul_inv_rev, inv_inv] at this
    subst hcd
    have hval : (h.1 : G) = (h'.1 : G) := mul_left_cancel (mul_right_cancel heq')
    exact Prod.ext rfl (Subtype.ext (Subtype.ext hval))
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    have hex : ∃ x : G, g ∈ H.map (MulAut.conj x).toMonoidHom ∧ g ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hg hcon
    obtain ⟨x, hgx, hg1⟩ := hex
    set c : G ⧸ H := QuotientGroup.mk x with hc
    have hk : (Quotient.out c)⁻¹ * x ∈ H := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    have hmem' : (Quotient.out c)⁻¹ * g * Quotient.out c ∈ H := by
      have h1 : x⁻¹ * g * x ∈ H := mem_map_conj_iff.mp hgx
      have harg : (Quotient.out c)⁻¹ * g * Quotient.out c
          = ((Quotient.out c)⁻¹ * x) * (x⁻¹ * g * x) * ((Quotient.out c)⁻¹ * x)⁻¹ := by
        group
      rw [harg]
      exact mul_mem (mul_mem hk h1) (inv_mem hk)
    refine ⟨⟨c, ⟨⟨(Quotient.out c)⁻¹ * g * Quotient.out c, hmem'⟩, fun hone => ?_⟩⟩, ?_⟩
    · apply hg1
      have h1 : (Quotient.out c)⁻¹ * g * ((Quotient.out c)⁻¹)⁻¹ = 1 := by
        rw [inv_inv]
        exact congrArg Subtype.val hone
      exact conj_eq_one_iff.mp h1
    · apply Subtype.ext
      change Quotient.out c * ((Quotient.out c)⁻¹ * g * Quotient.out c) * (Quotient.out c)⁻¹ = g
      group
  -- count both sides
  have hcards := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [Nat.card_prod] at hcards
  have hquot : Nat.card (G ⧸ H) = H.index := rfl
  have hsub1 : Nat.card {h : H // h ≠ 1} = Nat.card H - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := H),
      ← Fintype.card_subtype_eq (1 : H)]
    exact Fintype.card_subtype_compl _
  rw [hquot, hsub1] at hcards
  have hsplit : Nat.card {g : G // g ∈ H.frobeniusKernelSet}
      + Nat.card {g : G // g ∉ H.frobeniusKernelSet} = Nat.card G := by
    have hle := Fintype.card_subtype_le (fun g : G => g ∈ H.frobeniusKernelSet)
    have hcompl := Fintype.card_subtype_compl (fun g : G => g ∈ H.frobeniusKernelSet)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := G)]
    omega
  have hkey : H.index * (Nat.card H - 1) + H.index = Nat.card G := by
    have hindex : H.index * Nat.card H = Nat.card G := H.index_mul_card
    obtain ⟨m, hm⟩ : ∃ m, Nat.card H = m + 1 :=
      ⟨Nat.card H - 1, (Nat.succ_pred_eq_of_pos Nat.card_pos).symm⟩
    rw [hm, Nat.mul_succ] at hindex
    rw [hm, Nat.add_sub_cancel]
    exact hindex
  have hSeq : Nat.card H.frobeniusKernelSet
      = Nat.card {g : G // g ∈ H.frobeniusKernelSet} := rfl
  rw [hSeq]
  generalize hP : H.index * (Nat.card H - 1) = P at hcards hkey
  omega

end Subgroup

/-!
### Induced class functions on a malnormal subgroup

The two support computations that drive everything: `ind H φ` vanishes off the conjugates of
`H`, and on `H^#` the averaging sum collapses (by the collapse lemma) to a sum over `H`
itself, i.e. to `φ`. -/

namespace ClassFunction

variable [Fintype G] {H : Subgroup G}

/-- The induced class function vanishes at any element lying outside every conjugate of `H`:
each term of the defining average is an `extendZero` evaluated off `H`. -/
theorem ind_apply_eq_zero_of_forall_notMem (φ : ClassFunction H) {g : G}
    (hg : ∀ x : G, x⁻¹ * g * x ∉ H) : ClassFunction.ind H φ g = 0 := by
  rw [ind_apply, Finset.sum_eq_zero fun x _ => extendZero_apply_of_not_mem φ (hg x), mul_zero]

/-- **Collapse of the induced-character sum on `H^#`** (malnormal case): for `h ∈ H`,
`h ≠ 1`, only conjugators `x ∈ H` contribute to `ind H φ (h)`, and each contributes `φ h`;
the normalization `(#H)⁻¹` then gives `ind H φ h = φ h` exactly. -/
theorem ind_apply_coe_of_malnormal
    (hmal : ∀ g ∉ H, H ⊓ H.map (MulAut.conj g).toMonoidHom = ⊥)
    (φ : ClassFunction H) {h : H} (hh1 : h ≠ 1) :
    ClassFunction.ind H φ (h : G) = φ h := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  have hcoe1 : ((h : G) : G) ≠ 1 := fun hc => hh1 (Subtype.ext hc)
  -- terms with `x ∉ H` vanish
  have hzero : ∀ x : G, x ∉ H → extendZero φ (x⁻¹ * (h : G) * x) = 0 := by
    intro x hx
    refine extendZero_apply_of_not_mem φ fun hmem => ?_
    exact hx (Subgroup.mem_of_ne_one_mem_map_conj hmal h.2 hcoe1
      (Subgroup.mem_map_conj_iff.mpr hmem))
  have hsum : ∑ x : G, extendZero φ (x⁻¹ * (h : G) * x)
      = ∑ x ∈ Finset.univ.filter (· ∈ H), extendZero φ (x⁻¹ * (h : G) * x) :=
    (Finset.sum_subset (Finset.filter_subset _ _) fun x _ hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hzero x hx).symm
  have hbridge : ∑ x ∈ Finset.univ.filter (· ∈ H), extendZero φ (x⁻¹ * (h : G) * x)
      = ∑ x : H, extendZero φ ((x : G)⁻¹ * (h : G) * (x : G)) :=
    Finset.sum_subtype (p := fun x => x ∈ H) (Finset.univ.filter (· ∈ H)) (by simp)
      (fun x => extendZero φ (x⁻¹ * (h : G) * x))
  have hterm : ∀ x : H, extendZero φ ((x : G)⁻¹ * (h : G) * (x : G)) = φ h := by
    intro x
    have hmem : (x : G)⁻¹ * (h : G) * (x : G) ∈ H := mul_mem (mul_mem (inv_mem x.2) h.2) x.2
    rw [extendZero_apply_of_mem φ hmem]
    have hsub : (⟨(x : G)⁻¹ * (h : G) * (x : G), hmem⟩ : H) = x⁻¹ * h * x := rfl
    rw [hsub]
    have := φ.conj_apply h x⁻¹
    rwa [inv_inv] at this
  have hH0 : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [ind_apply, hsum, hbridge, Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hH0, one_mul]

/-- On a malnormal subgroup, `res ∘ ind` is the identity on class functions vanishing at
`1`: the collapse lemma handles `H^#`, and `ind φ 1 = [G:H] · φ 1 = 0` handles the
identity. -/
theorem res_ind_eq_self_of_malnormal
    (hmal : ∀ g ∉ H, H ⊓ H.map (MulAut.conj g).toMonoidHom = ⊥)
    {φ : ClassFunction H} (hφ1 : φ 1 = 0) :
    ClassFunction.res H (ClassFunction.ind H φ) = φ := by
  ext h
  rw [res_apply]
  rcases eq_or_ne h 1 with rfl | hh1
  · rw [OneMemClass.coe_one, ind_apply_one, hφ1, mul_zero]
  · rw [ind_apply_coe_of_malnormal hmal φ hh1]

/-- **The trivial-intersection induction isometry**: on a malnormal subgroup `H`, induction
is an isometry from the class functions of `H` vanishing at `1` (only the *first* argument
needs to vanish): `⟪ind α, ind β⟫_[G] = ⟪α, β⟫_[H]`.  One line from Frobenius reciprocity
once `res (ind α) = α`.  This is the trivial-intersection seed of the Dade isometry —
the future PFsection2 correspondent of MathComp's `normedTI_isometry` (approximate; the Coq
lemma is stated for `normedTI`-configurations). -/
theorem cfInner_ind_ind_of_malnormal [Fintype H]
    (hmal : ∀ g ∉ H, H ⊓ H.map (MulAut.conj g).toMonoidHom = ⊥)
    {α : ClassFunction H} (hα1 : α 1 = 0) (β : ClassFunction H) :
    ⟪ClassFunction.ind H α, ClassFunction.ind H β⟫_[G] = ⟪α, β⟫_[H] := by
  rw [cfInner_ind_right_eq_cfInner_res_left, res_ind_eq_self_of_malnormal hmal hα1]

end ClassFunction

end
