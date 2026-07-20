/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import OddOrder.Mathlib.GroupTheory.FrobeniusKernel
import OddOrder.Mathlib.RepresentationTheory.CharacterTransfer
import OddOrder.Mathlib.RepresentationTheory.VirtualChar

/-!
# Peterfalvi, Section 2: the Dade isometry

This is the port of `PFsection2.v` — the construction and basic theory of the **Dade
isometry**, the central tool of the character-theoretic half of the odd-order proof.
All results live in `namespace PF2`; each carries its Peterfalvi number and Coq name.

Given the Dade hypothesis for `(G, L, A)` — `A` a normal TI-like subset of a subgroup `L`
of `G` with coprime normal complements ("signalizers") `H a` to `C_L(a)` in `C_G(a)` — the
linear lift `τ = PF2.DadeHypothesis.dade` sends class functions of `L` supported on `A` to
class functions of `G`; it is an isometry (`dade_isometry`, 2.6(a)) mapping virtual
characters supported on `A` to virtual characters of `G` vanishing at `1`
(`dade_isVirtualChar`, 2.6(b); summary `dade_Zisometry`).

## Main definitions

* `PF2.IsNormedTI A L`: normed trivial-intersection subset (`g A g⁻¹` meets `A` iff
  `g ∈ L`, with `L = N_G(A)`).  MathComp: `normedTI A G L` (via the `normedTI_memJ_P`
  characterization; the ambient MathComp `G` is the whole group here).
* `PF2.DadeHypothesis G L A`: Peterfalvi Definition (2.2), as a structure carrying the
  signalizer functor `a ↦ H a` as *data* together with its defining properties (the survey
  recommendation, replacing the Coq's `[pick]`/`locked_with` canonical-`pcore` packaging).
  Any two instances agree on `A` (`signalizer_eq_of`, Coq `def_Dade_signalizer`), so the
  data is unique where it matters.  Coq: `Dade_hypothesis` + `Dade_signalizer` +
  `is_Dade_signalizer`.
* `PF2.DadeHypothesis.support1 a`: the class support of the coset `H a * a` — the set of
  elements identified with `a` by the Dade isometry.  Coq: `Dade_support1`.
* `PF2.DadeHypothesis.support`: the natural support of the isometry.  Coq: `Dade_support`.
* `PF2.DadeHypothesis.dade : ClassFunction ↥L →ₗ[ℂ] ClassFunction G`: Peterfalvi
  Definition (2.5), the lift `α^τ` (piecewise, via the class-support partition; total on
  `ClassFunction ↥L`, as in the Coq).  Coq: `Dade`.

## Main results

* `PF2.exists_pow_eq_coprime_mul` + `PF2.mem_centralizer_of_conj_mul_mem` +
  `PF2.exists_conj_mul_of_mul_inv_mem` — the (2.1) engine (`partition_cent_rcoset`): the
  `H`-conjugates of `C_H(g) * g` cover `H * g`, and the associated trivial-intersection
  facts, all driven by a Chinese-remainder exponent `k` with `u ^ k = g` for every `u` in
  the coset (replacing MathComp's `π`-part machinery `u.`_π`).
* `PF2.DadeHypothesis.dade_apply_of_mem_support1` (`DadeE`) and the (2.4) support kit
  (`support1_conj`, `exists_conj_of_mem_support1`, `mem_centralizer_of_conj_rcoset`).
* `PF2.DadeHypothesis.general_dade_reciprocity` (2.7) / `dade_reciprocity` /
  `dade_isometry` (2.6(a)).
* `PF2.DadeHypothesis.dade_expansion` (2.10) — `α^τ` as an alternating sum of induced
  class functions over a transversal of the `L`-orbits of nonempty subsets of `A` —
  and its consequence `dade_isVirtualChar` (2.6(b)), summarized in `dade_Zisometry`.
* `PF2.DadeHypothesis.restrict` (2.11): restriction of the Dade hypothesis and isometry
  to an `L`-stable subset `A₁ ⊆ A` (Coq `restr_Dade_hyp`, `restr_DadeE`).
* `PF2.DadeHypothesis.ofIsNormedTI` (the existence part of (2.3), Coq `normedTI_Dade`),
  `dade_eq_ind` (Coq `Dade_Ind`), `normedTI_isometry` (Isaacs, Lemma 7.7): in the
  trivial-signalizer case the Dade lift *is* ordinary induction, so induction from a
  normed TI-subset is an isometry.  The malnormal-subgroup case `A = H \ {1}` (bridge
  `PF2.isNormedTI_sdiff_one_of_malnormal`) recovers the seed isometry
  `ClassFunction.cfInner_ind_ind_of_malnormal` (`FrobeniusKernel.lean`); see
  `PF2.normedTI_isometry_of_malnormal`.

## Conventions and deviations from the Coq

* `G` is the ambient group (MathComp's `{group gT}` `G` becomes the ambient type);
  `L : Subgroup G`; `A : Set G` with `A ⊆ ↑L`.  `'CF(L, A)` is
  `ClassFunction.supportedOn ↥L (((↑) : ↥L → G) ⁻¹' A)`.
* `'C_G[a]` is `Subgroup.centralizer {a}`; `'C_L[a]` is `L ⊓ Subgroup.centralizer {a}`.
* Conjugation is spelled `x * a * x⁻¹` (project convention, `MulAut.conj`); MathComp's
  `a ^ x` is `x⁻¹ * a * x`, so fusion/orbit statements are transposed accordingly.
* The Coq derives the signalizer canonically as `'O_pi^'('C_G[a])` and its properties
  (`DadeJ`, `Dade_setU1`) from `pi`-core/Hall theory; here the signalizer is structure
  data, and the same properties follow from the *uniqueness* of coprime normal complements
  (`mem_signalizer_of_coprime`, a quotient-order argument replacing `sub_normal_Hall`).
* `Dade_transversal` (a fixed choice of representatives of the `L`-orbits of nonempty
  subsets of `A`) is replaced by the predicate `PF2.DadeHypothesis.IsSetTransversal` plus
  an existence lemma; `dade_expansion` (2.10) is stated for an arbitrary transversal.
  (The Coq transversal is used only inside `PFsection2.v` itself, to derive `Dade_vchar`.)
* Peterfalvi (2.1) `partition_cent_rcoset` is restated as its consumed consequences
  (cover, trivial intersection, block counting) rather than as a `partition` object.
-/

noncomputable section

open Finset
open scoped ClassFunction

universe u

namespace PF2

variable {G : Type u} [Group G]

/-! ### The Chinese-remainder exponent engine

MathComp proves the trivial-intersection facts of (2.1)/(2.4) by observing that every
element `u = x * g` of a coset `H * g` (with `x ∈ H` commuting with `g`, `|H|` coprime to
the order of `g`) has `π`-part `g`, for `π` the primes of the order of `g`.  The same
canonicity is obtained here from a single exponent: `k ≡ 0 mod n₁` and `k ≡ 1 mod n₂`
give `(x * g) ^ k = g` for all commuting `x, g` with `orderOf x ∣ n₁`, `orderOf g ∣ n₂`.
Since `u ↦ u ^ k` is conjugation-equivariant, conjugations moving such cosets into each
other must move the distinguished elements into each other. -/

/-- The **coprime-exponent engine**: for coprime `n₁ n₂` there is a single exponent `k`
with `(x * y) ^ k = y` whenever `x` and `y` commute, `orderOf x ∣ n₁` and `orderOf y ∣ n₂`.
MathComp: the `u.`_π = g` computations of `PFsection2.v` (2.1)/(2.4) (`consttM`,
`constt_p_elt`, `constt1P`). -/
theorem exists_pow_eq_coprime_mul {n₁ n₂ : ℕ} (h : Nat.Coprime n₁ n₂) :
    ∃ k : ℕ, ∀ x y : G, Commute x y → orderOf x ∣ n₁ → orderOf y ∣ n₂ → (x * y) ^ k = y := by
  obtain ⟨k, hk₁, hk₂⟩ := Nat.chineseRemainder h 0 1
  refine ⟨k, fun x y hxy hx hy => ?_⟩
  have hxk : x ^ k = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hx.trans (Nat.modEq_zero_iff_dvd.mp hk₁))
  have hyk : y ^ k = y ^ 1 := pow_eq_pow_iff_modEq.mpr (hk₂.of_dvd hy)
  rw [hxy.mul_pow, hxk, one_mul, hyk, pow_one]

/-- Conjugation commutes with powers: `(w * u * w⁻¹) ^ k = w * u ^ k * w⁻¹`. -/
private theorem conj_pow_eq (w u : G) (k : ℕ) : (w * u * w⁻¹) ^ k = w * u ^ k * w⁻¹ := by
  rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]

/-- Conjugation preserves element orders. -/
private theorem orderOf_conj_eq (x w : G) : orderOf (x⁻¹ * w * x) = orderOf w := by
  have h := orderOf_injective (MulAut.conj x⁻¹).toMonoidHom
    (MulAut.conj x⁻¹).injective w
  have harg : (MulAut.conj x⁻¹).toMonoidHom w = x⁻¹ * w * x := by
    show (MulAut.conj x⁻¹) w = _
    rw [MulAut.conj_apply]
    group
  rwa [harg] at h

/-- **Trivial-intersection collapse for centralizer cosets** (the engine behind Peterfalvi
(2.1) and the strengthened (2.4)(c)): if `u` and `w * u * w⁻¹` both lie in the coset
`(H ⊓ C_G(g)) * g` and `|H|` is coprime to the order of `g`, then `w` centralizes `g`.
MathComp: the `normedTI Cg H C` step of `partition_cent_rcoset` (`PFsection2.v` (2.1)). -/
theorem mem_centralizer_of_conj_mul_mem [Finite G] {H : Subgroup G} {g : G}
    (hco : Nat.Coprime (Nat.card H) (orderOf g)) {u w : G}
    (hu : u * g⁻¹ ∈ H ⊓ Subgroup.centralizer {g})
    (hu' : (w * u * w⁻¹) * g⁻¹ ∈ H ⊓ Subgroup.centralizer {g}) :
    w ∈ Subgroup.centralizer {g} := by
  obtain ⟨k, hk⟩ := exists_pow_eq_coprime_mul (G := G) hco
  have key : ∀ v : G, v * g⁻¹ ∈ H ⊓ Subgroup.centralizer {g} → v ^ k = g := by
    intro v hv
    have hcomm : Commute (v * g⁻¹) g := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hv).2
      exact this
    have horder : orderOf (v * g⁻¹) ∣ Nat.card H :=
      Subgroup.orderOf_dvd_natCard H (Subgroup.mem_inf.mp hv).1
    have := hk (v * g⁻¹) g hcomm horder dvd_rfl
    rwa [inv_mul_cancel_right] at this
  have h2 : w * g * w⁻¹ = g := by
    calc w * g * w⁻¹ = w * u ^ k * w⁻¹ := by rw [key u hu]
      _ = (w * u * w⁻¹) ^ k := (conj_pow_eq w u k).symm
      _ = g := key _ hu'
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc w * g = w * g * w⁻¹ * w := by group
    _ = g * w := by rw [h2]

/-- **Cover half of Peterfalvi (2.1)** (`partition_cent_rcoset`): if `g` normalizes a
finite subgroup `H` of order coprime to the order of `g`, then every element of the coset
`H * g` is an `H`-conjugate of an element of `(H ⊓ C_G(g)) * g`.  Proved by counting: the
parametrization `((y : H⧸C), c) ↦ y * (c * g) * y⁻¹` is injective into `H * g` by the
trivial-intersection collapse (`mem_centralizer_of_conj_mul_mem`), and its domain has full
cardinality `|H|`. -/
theorem exists_conj_mul_of_mul_inv_mem [Finite G] {H : Subgroup G} {g : G}
    (hnorm : ∀ h ∈ H, g * h * g⁻¹ ∈ H) (hco : Nat.Coprime (Nat.card H) (orderOf g))
    {u : G} (hu : u * g⁻¹ ∈ H) :
    ∃ y ∈ H, ∃ c ∈ H ⊓ Subgroup.centralizer {g}, y * (c * g) * y⁻¹ = u := by
  classical
  set C : Subgroup G := H ⊓ Subgroup.centralizer {g} with hCdef
  set C' : Subgroup ↥H := C.subgroupOf H with hC'def
  -- the parametrized conjugation map, injective by the trivial-intersection collapse
  have hΦmem : ∀ (q : ↥H ⧸ C') (c : ↥C),
      ((Quotient.out q : ↥H) : G) * (↑c * g) * ((Quotient.out q : ↥H) : G)⁻¹ * g⁻¹ ∈ H := by
    intro q c
    have hy := (Quotient.out q).2
    have hc : (↑c : G) ∈ H := (Subgroup.mem_inf.mp c.2).1
    have hcalc : ((Quotient.out q : ↥H) : G) * (↑c * g) * ((Quotient.out q : ↥H) : G)⁻¹ * g⁻¹
        = ((Quotient.out q : ↥H) : G) * ↑c
          * (g * ((Quotient.out q : ↥H) : G)⁻¹ * g⁻¹) := by group
    rw [hcalc]
    exact mul_mem (mul_mem hy hc) (hnorm _ (inv_mem hy))
  set Φ : (↥H ⧸ C') × ↥C → {v : G // v * g⁻¹ ∈ H} := fun p =>
    ⟨((Quotient.out p.1 : ↥H) : G) * (↑p.2 * g) * ((Quotient.out p.1 : ↥H) : G)⁻¹,
      hΦmem p.1 p.2⟩ with hΦdef
  have hΦinj : Function.Injective Φ := by
    rintro ⟨q₁, c₁⟩ ⟨q₂, c₂⟩ heq
    set y₁ : ↥H := Quotient.out q₁ with hy₁def
    set y₂ : ↥H := Quotient.out q₂ with hy₂def
    have heq' : (y₁ : G) * (↑c₁ * g) * (y₁ : G)⁻¹ = (y₂ : G) * (↑c₂ * g) * (y₂ : G)⁻¹ :=
      congrArg Subtype.val heq
    set w : G := (y₂ : G)⁻¹ * ↑y₁ with hwdef
    have hconj : w * (↑c₁ * g) * w⁻¹ = ↑c₂ * g := by
      calc w * (↑c₁ * g) * w⁻¹
          = (y₂ : G)⁻¹ * ((y₁ : G) * (↑c₁ * g) * (y₁ : G)⁻¹) * ↑y₂ := by
            rw [hwdef]; group
        _ = (y₂ : G)⁻¹ * ((y₂ : G) * (↑c₂ * g) * (y₂ : G)⁻¹) * ↑y₂ := by rw [heq']
        _ = ↑c₂ * g := by group
    have hcancel : ∀ c : ↥C, (↑c * g) * g⁻¹ ∈ C := fun c => by
      rw [mul_inv_cancel_right]; exact c.2
    have hwcent : w ∈ Subgroup.centralizer {g} := by
      refine mem_centralizer_of_conj_mul_mem (H := H) hco (u := ↑c₁ * g) (hcancel c₁) ?_
      rw [hconj]; exact hcancel c₂
    have hwH : w ∈ H := mul_mem (inv_mem y₂.2) y₁.2
    have hq : q₁ = q₂ := by
      have hmem : y₂⁻¹ * y₁ ∈ C' := by
        rw [hC'def, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_inf.mpr ⟨hwH, hwcent⟩
      calc q₁ = ↑y₁ := (QuotientGroup.out_eq' q₁).symm
        _ = ↑y₂ := ((QuotientGroup.eq (s := C')).mpr hmem).symm
        _ = q₂ := QuotientGroup.out_eq' q₂
    have hy : y₁ = y₂ := by rw [hy₁def, hy₂def, hq]
    have hc : (c₁ : G) = c₂ := by
      rw [hy] at heq'
      exact mul_right_cancel (mul_left_cancel (mul_right_cancel heq'))
    exact Prod.ext hq (Subtype.ext hc)
  -- cardinalities: the domain and codomain both have `|H|` elements
  have hcardC : Nat.card C' = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcard_dom : Nat.card ((↥H ⧸ C') × ↥C) = Nat.card ↥H := by
    rw [Nat.card_prod, ← hcardC]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup C').symm
  have hcard_cod : Nat.card {v : G // v * g⁻¹ ∈ H} = Nat.card ↥H := by
    refine Nat.card_congr ⟨fun v => ⟨(v : G) * g⁻¹, v.2⟩,
      fun h => ⟨(h : G) * g, by simp⟩, fun v => ?_, fun h => ?_⟩
    · ext; simp
    · ext; simp
  -- an injective map between finite types of equal cardinality is surjective
  have hΦbij : Function.Bijective Φ := by
    haveI : Finite (↥H ⧸ C') := Quotient.finite _
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨hΦinj, by rw [hcard_dom, hcard_cod]⟩
  obtain ⟨⟨q, c⟩, hqc⟩ := hΦbij.2 ⟨u, hu⟩
  refine ⟨↑(Quotient.out q), (Quotient.out q).2, ↑c, c.2, ?_⟩
  exact congrArg Subtype.val hqc

/-! ### The normed trivial-intersection predicate

MathComp: `normedTI A G L` (`frobenius.v`), through its `normedTI_memJ_P`
characterization — the ambient MathComp group `G` is the whole ambient type here.
The subset ↔ subgroup bridge: for a nontrivial subgroup `H`, malnormality of `H`
(`FrobeniusKernel.lean`'s spelling `∀ g ∉ H, H ⊓ H^g = ⊥`) is exactly
`IsNormedTI (↑H \ {1}) H`. -/

/-- `A` is a **normed trivial-intersection subset** with normalizer `L`: `A` is nonempty
and, for `a ∈ A`, the conjugate `g * a * g⁻¹` lies back in `A` exactly when `g ∈ L`.
Consequently distinct `G`-conjugates of `A` are disjoint and `L = N_G(A)`.
MathComp: `normedTI A G L` via `normedTI_memJ_P` (`frobenius.v`). -/
structure IsNormedTI (A : Set G) (L : Subgroup G) : Prop where
  nonempty : A.Nonempty
  conj_mem_iff : ∀ ⦃a⦄, a ∈ A → ∀ g : G, g * a * g⁻¹ ∈ A ↔ g ∈ L

namespace IsNormedTI

variable {A : Set G} {L : Subgroup G}

/-- A normed TI-subset is contained in its normalizer.  MathComp: the `A ⊆ L` step of
`normedTI_Dade` (`PFsection2.v`). -/
theorem subset (h : IsNormedTI A L) : A ⊆ ↑L := fun a ha => by
  have := (h.conj_mem_iff ha a).mp (by simpa using ha)
  exact this

/-- Conjugation by elements of `L` preserves a normed TI-subset. -/
theorem conj_mem (h : IsNormedTI A L) {x : G} (hx : x ∈ L) {a : G} (ha : a ∈ A) :
    x * a * x⁻¹ ∈ A :=
  (h.conj_mem_iff ha x).mpr hx

end IsNormedTI

/-- **Malnormality gives a normed TI-subset**: for a nontrivial malnormal subgroup `H`,
the set `H \ {1}` is a normed TI-subset with normalizer `H`.  This is the subset ↔
subgroup bridge between `FrobeniusKernel.lean`'s malnormality spelling and `PFsection2`'s
`normedTI`.  MathComp: `Frobenius_normedTI`-adjacent (`frobenius.v`; exact name
unconfirmed, MathComp proper not in this checkout). -/
theorem isNormedTI_sdiff_one_of_malnormal {H : Subgroup G} (hbot : H ≠ ⊥)
    (hmal : ∀ g ∉ H, H ⊓ H.map (MulAut.conj g).toMonoidHom = ⊥) :
    IsNormedTI ((H : Set G) \ {1}) H := by
  constructor
  · obtain ⟨h, hh, hne⟩ := H.bot_or_exists_ne_one.resolve_left hbot
    exact ⟨h, hh, by simpa using hne⟩
  · rintro a ⟨haH, ha1⟩ g
    rw [Set.mem_singleton_iff] at ha1
    constructor
    · rintro ⟨hgH, -⟩
      by_contra hg
      have hmem : g * a * g⁻¹ ∈ H ⊓ H.map (MulAut.conj g).toMonoidHom := by
        refine Subgroup.mem_inf.mpr ⟨hgH, ?_⟩
        rw [Subgroup.mem_map_conj_iff]
        have harg : g⁻¹ * (g * a * g⁻¹) * g = a := by group
        rw [harg]
        exact haH
      rw [hmal g hg, Subgroup.mem_bot] at hmem
      exact ha1 (by
        have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
        rw [this, hmem]; group)
    · intro hg
      refine ⟨mul_mem (mul_mem hg haH) (inv_mem hg), ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hone
      exact ha1 (by
        have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
        rw [this, hone]; group)

/-- **A normed TI-subset `H \ {1}` makes `H` malnormal** — the converse bridge. -/
theorem malnormal_of_isNormedTI_sdiff_one {H : Subgroup G}
    (h : IsNormedTI ((H : Set G) \ {1}) H) :
    ∀ g ∉ H, H ⊓ H.map (MulAut.conj g).toMonoidHom = ⊥ := by
  intro g hg
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH, hxconj⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  rw [Subgroup.mem_map_conj_iff] at hxconj
  have hmem : g⁻¹ * x * g ∈ (H : Set G) \ {1} := by
    refine ⟨hxconj, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hone
    exact hx1 (by
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [this, hone]; group)
  have := (h.conj_mem_iff hmem g).mp (by
    have harg : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [harg]
    exact ⟨hxH, by simpa using hx1⟩)
  exact hg this

/-! ### (2.2) The Dade hypothesis -/

/-- **The Dade hypothesis** for `(G, L, A)` — Peterfalvi Definition (2.2), Coq
`Dade_hypothesis G L A` (`PFsection2.v`).  `A` is a normal subset of `L` not containing
`1` whose `G`-fusion is controlled by `L`, equipped with a **signalizer functor**
`a ↦ signalizer a` satisfying `C_G(a) = H a ⋊ C_L(a)` (Coq `is_Dade_signalizer`, split
here into the fields `signalizer_le`, `signalizer_conj_mem` (normality in `C_G(a)`) and
`signalizer_mul` (the product decomposition; the intersection is trivial by coprimality))
and the coprimality condition `(|H a|, |C_L(b)|) = 1` for all `a, b ∈ A`.

The signalizer is carried as *data* (the survey recommendation), unlike the Coq, which
stores an existential and reconstructs the canonical signalizer `'O_pi^'('C_G[a])` via
`locked_with`.  No generality is lost: any two signalizer functors agree on `A`
(`PF2.DadeHypothesis.signalizer_eq_of`, Coq `def_Dade_signalizer`), because a coprime
normal complement is unique.  Values off `A` are junk and never used. -/
structure DadeHypothesis (G : Type u) [Group G] (L : Subgroup G) (A : Set G) where
  /-- `A ⊆ L` (half of `A <| L`). -/
  subset : A ⊆ ↑L
  /-- `1 ∉ A`. -/
  one_notMem : (1 : G) ∉ A
  /-- `A` is `L`-conjugation-stable (the other half of `A <| L`). -/
  conj_mem : ∀ x ∈ L, ∀ a ∈ A, x * a * x⁻¹ ∈ A
  /-- (2.2)(a): `L` controls the `G`-fusion of `A` — `G`-conjugate elements of `A` are
  already `L`-conjugate. -/
  fusion : ∀ a ∈ A, ∀ b ∈ A, IsConj a b → ∃ x ∈ L, x * a * x⁻¹ = b
  /-- The signalizer functor `a ↦ H a` (Coq `Dade_signalizer`; usually denoted `H a`).
  Only the values on `A` matter. -/
  signalizer : G → Subgroup G
  /-- `H a ≤ C_G(a)`. -/
  signalizer_le : ∀ a ∈ A, signalizer a ≤ Subgroup.centralizer {a}
  /-- `H a` is normal in `C_G(a)` (part of `H a ⋊ C_L(a) = C_G(a)`). -/
  signalizer_conj_mem : ∀ a ∈ A, ∀ g ∈ Subgroup.centralizer {a},
    ∀ x ∈ signalizer a, g * x * g⁻¹ ∈ signalizer a
  /-- `C_G(a) = H a * C_L(a)` (part of `H a ⋊ C_L(a) = C_G(a)`; the intersection is
  trivial by `signalizer_coprime`). -/
  signalizer_mul : ∀ a ∈ A, ∀ u ∈ Subgroup.centralizer {a},
    ∃ x ∈ signalizer a, ∃ c ∈ L ⊓ Subgroup.centralizer {a}, u = x * c
  /-- (2.2)(c): `|H a|` is coprime to `|C_L(b)|` for **all** `a, b ∈ A` (the two-variable
  quantification is essential: it makes the signalizers "π′-groups" for a set of primes
  π depending only on `(L, A)`). -/
  signalizer_coprime : ∀ a ∈ A, ∀ b ∈ A,
    Nat.Coprime (Nat.card (signalizer a)) (Nat.card ↥(L ⊓ Subgroup.centralizer {b}))

namespace DadeHypothesis

variable {L : Subgroup G} {A : Set G}

/-- Members of `A` are members of `L` (coercion form used to evaluate class functions of
`L` at elements of `A`). -/
theorem mem_of_mem_set (ddA : DadeHypothesis G L A) {a : G} (ha : a ∈ A) : a ∈ L :=
  ddA.subset ha

/-- `a ∈ C_L(a)` for `a ∈ A`. -/
theorem mem_inf_centralizer_self (ddA : DadeHypothesis G L A) {a : G} (ha : a ∈ A) :
    a ∈ L ⊓ Subgroup.centralizer {a} :=
  Subgroup.mem_inf.mpr ⟨ddA.mem_of_mem_set ha, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

/-- The order of `a ∈ A` divides `|C_L(a)|`. -/
theorem orderOf_dvd_card (ddA : DadeHypothesis G L A) {a : G} (ha : a ∈ A) :
    orderOf a ∣ Nat.card ↥(L ⊓ Subgroup.centralizer {a}) :=
  Subgroup.orderOf_dvd_natCard _ (ddA.mem_inf_centralizer_self ha)

/-- `|H a|` is coprime to the order of any `b ∈ A`. -/
theorem coprime_card_signalizer_orderOf (ddA : DadeHypothesis G L A) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) :
    Nat.Coprime (Nat.card (ddA.signalizer a)) (orderOf b) :=
  Nat.Coprime.coprime_dvd_right (ddA.orderOf_dvd_card hb) (ddA.signalizer_coprime a ha b hb)

/-- `H a ⊓ C_L(a) = ⊥` — the trivial-intersection half of the semidirect decomposition,
from coprimality.  MathComp: extracted from `sdprodP` of `Dade_sdprod`. -/
theorem signalizer_inf_eq_bot (ddA : DadeHypothesis G L A) {a : G} (ha : a ∈ A) :
    ddA.signalizer a ⊓ (L ⊓ Subgroup.centralizer {a}) = ⊥ :=
  disjoint_iff.mp
    (Subgroup.disjoint_of_coprime_natCard (ddA.signalizer_coprime a ha a ha))

/-! #### The semidirect decomposition `C_G(a) = H a ⋊ C_L(a)` inside the centralizer

Realized as an `IsComplement'` between the `subgroupOf`-images inside `↥(C_G(a))`, with
`H a` normal — the form Mathlib's `IsComplement'.QuotientMulEquiv` consumes.
MathComp: `Dade_sdprod` (`PFsection2.v`). -/

open scoped Pointwise in
/-- `C_L(a)` and `H a` are complements inside `C_G(a)` (in the `c * x` order matching
`IsComplement'.QuotientMulEquiv`'s `G ⧸ K ≃* H` with `K` normal).
MathComp: `Dade_sdprod` (`PFsection2.v`). -/
theorem isComplement'_subgroupOf (ddA : DadeHypothesis G L A) {a : G} (ha : a ∈ A) :
    ((L ⊓ Subgroup.centralizer {a}).subgroupOf
        (Subgroup.centralizer {a})).IsComplement'
      ((ddA.signalizer a).subgroupOf (Subgroup.centralizer {a})) := by
  set C : Subgroup G := Subgroup.centralizer {a}
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · -- disjointness, from coprimality of the cardinalities
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [Subgroup.card_subgroupOf inf_le_right,
      Subgroup.card_subgroupOf (ddA.signalizer_le a ha)]
    exact (ddA.signalizer_coprime a ha a ha).symm
  · -- the product decomposition, from `signalizer_mul` (reordered by normality)
    refine Set.eq_univ_iff_forall.mpr fun u => ?_
    obtain ⟨x, hx, c, hc, hu⟩ := ddA.signalizer_mul a ha ↑u u.2
    have hcC : c ∈ C := (Subgroup.mem_inf.mp hc).2
    have hxC : x ∈ C := ddA.signalizer_le a ha hx
    have hx' : c⁻¹ * x * c ∈ ddA.signalizer a := by
      have := ddA.signalizer_conj_mem a ha c⁻¹ (inv_mem hcC) x hx
      simpa using this
    refine Set.mem_mul.mpr ⟨⟨c, hcC⟩, ?_, ⟨c⁻¹ * x * c, mul_mem (mul_mem (inv_mem hcC) hxC) hcC⟩,
      ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact hc
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact hx'
    · ext
      push_cast
      rw [hu]
      group

/-- `H a` (viewed inside `C_G(a)`) is normal there — the normality half of
`Dade_sdprod`. -/
theorem normal_signalizer_subgroupOf (ddA : DadeHypothesis G L A) {a : G} (ha : a ∈ A) :
    ((ddA.signalizer a).subgroupOf (Subgroup.centralizer {a})).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  push_cast
  exact ddA.signalizer_conj_mem a ha ↑g g.2 ↑n hn

/-- `|C_G(a)| = |H a| * |C_L(a)|` — the order decomposition of `Dade_sdprod`. -/
theorem card_signalizer_mul_card (ddA : DadeHypothesis G L A) {a : G} (ha : a ∈ A) :
    Nat.card (ddA.signalizer a) * Nat.card ↥(L ⊓ Subgroup.centralizer {a})
      = Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  have h := (ddA.isComplement'_subgroupOf ha).card_mul
  rw [Subgroup.card_subgroupOf inf_le_right,
    Subgroup.card_subgroupOf (ddA.signalizer_le a ha)] at h
  rw [mul_comm]
  exact h

/-- **The Hall-containment engine**: any element of `C_G(a)` whose order is coprime to
`|C_L(a)|` lies in the signalizer `H a`.  This is the uniqueness mechanism replacing
MathComp's `sub_normal_Hall`/`pcore` canonicity: the image of such an element in
`C_G(a) ⧸ H a ≃ C_L(a)` has order dividing two coprime numbers.  Everything the Coq
derives from the canonical choice `H a = 'O_pi^'('C_G[a])` (`def_Dade_signalizer`,
`DadeJ`, `Dade_setU1`) flows from this lemma. -/
theorem mem_signalizer_of_coprime [Finite G] (ddA : DadeHypothesis G L A) {a : G}
    (ha : a ∈ A) {u : G} (hu : u ∈ Subgroup.centralizer {a})
    (hco : Nat.Coprime (orderOf u) (Nat.card ↥(L ⊓ Subgroup.centralizer {a}))) :
    u ∈ ddA.signalizer a := by
  set C : Subgroup G := Subgroup.centralizer {a} with hCdef
  set Ha' : Subgroup ↥C := (ddA.signalizer a).subgroupOf C with hHa'def
  haveI : Ha'.Normal := ddA.normal_signalizer_subgroupOf ha
  set uC : ↥C := ⟨u, hu⟩ with huCdef
  -- the order of the image of `u` in the quotient divides `orderOf u` …
  have h1 : orderOf ((QuotientGroup.mk' Ha') uC) ∣ orderOf u := by
    have h1a : orderOf ((QuotientGroup.mk' Ha') uC) ∣ orderOf uC :=
      orderOf_map_dvd (QuotientGroup.mk' Ha') uC
    have h1b : orderOf uC = orderOf u :=
      (orderOf_injective C.subtype (Subgroup.subtype_injective C) uC).symm
    rwa [h1b] at h1a
  -- … and divides the order of the quotient, which is `|C_L(a)|`
  have hcardQ : Nat.card (↥C ⧸ Ha') = Nat.card ↥(L ⊓ Subgroup.centralizer {a}) := by
    have := Nat.card_congr ((ddA.isComplement'_subgroupOf ha).QuotientMulEquiv).toEquiv
    rw [this, Subgroup.card_subgroupOf inf_le_right]
  have h2 : orderOf ((QuotientGroup.mk' Ha') uC) ∣ Nat.card (↥C ⧸ Ha') :=
    orderOf_dvd_natCard _
  rw [hcardQ] at h2
  -- coprimality forces the image to be trivial
  have h3 : orderOf ((QuotientGroup.mk' Ha') uC) = 1 :=
    Nat.eq_one_of_dvd_coprimes hco h1 h2
  have h4 : uC ∈ Ha' := by
    rw [← QuotientGroup.eq_one_iff]
    exact orderOf_eq_one_iff.mp h3
  rwa [hHa'def, Subgroup.mem_subgroupOf] at h4

/-- **Uniqueness of the signalizer** (`def_Dade_signalizer`): any two Dade-hypothesis
structures on the same `(G, L, A)` have the same signalizers on `A`.  Mutual containment,
each direction by the other structure's Hall-containment property.  This is the
proof-irrelevance surrogate justifying carrying the signalizer as data. -/
theorem signalizer_eq_of [Finite G] (ddA ddA' : DadeHypothesis G L A) {a : G} (ha : a ∈ A) :
    ddA.signalizer a = ddA'.signalizer a := by
  have key : ∀ dd₁ dd₂ : DadeHypothesis G L A, dd₁.signalizer a ≤ dd₂.signalizer a := by
    intro dd₁ dd₂ x hx
    refine dd₂.mem_signalizer_of_coprime ha (dd₁.signalizer_le a ha hx) ?_
    exact Nat.Coprime.coprime_dvd_left
      (Subgroup.orderOf_dvd_natCard _ hx) (dd₁.signalizer_coprime a ha a ha)
  exact le_antisymm (key ddA ddA') (key ddA' ddA)

/-- Conjugation transport for singleton centralizers:
`w ∈ C_G(x a x⁻¹) ↔ x⁻¹ w x ∈ C_G(a)`. -/
private theorem mem_centralizer_conj_iff {a x w : G} :
    w ∈ Subgroup.centralizer {x * a * x⁻¹} ↔ x⁻¹ * w * x ∈ Subgroup.centralizer {a} := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : x⁻¹ * (w * (x * a * x⁻¹)) * x = x⁻¹ * ((x * a * x⁻¹) * w) * x :=
      congrArg (fun t => x⁻¹ * t * x) h
    calc x⁻¹ * w * x * a = x⁻¹ * (w * (x * a * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * a * x⁻¹) * w) * x := h'
      _ = a * (x⁻¹ * w * x) := by group
  · intro h
    have h' : x * (x⁻¹ * w * x * a) * x⁻¹ = x * (a * (x⁻¹ * w * x)) * x⁻¹ :=
      congrArg (fun t => x * t * x⁻¹) h
    calc w * (x * a * x⁻¹) = x * (x⁻¹ * w * x * a) * x⁻¹ := by group
      _ = x * (a * (x⁻¹ * w * x)) * x⁻¹ := h'
      _ = (x * a * x⁻¹) * w := by group

/-- **Peterfalvi (2.4)(a)** (`DadeJ`): the signalizer functor is `L`-equivariant,
`H (x a x⁻¹) = x (H a) x⁻¹` for `x ∈ L`, `a ∈ A`.  Both containments are instances of
the Hall-containment property `mem_signalizer_of_coprime` (in the Coq this is the
`pcoreJ` equivariance of the canonical `pcore` choice). -/
theorem signalizer_conj [Finite G] (ddA : DadeHypothesis G L A) {x : G} (hx : x ∈ L)
    {a : G} (ha : a ∈ A) :
    ddA.signalizer (x * a * x⁻¹)
      = (ddA.signalizer a).map (MulAut.conj x).toMonoidHom := by
  have hax : x * a * x⁻¹ ∈ A := ddA.conj_mem x hx a ha
  apply le_antisymm
  · intro w hw
    rw [Subgroup.mem_map_conj_iff]
    refine ddA.mem_signalizer_of_coprime ha ?_ ?_
    · exact mem_centralizer_conj_iff.mp (ddA.signalizer_le _ hax hw)
    · rw [orderOf_conj_eq]
      exact Nat.Coprime.coprime_dvd_left
        (Subgroup.orderOf_dvd_natCard _ hw) (ddA.signalizer_coprime _ hax a ha)
  · intro w hw
    rw [Subgroup.mem_map_conj_iff] at hw
    refine ddA.mem_signalizer_of_coprime hax ?_ ?_
    · rw [mem_centralizer_conj_iff]
      exact ddA.signalizer_le a ha hw
    · rw [← orderOf_conj_eq x w]
      exact Nat.Coprime.coprime_dvd_left
        (Subgroup.orderOf_dvd_natCard _ hw) (ddA.signalizer_coprime a ha _ hax)

/-! ### (2.4) The Dade support sets -/

/-- **The local Dade support** `support1 a` — the `G`-class support of the coset
`(H a) * a`: all conjugates of elements `x * a`, `x ∈ H a`.  These are the elements the
Dade isometry identifies with `a`.  Coq: `Dade_support1` (`dd1`), `PFsection2.v`. -/
def support1 (ddA : DadeHypothesis G L A) (a : G) : Set G :=
  {u | ∃ x ∈ ddA.signalizer a, IsConj (x * a) u}

theorem mem_support1 {ddA : DadeHypothesis G L A} {a u : G} :
    u ∈ ddA.support1 a ↔ ∃ x ∈ ddA.signalizer a, ∃ g : G, g * (x * a) * g⁻¹ = u := by
  simp only [support1, Set.mem_setOf_eq, isConj_iff]

/-- Coset elements belong to the local support.  Coq: `mem_Dade_support1`. -/
theorem mul_mem_support1 (ddA : DadeHypothesis G L A) {a x : G}
    (hx : x ∈ ddA.signalizer a) : x * a ∈ ddA.support1 a :=
  ⟨x, hx, IsConj.refl _⟩

theorem self_mem_support1 (ddA : DadeHypothesis G L A) (a : G) : a ∈ ddA.support1 a := by
  have := ddA.mul_mem_support1 (a := a) (ddA.signalizer a).one_mem
  rwa [one_mul] at this

/-- The local support is closed under `G`-conjugation. -/
theorem conj_mem_support1 {ddA : DadeHypothesis G L A} {a u : G}
    (hu : u ∈ ddA.support1 a) (g : G) : g * u * g⁻¹ ∈ ddA.support1 a := by
  obtain ⟨x, hx, hconj⟩ := hu
  exact ⟨x, hx, hconj.trans (isConj_iff.mpr ⟨g, rfl⟩)⟩

/-- **Peterfalvi (2.4)(a), support form** (`Dade_support1_id`): `L`-conjugate elements of
`A` have the same local support. -/
theorem support1_conj [Finite G] (ddA : DadeHypothesis G L A) {x : G} (hx : x ∈ L)
    {a : G} (ha : a ∈ A) : ddA.support1 (x * a * x⁻¹) = ddA.support1 a := by
  ext u
  simp only [support1, Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, hw, hconj⟩
    rw [ddA.signalizer_conj hx ha, Subgroup.mem_map_conj_iff] at hw
    have h1 : IsConj (x⁻¹ * w * x * a) (w * (x * a * x⁻¹)) :=
      isConj_iff.mpr ⟨x, by group⟩
    exact ⟨x⁻¹ * w * x, hw, h1.trans hconj⟩
  · rintro ⟨w, hw, hconj⟩
    refine ⟨x * w * x⁻¹, ?_, ?_⟩
    · rw [ddA.signalizer_conj hx ha, Subgroup.mem_map_conj_iff]
      have harg : x⁻¹ * (x * w * x⁻¹) * x = w := by group
      rwa [harg]
    · have h1 : IsConj (x * w * x⁻¹ * (x * a * x⁻¹)) (w * a) :=
        isConj_iff.mpr ⟨x⁻¹, by group⟩
      exact h1.trans hconj

/-- **Peterfalvi (2.4)(b)** (`Dade_support1_TI`): local supports of non-`L`-conjugate
points of `A` are disjoint — the well-definedness of the Dade lift.  Driven by the
coprime-exponent engine: an element of `support1 a ∩ support1 b` yields conjugates
recovering both `a` and `b` under the same power map `u ↦ u^k`. -/
theorem exists_conj_of_mem_support1 [Finite G] (ddA : DadeHypothesis G L A) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) {u : G} (hu : u ∈ ddA.support1 a)
    (hu' : u ∈ ddA.support1 b) : ∃ x ∈ L, x * a * x⁻¹ = b := by
  obtain ⟨x₁, hx₁, g₁, hg₁⟩ := mem_support1.mp hu
  obtain ⟨x₂, hx₂, g₂, hg₂⟩ := mem_support1.mp hu'
  -- the common exponent for both cosets
  have hco : Nat.Coprime (Nat.card (ddA.signalizer a) * Nat.card (ddA.signalizer b))
      (orderOf a * orderOf b) := by
    have h11 := ddA.coprime_card_signalizer_orderOf ha ha
    have h12 := ddA.coprime_card_signalizer_orderOf ha hb
    have h21 := ddA.coprime_card_signalizer_orderOf hb ha
    have h22 := ddA.coprime_card_signalizer_orderOf hb hb
    exact Nat.Coprime.mul_left (h11.mul_right h12) (h21.mul_right h22)
  obtain ⟨k, hk⟩ := exists_pow_eq_coprime_mul (G := G) hco
  have hpow : ∀ (c : G) (hc : c ∈ A) (y : G), y ∈ ddA.signalizer c →
      orderOf y ∣ Nat.card (ddA.signalizer a) * Nat.card (ddA.signalizer b) →
      orderOf c ∣ orderOf a * orderOf b → (y * c) ^ k = c := by
    intro c hc y hy hdy hdc
    refine hk y c ?_ hdy hdc
    exact Subgroup.mem_centralizer_singleton_iff.mp (ddA.signalizer_le c hc hy)
  have h1 : u ^ k = g₁ * a * g₁⁻¹ := by
    rw [← hg₁, conj_pow_eq,
      hpow a ha x₁ hx₁ ((Subgroup.orderOf_dvd_natCard _ hx₁).trans (dvd_mul_right _ _))
        (dvd_mul_right _ _)]
  have h2 : u ^ k = g₂ * b * g₂⁻¹ := by
    rw [← hg₂, conj_pow_eq,
      hpow b hb x₂ hx₂ ((Subgroup.orderOf_dvd_natCard _ hx₂).trans (dvd_mul_left _ _))
        (dvd_mul_left _ _)]
  refine ddA.fusion a ha b hb (isConj_iff.mpr ⟨g₂⁻¹ * g₁, ?_⟩)
  have := h1.symm.trans h2
  calc g₂⁻¹ * g₁ * a * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * a * g₁⁻¹) * g₂ := by group
    _ = g₂⁻¹ * (g₂ * b * g₂⁻¹) * g₂ := by rw [this]
    _ = b := by group

/-- The `A`-points whose local support contains a given `u ∈ support1 a` are exactly the
`L`-conjugates of `a` — the fiber description used in (2.7) and (2.10). -/
theorem mem_support1_iff_of_mem [Finite G] (ddA : DadeHypothesis G L A) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) {u : G} (hu : u ∈ ddA.support1 a) :
    u ∈ ddA.support1 b ↔ ∃ x ∈ L, x * a * x⁻¹ = b := by
  constructor
  · exact fun hu' => ddA.exists_conj_of_mem_support1 ha hb hu hu'
  · rintro ⟨x, hx, rfl⟩
    rwa [ddA.support1_conj hx ha]

/-- **Peterfalvi (2.4)(c), strengthened** (`Dade_cover_TI`): a conjugation carrying one
point of the coset `(H a) * a` back into the coset centralizes `a`. -/
theorem mem_centralizer_of_conj_coset [Finite G] (ddA : DadeHypothesis G L A) {a : G}
    (ha : a ∈ A) {u w : G} (hu : u * a⁻¹ ∈ ddA.signalizer a)
    (hu' : (w * u * w⁻¹) * a⁻¹ ∈ ddA.signalizer a) : w ∈ Subgroup.centralizer {a} := by
  have hmem : ∀ {v : G}, v * a⁻¹ ∈ ddA.signalizer a →
      v * a⁻¹ ∈ ddA.signalizer a ⊓ Subgroup.centralizer {a} := fun hv =>
    Subgroup.mem_inf.mpr ⟨hv, ddA.signalizer_le a ha hv⟩
  exact mem_centralizer_of_conj_mul_mem (ddA.coprime_card_signalizer_orderOf ha ha)
    (hmem hu) (hmem hu')

/-- **The Dade support** — the union of the local supports.  Coq: `Dade_support`
(`Atau`), `PFsection2.v`. -/
def support (ddA : DadeHypothesis G L A) : Set G :=
  {u | ∃ a ∈ A, u ∈ ddA.support1 a}

theorem support1_subset_support (ddA : DadeHypothesis G L A) {a : G} (ha : a ∈ A) :
    ddA.support1 a ⊆ ddA.support := fun _ hu => ⟨a, ha, hu⟩

/-- `1 ∉ Atau`.  Coq: `not_support_Dade_1`. -/
theorem one_notMem_support (ddA : DadeHypothesis G L A) : (1 : G) ∉ ddA.support := by
  rintro ⟨a, ha, hu⟩
  obtain ⟨x, hx, g, hg⟩ := mem_support1.mp hu
  have hxa : x * a = 1 := by
    have : x * a = g⁻¹ * 1 * g := by rw [← hg]; group
    rwa [mul_one, inv_mul_cancel] at this
  have haH : a ∈ ddA.signalizer a := by
    have h1 : a⁻¹ ∈ ddA.signalizer a := by
      rw [show a⁻¹ = x from (eq_inv_of_mul_eq_one_left hxa).symm]
      exact hx
    simpa using inv_mem h1
  have hmem : a ∈ ddA.signalizer a ⊓ (L ⊓ Subgroup.centralizer {a}) :=
    Subgroup.mem_inf.mpr ⟨haH, ddA.mem_inf_centralizer_self ha⟩
  rw [ddA.signalizer_inf_eq_bot ha, Subgroup.mem_bot] at hmem
  exact ddA.one_notMem (hmem ▸ ha)

/-- The Dade support is closed under `G`-conjugation (it is a normal subset; Coq:
`Dade_support_normal`). -/
theorem conj_mem_support {ddA : DadeHypothesis G L A} {u : G} (hu : u ∈ ddA.support)
    (g : G) : g * u * g⁻¹ ∈ ddA.support := by
  obtain ⟨a, ha, hu⟩ := hu
  exact ⟨a, ha, conj_mem_support1 hu g⟩

/-! ### (2.5) The Dade lift -/

section DadeDef

variable [Finite G]

open scoped Classical in
/-- The underlying function of the Dade lift: `α^τ u = α a` if `u ∈ support1 a` for some
`a ∈ A` (any such `a` gives the same value, by (2.4)(b)), and `0` otherwise.
Coq: the `[pick a in A | x \in dd1 a]` body of `Dade` (`PFsection2.v`, Definition 2.5). -/
def dadeFun (ddA : DadeHypothesis G L A) (α : ClassFunction ↥L) (u : G) : ℂ :=
  if h : ∃ a, a ∈ A ∧ u ∈ ddA.support1 a then
    α ⟨h.choose, ddA.mem_of_mem_set h.choose_spec.1⟩
  else 0

/-- **Well-definedness of the Dade lift** (the validity of Definition (2.5), Coq
`DadeE` at function level): on `support1 a` the lift takes the value `α a`. -/
theorem dadeFun_apply_of_mem_support1 (ddA : DadeHypothesis G L A) (α : ClassFunction ↥L)
    {a u : G} (ha : a ∈ A) (hu : u ∈ ddA.support1 a) :
    ddA.dadeFun α u = α ⟨a, ddA.mem_of_mem_set ha⟩ := by
  have hex : ∃ b, b ∈ A ∧ u ∈ ddA.support1 b := ⟨a, ha, hu⟩
  rw [dadeFun, dif_pos hex]
  obtain ⟨x, hx, hconj⟩ :=
    ddA.exists_conj_of_mem_support1 hex.choose_spec.1 ha hex.choose_spec.2 hu
  set c : ↥L := ⟨hex.choose, ddA.mem_of_mem_set hex.choose_spec.1⟩
  have hsub : (⟨a, ddA.mem_of_mem_set ha⟩ : ↥L) = ⟨x, hx⟩ * c * (⟨x, hx⟩ : ↥L)⁻¹ :=
    Subtype.ext (by push_cast; exact hconj.symm)
  rw [hsub, ClassFunction.conj_apply]

omit [Finite G] in
theorem dadeFun_apply_of_notMem_support (ddA : DadeHypothesis G L A)
    (α : ClassFunction ↥L) {u : G} (hu : u ∉ ddA.support) : ddA.dadeFun α u = 0 := by
  rw [dadeFun, dif_neg]
  rintro ⟨a, ha, hmem⟩
  exact hu ⟨a, ha, hmem⟩

/-- **Peterfalvi Definition (2.5)** — the Dade lift
`dade : ClassFunction ↥L →ₗ[ℂ] ClassFunction G`, `α ↦ α^τ`.  Total on
`ClassFunction ↥L` (like the Coq `Dade`); its characteristic properties hold on
`'CF(L, A)`.  Coq: `Dade` + `Dade_is_linear` (`PFsection2.v`). -/
def dade (ddA : DadeHypothesis G L A) : ClassFunction ↥L →ₗ[ℂ] ClassFunction G where
  toFun α :=
    ⟨ddA.dadeFun α, by
      intro u g
      by_cases h : ∃ a, a ∈ A ∧ u ∈ ddA.support1 a
      · obtain ⟨a, ha, hu⟩ := h
        rw [ddA.dadeFun_apply_of_mem_support1 α ha hu,
          ddA.dadeFun_apply_of_mem_support1 α ha (conj_mem_support1 hu g)]
      · have hu : u ∉ ddA.support := fun ⟨a, ha, hmem⟩ => h ⟨a, ha, hmem⟩
        have hgu : g * u * g⁻¹ ∉ ddA.support := by
          intro hmem
          have := conj_mem_support hmem g⁻¹
          have harg : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
          rw [harg] at this
          exact hu this
        rw [ddA.dadeFun_apply_of_notMem_support α hu,
          ddA.dadeFun_apply_of_notMem_support α hgu]⟩
  map_add' α β := by
    ext u
    show ddA.dadeFun (α + β) u = ddA.dadeFun α u + ddA.dadeFun β u
    by_cases h : ∃ a, a ∈ A ∧ u ∈ ddA.support1 a
    · simp only [dadeFun, dif_pos h, ClassFunction.add_apply]
    · simp only [dadeFun, dif_neg h, add_zero]
  map_smul' c α := by
    ext u
    show ddA.dadeFun (c • α) u = c * ddA.dadeFun α u
    by_cases h : ∃ a, a ∈ A ∧ u ∈ ddA.support1 a
    · simp only [dadeFun, dif_pos h, ClassFunction.smul_apply, smul_eq_mul]
    · simp only [dadeFun, dif_neg h, mul_zero]

/-- **`DadeE`** — the evaluation rule of the Dade lift (the validity of Peterfalvi
Definition (2.5)): `α^τ u = α a` for `u ∈ support1 a`, `a ∈ A`.  No support hypothesis
on `α` is needed (as in the Coq). -/
theorem dade_apply_of_mem_support1 (ddA : DadeHypothesis G L A) (α : ClassFunction ↥L)
    {a u : G} (ha : a ∈ A) (hu : u ∈ ddA.support1 a) :
    ddA.dade α u = α ⟨a, ddA.mem_of_mem_set ha⟩ :=
  ddA.dadeFun_apply_of_mem_support1 α ha hu

theorem dade_apply_of_notMem_support (ddA : DadeHypothesis G L A) (α : ClassFunction ↥L)
    {u : G} (hu : u ∉ ddA.support) : ddA.dade α u = 0 :=
  ddA.dadeFun_apply_of_notMem_support α hu

/-- `α^τ` agrees with `α` on `A`.  Coq: `Dade_id`. -/
theorem dade_apply_of_mem (ddA : DadeHypothesis G L A) (α : ClassFunction ↥L) {a : G}
    (ha : a ∈ A) : ddA.dade α a = α ⟨a, ddA.mem_of_mem_set ha⟩ :=
  ddA.dade_apply_of_mem_support1 α ha (ddA.self_mem_support1 a)

/-- `α^τ` is supported on the Dade support.  Coq: `Dade_cfunS`. -/
theorem dade_mem_supportedOn (ddA : DadeHypothesis G L A) (α : ClassFunction ↥L) :
    ddA.dade α ∈ ClassFunction.supportedOn G ddA.support := fun _ hu =>
  ddA.dade_apply_of_notMem_support α hu

/-- `α^τ 1 = 0`.  Coq: `Dade1`. -/
theorem dade_apply_one (ddA : DadeHypothesis G L A) (α : ClassFunction ↥L) :
    ddA.dade α 1 = 0 :=
  ddA.dade_apply_of_notMem_support α ddA.one_notMem_support

/-- `α^τ ∈ 'CF(G, G^#)`.  Coq: `Dade_cfun` (with `cfunD1E`). -/
theorem dade_mem_supportedOn_compl_one (ddA : DadeHypothesis G L A)
    (α : ClassFunction ↥L) :
    ddA.dade α ∈ ClassFunction.supportedOn G ({1}ᶜ : Set G) :=
  ClassFunction.mem_supportedOn_compl_one.mpr (ddA.dade_apply_one α)

/-- **`Dade_id1`**: for `α ∈ 'CF(L, A)`, the lift agrees with `α` on `{1} ∪ A`. -/
theorem dade_apply_of_mem_insert (ddA : DadeHypothesis G L A) {α : ClassFunction ↥L}
    (hα : α ∈ ClassFunction.supportedOn ↥L (((↑) : ↥L → G) ⁻¹' A)) {a : G} (haL : a ∈ L)
    (ha : a = 1 ∨ a ∈ A) : ddA.dade α a = α ⟨a, haL⟩ := by
  rcases ha with rfl | ha
  · rw [ddA.dade_apply_one α, eq_comm]
    exact hα _ (by simpa using ddA.one_notMem)
  · exact ddA.dade_apply_of_mem α ha

/-- **`Dade_aut`**: the Dade lift commutes with any ring endomorphism of `ℂ` applied to
the values.  Coq: `Dade_aut` (`PFsection2.v`, Section `AutomorphismCFun`). -/
theorem dade_aut (ddA : DadeHypothesis G L A) (v : ℂ →+* ℂ) (α : ClassFunction ↥L) :
    ddA.dade (α.aut v) = (ddA.dade α).aut v := by
  ext u
  rw [ClassFunction.aut_apply]
  by_cases h : ∃ a, a ∈ A ∧ u ∈ ddA.support1 a
  · obtain ⟨a, ha, hu⟩ := h
    rw [ddA.dade_apply_of_mem_support1 _ ha hu, ddA.dade_apply_of_mem_support1 α ha hu,
      ClassFunction.aut_apply]
  · have hu : u ∉ ddA.support := fun ⟨a, ha, hmem⟩ => h ⟨a, ha, hmem⟩
    rw [ddA.dade_apply_of_notMem_support _ hu, ddA.dade_apply_of_notMem_support α hu,
      map_zero]

/-- **`Dade_conjC`**: the Dade lift commutes with complex conjugation. -/
theorem dade_conjC (ddA : DadeHypothesis G L A) (α : ClassFunction ↥L) :
    ddA.dade α.conjC = (ddA.dade α).conjC := by
  rw [← ClassFunction.aut_starRingEnd, ← ClassFunction.aut_starRingEnd]
  exact ddA.dade_aut (starRingEnd ℂ) α

end DadeDef

/-! ### (2.7) Dade reciprocity and (2.6)(a) the isometry property

The Coq proof partitions `Atau` into class supports over a transversal of `A / L` and
each class support into `G`-conjugates of the coset `(H a) * a`.  Here the same counts
are extracted as three lemmas — the conjugator count `card_filter_conj_mem_coset`
(`|{g : g⁻¹ug ∈ (H a) a}| = |C_G(a)|`), the coset-sum collapse `sum_conj_coset`, and the
orbit-weight identity `sum_card_inf_centralizer` (`∑_{a' ∈ a^L} |C_L(a')| = |L|`) — and
the inner products are compared through one weighted double count. -/

section Reciprocity

variable [Fintype G]

open scoped Classical in
/-- The conjugator count behind (2.7): for `u ∈ support1 a` there are exactly `|C_G(a)|`
elements `g ∈ G` with `g⁻¹ u g ∈ (H a) * a`.  Coq: the
`card_orbit`/`astab1Js`/`norm_Dade_cover` step of `general_Dade_reciprocity`, powered by
the strengthened (2.4)(c). -/
theorem card_filter_conj_mem_coset (ddA : DadeHypothesis G L A) {a : G} (ha : a ∈ A)
    {u : G} (hu : u ∈ ddA.support1 a) :
    ({g ∈ (Finset.univ : Finset G) | (g⁻¹ * u * g) * a⁻¹ ∈ ddA.signalizer a}).card
      = Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨x₀, hx₀, g₀, hg₀⟩ := mem_support1.mp hu
  have hbase : (x₀ * a) * a⁻¹ ∈ ddA.signalizer a := by
    rwa [mul_inv_cancel_right]
  have hcard : ({g ∈ (Finset.univ : Finset G) | (g⁻¹ * u * g) * a⁻¹ ∈ ddA.signalizer a}).card
      = ({z ∈ (Finset.univ : Finset G) | z ∈ Subgroup.centralizer ({a} : Set G)}).card := by
    refine Finset.card_bij' (fun g _ => g₀⁻¹ * g) (fun z _ => g₀ * z) ?_ ?_ ?_ ?_
    · -- forward membership: `g₀⁻¹ g` centralizes `a`
      intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      have hkey : ((g₀⁻¹ * g)⁻¹ * (x₀ * a) * (g₀⁻¹ * g)) * a⁻¹ ∈ ddA.signalizer a := by
        have harg : (g₀⁻¹ * g)⁻¹ * (x₀ * a) * (g₀⁻¹ * g) = g⁻¹ * u * g := by
          rw [← hg₀]; group
        rwa [harg]
      have hinv := ddA.mem_centralizer_of_conj_coset ha hbase (w := (g₀⁻¹ * g)⁻¹) (by
        have harg : (g₀⁻¹ * g)⁻¹ * (x₀ * a) * ((g₀⁻¹ * g)⁻¹)⁻¹
            = (g₀⁻¹ * g)⁻¹ * (x₀ * a) * (g₀⁻¹ * g) := by rw [inv_inv]
        rw [harg]
        exact hkey)
      simpa using inv_mem hinv
    · -- backward membership: `g₀ z ∈` the conjugator set for `z ∈ C_G(a)`
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      have hza : z⁻¹ * a * z = a := by
        have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hz
        calc z⁻¹ * a * z = z⁻¹ * (a * z) := by group
          _ = z⁻¹ * (z * a) := by rw [← hcomm]
          _ = a := by group
      have harg : ((g₀ * z)⁻¹ * u * (g₀ * z)) * a⁻¹ = z⁻¹ * x₀ * z := by
        have h1 : (g₀ * z)⁻¹ * u * (g₀ * z) = z⁻¹ * (x₀ * a) * z := by
          rw [← hg₀]; group
        calc ((g₀ * z)⁻¹ * u * (g₀ * z)) * a⁻¹ = (z⁻¹ * (x₀ * a) * z) * a⁻¹ := by rw [h1]
          _ = (z⁻¹ * x₀ * z) * ((z⁻¹ * a * z) * a⁻¹) := by group
          _ = z⁻¹ * x₀ * z := by rw [hza, mul_inv_cancel, mul_one]
      rw [harg]
      have := ddA.signalizer_conj_mem a ha z⁻¹ (inv_mem hz) x₀ hx₀
      simpa using this
    · intro g _; group
    · intro z _; group
  rw [hcard]
  calc ({z ∈ (Finset.univ : Finset G) | z ∈ Subgroup.centralizer ({a} : Set G)}).card
      = Fintype.card {z : G // z ∈ Subgroup.centralizer ({a} : Set G)} :=
        (Fintype.card_subtype _).symm
    _ = Nat.card {z : G // z ∈ Subgroup.centralizer ({a} : Set G)} :=
        Nat.card_eq_fintype_card.symm
    _ = Nat.card (Subgroup.centralizer ({a} : Set G)) := rfl

open scoped Classical in
/-- The coset-sum collapse: summing any function over all `G`-conjugates of all elements
of the coset `(H a) * a` counts each element of `support1 a` exactly `|C_G(a)|` times.
Coq: the `partition_class_support` step of `general_Dade_reciprocity`. -/
theorem sum_conj_coset (ddA : DadeHypothesis G L A) {a : G} (ha : a ∈ A) (h : G → ℂ) :
    ∑ x ∈ {x ∈ (Finset.univ : Finset G) | x ∈ ddA.signalizer a},
        ∑ g : G, h (g * (x * a) * g⁻¹)
      = (Nat.card (Subgroup.centralizer ({a} : Set G)) : ℂ)
        * ∑ u ∈ {u ∈ (Finset.univ : Finset G) | u ∈ ddA.support1 a}, h u := by
  set HF : Finset G := {x ∈ (Finset.univ : Finset G) | x ∈ ddA.signalizer a} with hHF
  set dd1F : Finset G := {u ∈ (Finset.univ : Finset G) | u ∈ ddA.support1 a} with hdd1F
  set key : G × G → G := fun p => p.2 * (p.1 * a) * p.2⁻¹ with hkey
  have hmaps : ∀ p ∈ HF ×ˢ (Finset.univ : Finset G), key p ∈ dd1F := by
    rintro ⟨x, g⟩ hp
    rw [Finset.mem_product, hHF, Finset.mem_filter] at hp
    rw [hdd1F, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, mem_support1.mpr ⟨x, hp.1.2, g, rfl⟩⟩
  have hfib := Finset.sum_fiberwise_of_maps_to' hmaps h
  -- each fiber has `|C_G(a)|` elements, via the conjugator count
  have hfibcard : ∀ u ∈ dd1F,
      ((HF ×ˢ (Finset.univ : Finset G)).filter fun p => key p = u).card
        = Nat.card (Subgroup.centralizer ({a} : Set G)) := by
    intro u hu
    rw [hdd1F, Finset.mem_filter] at hu
    rw [← ddA.card_filter_conj_mem_coset ha hu.2]
    refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
    · rintro ⟨x, g⟩ hp
      rw [Finset.mem_filter, Finset.mem_product, hHF, Finset.mem_filter] at hp
      obtain ⟨⟨⟨-, hx⟩, -⟩, hkeyp⟩ := hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have harg : (g⁻¹ * u * g) * a⁻¹ = x := by
        rw [← hkeyp, hkey]
        show (g⁻¹ * (g * (x * a) * g⁻¹) * g) * a⁻¹ = x
        group
      rwa [harg]
    · rintro ⟨x₁, g₁⟩ hp₁ ⟨x₂, g₂⟩ hp₂ heq
      rw [Finset.mem_filter] at hp₁ hp₂
      dsimp only at heq
      subst heq
      have hval : g₁ * (x₁ * a) * g₁⁻¹ = g₁ * (x₂ * a) * g₁⁻¹ := hp₁.2.trans hp₂.2.symm
      have : x₁ = x₂ := by
        have h1 : x₁ * a = x₂ * a := mul_left_cancel (mul_right_cancel hval)
        exact mul_right_cancel h1
      rw [this]
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      refine ⟨((g⁻¹ * u * g) * a⁻¹, g), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product, hHF, Finset.mem_filter]
      refine ⟨⟨⟨Finset.mem_univ _, hg⟩, Finset.mem_univ _⟩, ?_⟩
      show g * ((g⁻¹ * u * g) * a⁻¹ * a) * g⁻¹ = u
      group
  calc ∑ x ∈ HF, ∑ g : G, h (g * (x * a) * g⁻¹)
      = ∑ p ∈ HF ×ˢ (Finset.univ : Finset G), h (key p) := by
        rw [Finset.sum_product]
    _ = ∑ u ∈ dd1F, ∑ _p ∈ (HF ×ˢ (Finset.univ : Finset G)).filter fun p => key p = u,
          h u := hfib.symm
    _ = ∑ u ∈ dd1F, (Nat.card (Subgroup.centralizer ({a} : Set G)) : ℂ) * h u := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Finset.sum_const, hfibcard u hu, nsmul_eq_mul]
    _ = (Nat.card (Subgroup.centralizer ({a} : Set G)) : ℂ) * ∑ u ∈ dd1F, h u := by
        rw [Finset.mul_sum]

open scoped Classical in
/-- The orbit-weight identity: for `u` in the Dade support with witness `a₀`, the
`A`-points whose local support contains `u` are the `L`-orbit of `a₀`, and their
centralizer orders sum to `|L|`: `∑_{a ∈ a₀^L} |C_L(a)| = |L|`.  Coq: the
`index_cent1`/`Lagrange` bookkeeping inside `general_Dade_reciprocity`. -/
theorem sum_card_inf_centralizer (ddA : DadeHypothesis G L A) {a₀ u : G} (ha₀ : a₀ ∈ A)
    (hu : u ∈ ddA.support1 a₀) :
    ∑ a ∈ {a ∈ (Finset.univ : Finset G) | a ∈ A ∧ u ∈ ddA.support1 a},
        (Nat.card ↥(L ⊓ Subgroup.centralizer {a}) : ℂ)
      = (Nat.card ↥L : ℂ) := by
  letI : Fintype ↥L := Fintype.ofFinite ↥L
  set orbF : Finset G :=
    (Finset.univ : Finset ↥L).image (fun y : ↥L => ↑y * a₀ * (↑y)⁻¹) with horbF
  -- the fiber Finset is the `L`-orbit of `a₀`
  have hset : {a ∈ (Finset.univ : Finset G) | a ∈ A ∧ u ∈ ddA.support1 a} = orbF := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, horbF, Finset.mem_image]
    constructor
    · rintro ⟨hb, hub⟩
      obtain ⟨x, hx, hconj⟩ := ddA.exists_conj_of_mem_support1 ha₀ hb hu hub
      exact ⟨⟨x, hx⟩, by simpa using hconj⟩
    · rintro ⟨y, rfl⟩
      refine ⟨ddA.conj_mem ↑y y.2 a₀ ha₀, ?_⟩
      rwa [ddA.support1_conj y.2 ha₀]
  -- centralizer orders are constant along the orbit
  have hconst : ∀ y : ↥L,
      Nat.card ↥(L ⊓ Subgroup.centralizer {↑y * a₀ * (↑y)⁻¹})
        = Nat.card ↥(L ⊓ Subgroup.centralizer {a₀}) := by
    intro y
    refine Nat.card_congr ⟨fun w => ⟨(↑y)⁻¹ * ↑w * ↑y, ?_⟩, fun v => ⟨↑y * ↑v * (↑y)⁻¹, ?_⟩,
      fun w => ?_, fun v => ?_⟩
    · obtain ⟨hwL, hwC⟩ := Subgroup.mem_inf.mp w.2
      exact Subgroup.mem_inf.mpr
        ⟨mul_mem (mul_mem (inv_mem y.2) hwL) y.2, mem_centralizer_conj_iff.mp hwC⟩
    · obtain ⟨hvL, hvC⟩ := Subgroup.mem_inf.mp v.2
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem y.2 hvL) (inv_mem y.2), ?_⟩
      rw [mem_centralizer_conj_iff]
      have harg : (↑y)⁻¹ * (↑y * ↑v * (↑y)⁻¹) * ↑y = (v : G) := by group
      rwa [harg]
    · ext; push_cast; group
    · ext; push_cast; group
  -- the orbit-stabilizer count `|orbit| * |C_L(a₀)| = |L|`
  have horb : orbF.card * Nat.card ↥(L ⊓ Subgroup.centralizer {a₀}) = Nat.card ↥L := by
    have hfibcard : ∀ b ∈ orbF,
        ((Finset.univ : Finset ↥L).filter fun y : ↥L => ↑y * a₀ * (↑y)⁻¹ = b).card
          = Nat.card ↥(L ⊓ Subgroup.centralizer {a₀}) := by
      intro b hb
      rw [horbF, Finset.mem_image] at hb
      obtain ⟨y₀, -, rfl⟩ := hb
      calc ((Finset.univ : Finset ↥L).filter
              fun y : ↥L => ↑y * a₀ * (↑y)⁻¹ = ↑y₀ * a₀ * (↑y₀)⁻¹).card
          = Fintype.card {y : ↥L // ↑y * a₀ * (↑y)⁻¹ = ↑y₀ * a₀ * (↑y₀)⁻¹} :=
            (Fintype.card_subtype _).symm
        _ = Nat.card {y : ↥L // ↑y * a₀ * (↑y)⁻¹ = ↑y₀ * a₀ * (↑y₀)⁻¹} :=
            Nat.card_eq_fintype_card.symm
        _ = Nat.card ↥(L ⊓ Subgroup.centralizer {a₀}) := by
            refine Nat.card_congr ⟨fun y => ⟨(↑y₀)⁻¹ * ↑y.1, ?_⟩,
              fun c => ⟨⟨↑y₀ * ↑c, mul_mem y₀.2 (Subgroup.mem_inf.mp c.2).1⟩, ?_⟩,
              fun y => ?_, fun c => ?_⟩
            · obtain ⟨y, hy⟩ := y
              refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem y₀.2) y.2, ?_⟩
              rw [Subgroup.mem_centralizer_singleton_iff]
              have h1 : (↑y : G) * a₀ * (↑y)⁻¹ = ↑y₀ * a₀ * (↑y₀)⁻¹ := hy
              calc (↑y₀)⁻¹ * ↑y * a₀ = (↑y₀)⁻¹ * (↑y * a₀ * (↑y)⁻¹) * ↑y := by group
                _ = (↑y₀)⁻¹ * (↑y₀ * a₀ * (↑y₀)⁻¹) * ↑y := by rw [h1]
                _ = a₀ * ((↑y₀)⁻¹ * ↑y) := by group
            · have hcC := (Subgroup.mem_inf.mp c.2).2
              have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hcC
              show ((y₀ : G) * (c : G)) * a₀ * ((y₀ : G) * (c : G))⁻¹
                  = (y₀ : G) * a₀ * (y₀ : G)⁻¹
              have hca : (c : G) * a₀ * (c : G)⁻¹ = a₀ := by
                rw [hcomm, mul_inv_cancel_right]
              calc ((y₀ : G) * (c : G)) * a₀ * ((y₀ : G) * (c : G))⁻¹
                  = (y₀ : G) * ((c : G) * a₀ * (c : G)⁻¹) * (y₀ : G)⁻¹ := by group
                _ = (y₀ : G) * a₀ * (y₀ : G)⁻¹ := by rw [hca]
            · ext; push_cast; group
            · ext; push_cast; group
    have hL := Finset.card_eq_sum_card_image (fun y : ↥L => ↑y * a₀ * (↑y)⁻¹)
      (Finset.univ : Finset ↥L)
    rw [← horbF] at hL
    rw [Finset.sum_congr rfl hfibcard, Finset.sum_const, smul_eq_mul] at hL
    rw [← hL, Finset.card_univ, Nat.card_eq_fintype_card]
  -- assemble in `ℂ`
  rw [hset]
  have hconst' : ∀ b ∈ orbF, (Nat.card ↥(L ⊓ Subgroup.centralizer {b}) : ℂ)
      = (Nat.card ↥(L ⊓ Subgroup.centralizer {a₀}) : ℂ) := by
    intro b hb
    rw [horbF, Finset.mem_image] at hb
    obtain ⟨y, -, rfl⟩ := hb
    exact congrArg (fun n : ℕ => (n : ℂ)) (hconst y)
  rw [Finset.sum_congr rfl hconst', Finset.sum_const, nsmul_eq_mul, ← Nat.cast_mul, horb]

open scoped Classical in
/-- **Peterfalvi (2.7), main part** (`general_Dade_reciprocity`): for `α ∈ 'CF(L, A)`
and `φ ∈ CF(G)`, if `ψ ∈ CF(L)` satisfies `ψ a = |H a|⁻¹ ∑_{x ∈ H a} φ(x a)` on `A`,
then `⟪α^τ, φ⟫_G = ⟪α, ψ⟫_L`. -/
theorem general_dade_reciprocity [Fintype L] (ddA : DadeHypothesis G L A)
    {α : ClassFunction ↥L}
    (hα : α ∈ ClassFunction.supportedOn ↥L (((↑) : ↥L → G) ⁻¹' A)) (φ : ClassFunction G)
    (ψ : ClassFunction ↥L)
    (hψ : ∀ (a : G) (ha : a ∈ A),
      ψ ⟨a, ddA.mem_of_mem_set ha⟩ = (Nat.card (ddA.signalizer a) : ℂ)⁻¹
        * ∑ x : ↥(ddA.signalizer a), φ (↑x * a)) :
    ⟪ddA.dade α, φ⟫_[G] = ⟪α, ψ⟫_[↥L] := by
  classical
  set AF : Finset G := {a ∈ (Finset.univ : Finset G) | a ∈ A} with hAF
  set AtF : Finset G := {u ∈ (Finset.univ : Finset G) | u ∈ ddA.support} with hAtF
  have hG0 : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hL0 : (Fintype.card ↥L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- abbreviations for the two per-`a` partial sums
  set P : G → ℂ := fun a => ∑ u ∈ {u ∈ (Finset.univ : Finset G) | u ∈ ddA.support1 a},
    starRingEnd ℂ (φ u) with hP
  set Q : G → ℂ := fun a => ∑ x ∈ {x ∈ (Finset.univ : Finset G) | x ∈ ddA.signalizer a},
    starRingEnd ℂ (φ (x * a)) with hQ
  -- the coset-sum collapse relates `P` and `Q`
  have hPQ : ∀ a ∈ AF, (Fintype.card G : ℂ) * Q a
      = (Nat.card (Subgroup.centralizer ({a} : Set G)) : ℂ) * P a := by
    intro a haF
    rw [hAF, Finset.mem_filter] at haF
    have := ddA.sum_conj_coset haF.2 (fun u => starRingEnd ℂ (φ u))
    rw [hP, hQ, ← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hval : ∀ g : G, starRingEnd ℂ (φ (g * (x * a) * g⁻¹)) = starRingEnd ℂ (φ (x * a)) :=
      fun g => by rw [φ.conj_apply]
    rw [Finset.sum_congr rfl fun g _ => hval g, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  -- Step 1: expand the left inner product over the Dade support
  have hL1 : ⟪ddA.dade α, φ⟫_[G] = (Fintype.card G : ℂ)⁻¹
      * ∑ u ∈ AtF, ddA.dade α u * starRingEnd ℂ (φ u) := by
    rw [ClassFunction.cfInner_def]
    congr 1
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun u _ hu => ?_).symm
    have hu' : u ∉ ddA.support := fun hmem =>
      hu (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hmem⟩)
    rw [ddA.dade_apply_of_notMem_support α hu', zero_mul]
  -- Step 2: the support sum decomposes over `A` with weights `|C_L(a)|`
  have hL2 : (Nat.card ↥L : ℂ) * ∑ u ∈ AtF, ddA.dade α u * starRingEnd ℂ (φ u)
      = ∑ a ∈ AF, (Nat.card ↥(L ⊓ Subgroup.centralizer {a}) : ℂ)
          * (ClassFunction.extendZero α a * P a) := by
    have hswap : ∑ a ∈ AF, ∑ u ∈ {u ∈ (Finset.univ : Finset G) | u ∈ ddA.support1 a},
          (Nat.card ↥(L ⊓ Subgroup.centralizer {a}) : ℂ)
            * (ddA.dade α u * starRingEnd ℂ (φ u))
        = ∑ u ∈ AtF, ∑ a ∈ {a ∈ (Finset.univ : Finset G) | a ∈ A ∧ u ∈ ddA.support1 a},
            (Nat.card ↥(L ⊓ Subgroup.centralizer {a}) : ℂ)
              * (ddA.dade α u * starRingEnd ℂ (φ u)) := by
      refine Finset.sum_comm' fun a u => ?_
      simp only [hAF, hAtF, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨ha, hua⟩
        exact ⟨⟨ha, hua⟩, ⟨a, ha, hua⟩⟩
      · rintro ⟨⟨ha, hua⟩, -⟩
        exact ⟨ha, hua⟩
    calc (Nat.card ↥L : ℂ) * ∑ u ∈ AtF, ddA.dade α u * starRingEnd ℂ (φ u)
        = ∑ u ∈ AtF, (Nat.card ↥L : ℂ) * (ddA.dade α u * starRingEnd ℂ (φ u)) := by
          rw [Finset.mul_sum]
      _ = ∑ u ∈ AtF, ∑ a ∈ {a ∈ (Finset.univ : Finset G) | a ∈ A ∧ u ∈ ddA.support1 a},
            (Nat.card ↥(L ⊓ Subgroup.centralizer {a}) : ℂ)
              * (ddA.dade α u * starRingEnd ℂ (φ u)) := by
          refine Finset.sum_congr rfl fun u hu => ?_
          rw [hAtF, Finset.mem_filter] at hu
          obtain ⟨-, a₀, ha₀, hua₀⟩ := hu
          rw [← Finset.sum_mul, ddA.sum_card_inf_centralizer ha₀ hua₀]
      _ = ∑ a ∈ AF, ∑ u ∈ {u ∈ (Finset.univ : Finset G) | u ∈ ddA.support1 a},
            (Nat.card ↥(L ⊓ Subgroup.centralizer {a}) : ℂ)
              * (ddA.dade α u * starRingEnd ℂ (φ u)) := hswap.symm
      _ = ∑ a ∈ AF, (Nat.card ↥(L ⊓ Subgroup.centralizer {a}) : ℂ)
            * (ClassFunction.extendZero α a * P a) := by
          refine Finset.sum_congr rfl fun a haF => ?_
          rw [hAF, Finset.mem_filter] at haF
          rw [hP, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun u hu => ?_
          rw [Finset.mem_filter] at hu
          rw [ddA.dade_apply_of_mem_support1 α haF.2 hu.2,
            ClassFunction.extendZero_apply_of_mem α (ddA.mem_of_mem_set haF.2)]
  -- Step 3: the right inner product over `A`, with `conj ψ` expanded by `hψ`
  have hR1 : ⟪α, ψ⟫_[↥L] = (Fintype.card ↥L : ℂ)⁻¹
      * ∑ a ∈ AF, ClassFunction.extendZero α a
          * ((Nat.card (ddA.signalizer a) : ℂ)⁻¹ * Q a) := by
    rw [ClassFunction.cfInner_def]
    congr 1
    have hsub : ∑ l : ↥L, α l * starRingEnd ℂ (ψ l)
        = ∑ l ∈ (Finset.univ : Finset ↥L).filter (fun l : ↥L => (l : G) ∈ A),
            α l * starRingEnd ℂ (ψ l) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) fun l _ hl => ?_).symm
      have hl' : (l : G) ∉ A := fun hmem =>
        hl (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hmem⟩)
      rw [hα l hl', zero_mul]
    rw [hsub]
    refine Finset.sum_bij (fun l _ => (l : G)) ?_ ?_ ?_ ?_
    · intro l hl
      rw [Finset.mem_filter] at hl
      rw [hAF, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hl.2⟩
    · intro l₁ h₁ l₂ h₂ h
      exact Subtype.ext h
    · intro a haF
      rw [hAF, Finset.mem_filter] at haF
      exact ⟨⟨a, ddA.mem_of_mem_set haF.2⟩, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, haF.2⟩, rfl⟩
    · intro l hl
      rw [Finset.mem_filter] at hl
      have hl' : (l : G) ∈ A := hl.2
      have hle : ClassFunction.extendZero α (l : G) = α l := by
        rw [ClassFunction.extendZero_apply_of_mem α l.2]
      have hψl : starRingEnd ℂ (ψ l)
          = (Nat.card (ddA.signalizer (l : G)) : ℂ)⁻¹ * Q (l : G) := by
        have h1 : ψ l = (Nat.card (ddA.signalizer (l : G)) : ℂ)⁻¹
            * ∑ x : ↥(ddA.signalizer (l : G)), φ (↑x * (l : G)) := by
          have := hψ (l : G) hl'
          have hsubty : (⟨(l : G), ddA.mem_of_mem_set hl'⟩ : ↥L) = l := Subtype.ext rfl
          rwa [hsubty] at this
        rw [h1, map_mul, map_inv₀, map_natCast, map_sum, hQ]
        congr 1
        rw [← Finset.sum_subtype (p := fun x => x ∈ ddA.signalizer (l : G))
          {x ∈ (Finset.univ : Finset G) | x ∈ ddA.signalizer (l : G)} (by simp)
          (fun x => starRingEnd ℂ (φ (x * (l : G))))]
      rw [hle, hψl]
  -- Step 4: match the two expansions termwise
  have hterm : ∀ a ∈ AF,
      (Nat.card ↥(L ⊓ Subgroup.centralizer {a}) : ℂ) * (ClassFunction.extendZero α a * P a)
        = (Fintype.card G : ℂ) * (ClassFunction.extendZero α a
            * ((Nat.card (ddA.signalizer a) : ℂ)⁻¹ * Q a)) := by
    intro a haF
    have haA : a ∈ A := by
      rw [hAF, Finset.mem_filter] at haF
      exact haF.2
    have hHa0 : (Nat.card (ddA.signalizer a) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hcards : (Nat.card (ddA.signalizer a) : ℂ)
        * (Nat.card ↥(L ⊓ Subgroup.centralizer {a}) : ℂ)
        = (Nat.card (Subgroup.centralizer ({a} : Set G)) : ℂ) := by
      rw [← Nat.cast_mul, ddA.card_signalizer_mul_card haA]
    have hQP := hPQ a haF
    refine mul_left_cancel₀ hHa0 ?_
    calc (Nat.card (ddA.signalizer a) : ℂ)
          * ((Nat.card ↥(L ⊓ Subgroup.centralizer {a}) : ℂ)
            * (ClassFunction.extendZero α a * P a))
        = ClassFunction.extendZero α a
            * ((Nat.card (ddA.signalizer a) : ℂ)
              * (Nat.card ↥(L ⊓ Subgroup.centralizer {a}) : ℂ) * P a) := by ring
      _ = ClassFunction.extendZero α a
            * ((Nat.card (Subgroup.centralizer ({a} : Set G)) : ℂ) * P a) := by
          rw [hcards]
      _ = ClassFunction.extendZero α a * ((Fintype.card G : ℂ) * Q a) := by rw [← hQP]
      _ = (Nat.card (ddA.signalizer a) : ℂ)
            * ((Fintype.card G : ℂ) * (ClassFunction.extendZero α a
              * ((Nat.card (ddA.signalizer a) : ℂ)⁻¹ * Q a))) := by
          field_simp
  -- assemble
  rw [hL1, hR1]
  have hsum := hL2
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hsum
  set S₁ : ℂ := ∑ u ∈ AtF, ddA.dade α u * starRingEnd ℂ (φ u) with hS₁
  set S₂ : ℂ := ∑ a ∈ AF, ClassFunction.extendZero α a
      * ((Nat.card (ddA.signalizer a) : ℂ)⁻¹ * Q a) with hS₂
  have hkey : (Fintype.card ↥L : ℂ) * S₁ = (Fintype.card G : ℂ) * S₂ := by
    rw [← Nat.card_eq_fintype_card (α := ↥L)]
    exact hsum
  calc (Fintype.card G : ℂ)⁻¹ * S₁
      = (Fintype.card G : ℂ)⁻¹
          * ((Fintype.card ↥L : ℂ)⁻¹ * ((Fintype.card ↥L : ℂ) * S₁)) := by
        rw [← mul_assoc ((Fintype.card ↥L : ℂ)⁻¹), inv_mul_cancel₀ hL0, one_mul]
    _ = (Fintype.card G : ℂ)⁻¹
          * ((Fintype.card ↥L : ℂ)⁻¹ * ((Fintype.card G : ℂ) * S₂)) := by
        rw [hkey]
    _ = (Fintype.card ↥L : ℂ)⁻¹ * S₂ := by
        field_simp

open scoped Classical in
/-- **Peterfalvi (2.7), second part** (`Dade_reciprocity`): if `φ ∈ CF(G)` is constant
on each coset `(H a) * a`, then `⟪α^τ, φ⟫_G = ⟪α, Res_L φ⟫_L`. -/
theorem dade_reciprocity [Fintype L] (ddA : DadeHypothesis G L A) {α : ClassFunction ↥L}
    (hα : α ∈ ClassFunction.supportedOn ↥L (((↑) : ↥L → G) ⁻¹' A)) (φ : ClassFunction G)
    (hφ : ∀ a ∈ A, ∀ x ∈ ddA.signalizer a, φ (x * a) = φ a) :
    ⟪ddA.dade α, φ⟫_[G] = ⟪α, ClassFunction.res L φ⟫_[↥L] := by
  classical
  refine ddA.general_dade_reciprocity hα φ _ fun a ha => ?_
  have hHa0 : (Nat.card (ddA.signalizer a) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [ClassFunction.res_apply]
  have hval : ∀ x : ↥(ddA.signalizer a), φ (↑x * a) = φ a := fun x => hφ a ha ↑x x.2
  rw [Finset.sum_congr rfl fun x _ => hval x, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hHa0, one_mul]

/-- **Peterfalvi (2.6)(a)** (`Dade_isometry`): the Dade lift is an isometry on
`'CF(L, A)`: `⟪α^τ, β^τ⟫_G = ⟪α, β⟫_L`.  Only the *first* argument needs to be supported
on `A` (the Coq states the symmetric special case `{in 'CF(L, A) &, isometry Dade}`);
the one-sided form matches the seed TI isometry
`ClassFunction.cfInner_ind_ind_of_malnormal`. -/
theorem dade_isometry [Fintype L] (ddA : DadeHypothesis G L A) {α : ClassFunction ↥L}
    (hα : α ∈ ClassFunction.supportedOn ↥L (((↑) : ↥L → G) ⁻¹' A))
    (β : ClassFunction ↥L) :
    ⟪ddA.dade α, ddA.dade β⟫_[G] = ⟪α, β⟫_[↥L] := by
  classical
  refine ddA.general_dade_reciprocity hα (ddA.dade β) β fun a ha => ?_
  have hHa0 : (Nat.card (ddA.signalizer a) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hval : ∀ x : ↥(ddA.signalizer a),
      ddA.dade β (↑x * a) = β ⟨a, ddA.mem_of_mem_set ha⟩ := fun x =>
    ddA.dade_apply_of_mem_support1 β ha (ddA.mul_mem_support1 x.2)
  rw [Finset.sum_congr rfl fun x _ => hval x, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hHa0, one_mul]

end Reciprocity

end DadeHypothesis

/-! ### (2.8)–(2.10) The expansion of the Dade lift into induced class functions

For a nonempty subset `B ⊆ A` (a `Finset`, so that (2.10)'s alternating sums are finite),
the Coq defines `'H(B) = ⋂_{b ∈ B} H b` (`Dade_set_signalizer`), `'N_L(B)`
(`setNormalizer L B` below), `'M(B) = 'H(B) ⋊ 'N_L(B)` (`Dade_set_normalizer`), and the
restriction `'aa_B` of `α ∈ 'CF(L, A)` to `'M(B)` along the projection killing `'H(B)`
(`Dade_cfun_restriction`).  (2.10) expands `α^τ` as
`-∑_{B ∈ calB} (-1)^{|B|} Ind_{M(B)}^G 'aa_B` over a transversal `calB` of the
`L`-orbits of such `B`. -/

section SetSignalizer

/-- `'N_L(B)`: the stabilizer in `L` of a `Finset` `B` under conjugation.
Coq: `'N_L(B)` in `PFsection2.v` (the `Dade_set_normalizer` factor). -/
def setNormalizer (L : Subgroup G) (B : Finset G) : Subgroup G :=
  L ⊓ Subgroup.normalizer (↑B : Set G)

theorem mem_setNormalizer {L : Subgroup G} {B : Finset G} {x : G} :
    x ∈ setNormalizer L B ↔ x ∈ L ∧ ∀ b : G, b ∈ B ↔ x * b * x⁻¹ ∈ B := by
  rw [setNormalizer, Subgroup.mem_inf, Subgroup.mem_set_normalizer_iff]
  simp only [Finset.mem_coe]

theorem setNormalizer_le {L : Subgroup G} {B : Finset G} : setNormalizer L B ≤ L :=
  inf_le_left

open scoped Classical in
/-- A `Finset` is fixed by conjugation exactly by the members of the normalizer of its
coercion. -/
theorem image_conj_eq_iff {B : Finset G} {w : G} :
    B.image (fun b => w * b * w⁻¹) = B ↔ w ∈ Subgroup.normalizer (↑B : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    constructor
    · intro hn
      have : w * n * w⁻¹ ∈ B.image (fun b => w * b * w⁻¹) :=
        Finset.mem_image.mpr ⟨n, hn, rfl⟩
      rwa [h] at this
    · intro hn
      rw [← h] at hn
      obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp hn
      have : b = n := mul_left_cancel (mul_right_cancel hbe)
      rwa [← this]
  · intro h
    ext m
    rw [Finset.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ((Subgroup.mem_set_normalizer_iff.mp h) b).mp hb
    · intro hm
      refine ⟨w⁻¹ * m * w, ?_, by group⟩
      have := (Subgroup.mem_set_normalizer_iff.mp h) (w⁻¹ * m * w)
      rw [show w * (w⁻¹ * m * w) * w⁻¹ = m by group] at this
      exact this.mpr hm

open scoped Classical in
/-- Composition law for `Finset` conjugation. -/
theorem image_conj_image_conj (B : Finset G) (x y : G) :
    (B.image fun b => y * b * y⁻¹).image (fun b => x * b * x⁻¹)
      = B.image (fun b => (x * y) * b * (x * y)⁻¹) := by
  rw [Finset.image_image]
  refine Finset.image_congr fun b _ => ?_
  show x * (y * b * y⁻¹) * x⁻¹ = (x * y) * b * (x * y)⁻¹
  group

namespace DadeHypothesis

variable {L : Subgroup G} {A : Set G}

/-- `'H(B) = ⋂_{b ∈ B} H b` — the generalized signalizer of Peterfalvi (2.8)–(2.10).
Coq: `Dade_set_signalizer` (`PFsection2.v`). -/
def setSignalizer (ddA : DadeHypothesis G L A) (B : Finset G) : Subgroup G :=
  ⨅ b ∈ B, ddA.signalizer b

theorem mem_setSignalizer {ddA : DadeHypothesis G L A} {B : Finset G} {x : G} :
    x ∈ ddA.setSignalizer B ↔ ∀ b ∈ B, x ∈ ddA.signalizer b := by
  simp [setSignalizer, Subgroup.mem_iInf]

theorem setSignalizer_le (ddA : DadeHypothesis G L A) {B : Finset G} {b : G} (hb : b ∈ B) :
    ddA.setSignalizer B ≤ ddA.signalizer b := fun _ hx => mem_setSignalizer.mp hx b hb

theorem setSignalizer_singleton (ddA : DadeHypothesis G L A) (a : G) :
    ddA.setSignalizer {a} = ddA.signalizer a := by
  ext x
  simp [mem_setSignalizer]

/-- `|'H(B)|` is coprime to `|C_L(b')|` for every `b' ∈ A` — the `π'`-group property of
the generalized signalizer, inherited from any single member of `B`. -/
theorem coprime_card_setSignalizer (ddA : DadeHypothesis G L A) {B : Finset G}
    (hB : ↑B ⊆ A) (hne : B.Nonempty) {b' : G} (hb' : b' ∈ A) :
    Nat.Coprime (Nat.card (ddA.setSignalizer B))
      (Nat.card ↥(L ⊓ Subgroup.centralizer {b'})) := by
  obtain ⟨b₀, hb₀⟩ := hne
  exact Nat.Coprime.coprime_dvd_left
    (Subgroup.card_dvd_of_le (ddA.setSignalizer_le hb₀))
    (ddA.signalizer_coprime b₀ (hB hb₀) b' hb')

/-- Members of `'N_L(B)` normalize `'H(B)` (elementwise form).  Part of Peterfalvi (2.8),
Coq `Dade_set_sdprod`. -/
theorem conj_mem_setSignalizer [Finite G] (ddA : DadeHypothesis G L A) {B : Finset G}
    (hB : ↑B ⊆ A) {x : G} (hx : x ∈ setNormalizer L B) {h : G}
    (hh : h ∈ ddA.setSignalizer B) : x * h * x⁻¹ ∈ ddA.setSignalizer B := by
  obtain ⟨hxL, hxB⟩ := mem_setNormalizer.mp hx
  rw [mem_setSignalizer]
  intro b hb
  have hb' : x⁻¹ * b * x ∈ B := by
    have := hxB (x⁻¹ * b * x)
    rw [show x * (x⁻¹ * b * x) * x⁻¹ = b by group] at this
    exact this.mpr hb
  have hbA : x⁻¹ * b * x ∈ A := hB hb'
  have hconj : ddA.signalizer b
      = (ddA.signalizer (x⁻¹ * b * x)).map (MulAut.conj x).toMonoidHom := by
    have := ddA.signalizer_conj hxL hbA
    rwa [show x * (x⁻¹ * b * x) * x⁻¹ = b by group] at this
  rw [hconj, Subgroup.mem_map_conj_iff]
  have harg : x⁻¹ * (x * h * x⁻¹) * x = h := by group
  rw [harg]
  exact mem_setSignalizer.mp hh _ hb'

/-- `'H(B) ⊓ 'N_L(B) = ⊥` — part of Peterfalvi (2.8), Coq `Dade_set_sdprod`. -/
theorem setSignalizer_inf_setNormalizer (ddA : DadeHypothesis G L A) {B : Finset G}
    (hB : ↑B ⊆ A) (hne : B.Nonempty) :
    ddA.setSignalizer B ⊓ setNormalizer L B = ⊥ := by
  obtain ⟨b₀, hb₀⟩ := hne
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH, hxN⟩ := Subgroup.mem_inf.mp hx
  have h1 : x ∈ ddA.signalizer b₀ := ddA.setSignalizer_le hb₀ hxH
  have h2 : x ∈ L ⊓ Subgroup.centralizer {b₀} :=
    Subgroup.mem_inf.mpr ⟨setNormalizer_le hxN, ddA.signalizer_le b₀ (hB hb₀) h1⟩
  have h3 : x ∈ ddA.signalizer b₀ ⊓ (L ⊓ Subgroup.centralizer {b₀}) :=
    Subgroup.mem_inf.mpr ⟨h1, h2⟩
  rw [ddA.signalizer_inf_eq_bot (hB hb₀)] at h3
  exact h3

/-- `'M(B) = 'H(B) ⊔ 'N_L(B)` — with (2.8) this is the internal semidirect product
`'H(B) ⋊ 'N_L(B)`.  Coq: `Dade_set_normalizer` (`PFsection2.v`). -/
def setProd (ddA : DadeHypothesis G L A) (B : Finset G) : Subgroup G :=
  ddA.setSignalizer B ⊔ setNormalizer L B

theorem setSignalizer_le_setProd (ddA : DadeHypothesis G L A) {B : Finset G} :
    ddA.setSignalizer B ≤ ddA.setProd B := le_sup_left

theorem setNormalizer_le_setProd (ddA : DadeHypothesis G L A) {B : Finset G} :
    setNormalizer L B ≤ ddA.setProd B := le_sup_right

/-- **Peterfalvi (2.8)** (`Dade_set_sdprod`), decomposition form: every element of
`'M(B)` factors as `h * n` with `h ∈ 'H(B)`, `n ∈ 'N_L(B)`. -/
theorem exists_mul_of_mem_setProd [Finite G] (ddA : DadeHypothesis G L A) {B : Finset G}
    (hB : ↑B ⊆ A) {m : G} (hm : m ∈ ddA.setProd B) :
    ∃ h ∈ ddA.setSignalizer B, ∃ n ∈ setNormalizer L B, m = h * n := by
  rw [setProd, Subgroup.sup_eq_closure] at hm
  induction hm using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, one_mem _, (mul_one x).symm⟩
    · exact ⟨1, one_mem _, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, (one_mul 1).symm⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨h₁, hh₁, n₁, hn₁, rfl⟩ := ihx
    obtain ⟨h₂, hh₂, n₂, hn₂, rfl⟩ := ihy
    refine ⟨h₁ * (n₁ * h₂ * n₁⁻¹), mul_mem hh₁ (ddA.conj_mem_setSignalizer hB hn₁ hh₂),
      n₁ * n₂, mul_mem hn₁ hn₂, by group⟩
  | inv x _ ihx =>
    obtain ⟨h, hh, n, hn, rfl⟩ := ihx
    refine ⟨n⁻¹ * h⁻¹ * n, ?_, n⁻¹, inv_mem hn, by group⟩
    have := ddA.conj_mem_setSignalizer hB (inv_mem hn) (inv_mem hh)
    simpa using this

/-- The `'H(B)`-part of `'M(B)` is normal in `'M(B)` (as a `subgroupOf`). -/
theorem normal_setSignalizer_subgroupOf' [Finite G] (ddA : DadeHypothesis G L A)
    {B : Finset G} (hB : ↑B ⊆ A) :
    ((ddA.setSignalizer B).subgroupOf (ddA.setProd B)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨h, hh, m, hm, hgm⟩ := ddA.exists_mul_of_mem_setProd hB g.2
  have step1 : m * ↑n * m⁻¹ ∈ ddA.setSignalizer B := ddA.conj_mem_setSignalizer hB hm hn
  have step2 : h * (m * ↑n * m⁻¹) * h⁻¹ ∈ ddA.setSignalizer B :=
    mul_mem (mul_mem hh step1) (inv_mem hh)
  have harg : (↑g : G) * ↑n * (↑g)⁻¹ = h * (m * ↑n * m⁻¹) * h⁻¹ := by
    rw [hgm]; group
  push_cast
  rwa [harg]

open scoped Pointwise in
/-- **Peterfalvi (2.8)** (`Dade_set_sdprod`), complement form: `'N_L(B)` and `'H(B)` are
complements inside `'M(B)` (with `'H(B)` normal), realizing `'M(B) = 'H(B) ⋊ 'N_L(B)`. -/
theorem isComplement'_setProd [Finite G] (ddA : DadeHypothesis G L A) {B : Finset G}
    (hB : ↑B ⊆ A) (hne : B.Nonempty) :
    ((setNormalizer L B).subgroupOf (ddA.setProd B)).IsComplement'
      ((ddA.setSignalizer B).subgroupOf (ddA.setProd B)) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxH⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_subgroupOf] at hxN hxH
    have hmem : (↑x : G) ∈ ddA.setSignalizer B ⊓ setNormalizer L B :=
      Subgroup.mem_inf.mpr ⟨hxH, hxN⟩
    rw [ddA.setSignalizer_inf_setNormalizer hB hne, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact Subtype.ext hmem
  · refine Set.eq_univ_iff_forall.mpr fun u => ?_
    obtain ⟨h, hh, n, hn, hu⟩ := ddA.exists_mul_of_mem_setProd hB u.2
    have hh' : n⁻¹ * h * n ∈ ddA.setSignalizer B := by
      have := ddA.conj_mem_setSignalizer hB (inv_mem hn) hh
      simpa using this
    refine Set.mem_mul.mpr
      ⟨⟨n, ddA.setNormalizer_le_setProd hn⟩, ?_,
        ⟨n⁻¹ * h * n, ddA.setSignalizer_le_setProd hh'⟩, ?_, ?_⟩
    · exact SetLike.mem_coe.mpr (Subgroup.mem_subgroupOf.mpr hn)
    · exact SetLike.mem_coe.mpr (Subgroup.mem_subgroupOf.mpr hh')
    · ext
      push_cast
      rw [hu]
      group

/-- `|'M(B)| = |'H(B)| * |'N_L(B)|`. -/
theorem card_setProd [Finite G] (ddA : DadeHypothesis G L A) {B : Finset G}
    (hB : ↑B ⊆ A) (hne : B.Nonempty) :
    Nat.card (ddA.setProd B)
      = Nat.card (ddA.setSignalizer B) * Nat.card (setNormalizer L B) := by
  have h := (ddA.isComplement'_setProd hB hne).card_mul
  rw [Subgroup.card_subgroupOf ddA.setNormalizer_le_setProd,
    Subgroup.card_subgroupOf ddA.setSignalizer_le_setProd] at h
  rw [← h, mul_comm]

/-! #### The Dade restriction `'aa_B` -/

section Restriction

variable [Fintype G]

open scoped Classical in
/-- The projection `'M(B) → L` with kernel `'H(B)`: the composite
`'M(B) → 'M(B) ⧸ 'H(B) ≃* 'N_L(B) ↪ L` (junk `1` off `calP`, mirroring the Coq's
`trivm` fallback in `Dade_restrm`).  Coq: `Dade_restrm` (`PFsection2.v`). -/
noncomputable def dadeProj (ddA : DadeHypothesis G L A) (B : Finset G) :
    ↥(ddA.setProd B) →* ↥L :=
  if hB : ↑B ⊆ A ∧ B.Nonempty then
    haveI := ddA.normal_setSignalizer_subgroupOf' hB.1
    (Subgroup.inclusion (setNormalizer_le (L := L) (B := B))).comp
      (((Subgroup.subgroupOfEquivOfLe
          (ddA.setNormalizer_le_setProd (B := B))).toMonoidHom).comp
        (((ddA.isComplement'_setProd hB.1 hB.2).QuotientMulEquiv).toMonoidHom.comp
          (QuotientGroup.mk' ((ddA.setSignalizer B).subgroupOf (ddA.setProd B)))))
  else 1

/-- Evaluation of the Dade projection on a factored element: `h * n ↦ n`.
Coq: the `remgrMid` computation inside `Dade_restrictionE`. -/
theorem dadeProj_apply_mul (ddA : DadeHypothesis G L A) {B : Finset G}
    (hB : ↑B ⊆ A ∧ B.Nonempty) {h n : G} (hh : h ∈ ddA.setSignalizer B)
    (hn : n ∈ setNormalizer L B) (hmem : h * n ∈ ddA.setProd B) :
    ddA.dadeProj B ⟨h * n, hmem⟩ = ⟨n, setNormalizer_le hn⟩ := by
  classical
  haveI := ddA.normal_setSignalizer_subgroupOf' hB.1
  set e := (ddA.isComplement'_setProd hB.1 hB.2).QuotientMulEquiv with he
  have hproj : ddA.dadeProj B ⟨h * n, hmem⟩
      = Subgroup.inclusion (setNormalizer_le (L := L) (B := B))
          ((Subgroup.subgroupOfEquivOfLe (ddA.setNormalizer_le_setProd (B := B)))
            (e (QuotientGroup.mk (⟨h * n, hmem⟩ : ↥(ddA.setProd B))))) := by
    rw [dadeProj, dif_pos hB]
    rfl
  have hnPmem : n ∈ ddA.setProd B := ddA.setNormalizer_le_setProd hn
  have hmk : QuotientGroup.mk (s := (ddA.setSignalizer B).subgroupOf (ddA.setProd B))
      (⟨h * n, hmem⟩ : ↥(ddA.setProd B)) = QuotientGroup.mk ⟨n, hnPmem⟩ := by
    rw [QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have hval : (((⟨h * n, hmem⟩ : ↥(ddA.setProd B))⁻¹
        * (⟨n, hnPmem⟩ : ↥(ddA.setProd B)) : ↥(ddA.setProd B)) : G) = n⁻¹ * h⁻¹ * n := by
      show (h * n)⁻¹ * n = n⁻¹ * h⁻¹ * n
      group
    rw [hval]
    have := ddA.conj_mem_setSignalizer hB.1 (inv_mem hn) (inv_mem hh)
    simpa using this
  have hE : e (QuotientGroup.mk (⟨n, hnPmem⟩ : ↥(ddA.setProd B)))
      = ⟨⟨n, hnPmem⟩, Subgroup.mem_subgroupOf.mpr hn⟩ := by
    have hsymm : e.symm ⟨⟨n, hnPmem⟩, Subgroup.mem_subgroupOf.mpr hn⟩
        = QuotientGroup.mk (⟨n, hnPmem⟩ : ↥(ddA.setProd B)) := rfl
    exact ((MulEquiv.symm_apply_eq e).mp hsymm).symm
  rw [hproj, hmk, hE]
  rfl

/-- `'aa_B`: the Dade restriction of `α ∈ 'CF(L)` to `'M(B)` — the pullback of `α` along
the projection `'M(B) → 'N_L(B) ≤ L`, bundled linearly in `α`.
Coq: `Dade_cfun_restriction` (`PFsection2.v`). -/
noncomputable def dadeRestriction (ddA : DadeHypothesis G L A) (B : Finset G) :
    ClassFunction ↥L →ₗ[ℂ] ClassFunction ↥(ddA.setProd B) :=
  ClassFunction.compHom (ddA.dadeProj B)

/-- **`Dade_restrictionE`**: on a factored element, `'aa_B (h * n) = α n`. -/
theorem dadeRestriction_apply_mul (ddA : DadeHypothesis G L A) (α : ClassFunction ↥L)
    {B : Finset G} (hB : ↑B ⊆ A ∧ B.Nonempty) {h n : G} (hh : h ∈ ddA.setSignalizer B)
    (hn : n ∈ setNormalizer L B) (hmem : h * n ∈ ddA.setProd B) :
    ddA.dadeRestriction B α ⟨h * n, hmem⟩ = α ⟨n, setNormalizer_le hn⟩ := by
  rw [dadeRestriction, ClassFunction.compHom_apply, ddA.dadeProj_apply_mul hB hh hn hmem]

open scoped Classical in
/-- **`Dade_restriction_vchar`**: the Dade restriction of a virtual character is a
virtual character. -/
theorem dadeRestriction_isVirtualChar (ddA : DadeHypothesis G L A) [Fintype L]
    (B : Finset G) {α : ClassFunction ↥L} (hα : α.IsVirtualChar) :
    (ddA.dadeRestriction B α).IsVirtualChar := by
  obtain ⟨α₁, α₂, h₁, h₂, rfl⟩ := ClassFunction.isVirtualChar_iff_exists_isChar_sub.mp hα
  rw [dadeRestriction, map_sub]
  exact ClassFunction.IsChar.sub_isVirtualChar
    (h₁.compHom (ddA.dadeProj B)) (h₂.compHom (ddA.dadeProj B))

end Restriction

/-! #### Conjugation transport for the expansion data (Peterfalvi (2.10.1)) -/

section ConjTransport

open scoped Classical

variable [Fintype G]

/-- `'H(B ^ x) = 'H(B) ^ x` for `x ∈ L`, `B ⊆ A`. -/
theorem setSignalizer_image_conj (ddA : DadeHypothesis G L A) {x : G} (hx : x ∈ L)
    {B : Finset G} (hB : ↑B ⊆ A) :
    ddA.setSignalizer (B.image fun b => x * b * x⁻¹)
      = (ddA.setSignalizer B).map (MulAut.conj x).toMonoidHom := by
  ext w
  rw [Subgroup.mem_map_conj_iff, mem_setSignalizer, mem_setSignalizer]
  constructor
  · intro hw b hb
    have hmem := hw (x * b * x⁻¹) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    rw [ddA.signalizer_conj hx (hB hb), Subgroup.mem_map_conj_iff] at hmem
    exact hmem
  · intro hw b' hb'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb'
    rw [ddA.signalizer_conj hx (hB hb), Subgroup.mem_map_conj_iff]
    exact hw b hb

omit [Fintype G] in
/-- Conjugating a `Finset` conjugates its normalizer: membership form. -/
theorem mem_normalizer_image_conj_iff {B : Finset G} {x w : G} :
    w ∈ Subgroup.normalizer (↑(B.image fun b => x * b * x⁻¹) : Set G)
      ↔ x⁻¹ * w * x ∈ Subgroup.normalizer (↑B : Set G) := by
  have hmem : ∀ n : G, n ∈ B.image (fun b => x * b * x⁻¹) ↔ x⁻¹ * n * x ∈ B := by
    intro n
    rw [Finset.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rwa [show x⁻¹ * (x * b * x⁻¹) * x = b by group]
    · intro h
      exact ⟨x⁻¹ * n * x, h, by group⟩
  constructor
  · intro h
    rw [Subgroup.mem_set_normalizer_iff]
    intro m
    have h1 := Subgroup.mem_set_normalizer_iff.mp h (x * m * x⁻¹)
    simp only [Finset.mem_coe, hmem] at h1
    rw [show x⁻¹ * (x * m * x⁻¹) * x = m by group,
      show x⁻¹ * (w * (x * m * x⁻¹) * w⁻¹) * x = (x⁻¹ * w * x) * m * (x⁻¹ * w * x)⁻¹
        by group] at h1
    simpa using h1
  · intro h
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    have h1 := Subgroup.mem_set_normalizer_iff.mp h (x⁻¹ * n * x)
    simp only [Finset.mem_coe] at h1
    rw [show (x⁻¹ * w * x) * (x⁻¹ * n * x) * (x⁻¹ * w * x)⁻¹ = x⁻¹ * (w * n * w⁻¹) * x
      by group] at h1
    simp only [Finset.mem_coe, hmem]
    exact h1

omit [Fintype G] in
/-- `'N_L(B ^ x) = 'N_L(B) ^ x` for `x ∈ L`. -/
theorem setNormalizer_image_conj {L : Subgroup G} {x : G} (hx : x ∈ L) (B : Finset G) :
    setNormalizer L (B.image fun b => x * b * x⁻¹)
      = (setNormalizer L B).map (MulAut.conj x).toMonoidHom := by
  ext w
  rw [Subgroup.mem_map_conj_iff, setNormalizer, setNormalizer, Subgroup.mem_inf,
    Subgroup.mem_inf, mem_normalizer_image_conj_iff]
  constructor
  · rintro ⟨hwL, hwN⟩
    exact ⟨mul_mem (mul_mem (inv_mem hx) hwL) hx, hwN⟩
  · rintro ⟨hwL, hwN⟩
    refine ⟨?_, hwN⟩
    have := mul_mem (mul_mem hx hwL) (inv_mem hx)
    rwa [show x * (x⁻¹ * w * x) * x⁻¹ = w by group] at this

/-- `'M(B ^ x) = 'M(B) ^ x` for `x ∈ L`, `B ⊆ A`. -/
theorem setProd_image_conj (ddA : DadeHypothesis G L A) {x : G} (hx : x ∈ L)
    {B : Finset G} (hB : ↑B ⊆ A) :
    ddA.setProd (B.image fun b => x * b * x⁻¹)
      = (ddA.setProd B).map (MulAut.conj x).toMonoidHom := by
  rw [setProd, setProd, ddA.setSignalizer_image_conj hx hB, setNormalizer_image_conj hx B,
    Subgroup.map_sup]

omit [Fintype G] in
/-- `calP` is stable under `L`-conjugation. -/
theorem image_conj_subset_and_nonempty {x : G} (hx : x ∈ L)
    {A : Set G} (hstab : ∀ y ∈ L, ∀ a ∈ A, y * a * y⁻¹ ∈ A) {B : Finset G} (hB : ↑B ⊆ A)
    (hne : B.Nonempty) :
    ↑(B.image fun b => x * b * x⁻¹) ⊆ A ∧ (B.image fun b => x * b * x⁻¹).Nonempty := by
  constructor
  · intro b' hb'
    rw [Finset.mem_coe, Finset.mem_image] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    exact hstab x hx b (hB hb)
  · exact hne.image _

/-- **Peterfalvi (2.10.1)** (`Dade_Ind_restr_J`): the induced Dade restriction is
invariant under `L`-conjugation of `B`: `Ind_G 'aa_{B^x} = Ind_G 'aa_B` for `x ∈ L`. -/
theorem ind_dadeRestriction_image_conj (ddA : DadeHypothesis G L A) (α : ClassFunction ↥L)
    {x : G} (hx : x ∈ L) {B : Finset G} (hB : ↑B ⊆ A) (hne : B.Nonempty) :
    ClassFunction.ind (ddA.setProd (B.image fun b => x * b * x⁻¹))
        (ddA.dadeRestriction (B.image fun b => x * b * x⁻¹) α)
      = ClassFunction.ind (ddA.setProd B) (ddA.dadeRestriction B α) := by
  set Bx : Finset G := B.image fun b => x * b * x⁻¹ with hBx
  have hBx' : ↑Bx ⊆ A ∧ Bx.Nonempty := by
    constructor
    · intro b' hb'
      rw [hBx, Finset.mem_coe, Finset.mem_image] at hb'
      obtain ⟨b, hb, rfl⟩ := hb'
      exact ddA.conj_mem x hx b (hB hb)
    · exact hne.image _
  have hMx : ddA.setProd Bx = (ddA.setProd B).map (MulAut.conj x).toMonoidHom :=
    ddA.setProd_image_conj hx hB
  -- the values of the two restrictions correspond under conjugation
  have hval : ∀ w : G,
      ClassFunction.extendZero (ddA.dadeRestriction Bx α) w
        = ClassFunction.extendZero (ddA.dadeRestriction B α) (x⁻¹ * w * x) := by
    intro w
    by_cases hw : w ∈ ddA.setProd Bx
    · have hw' : x⁻¹ * w * x ∈ ddA.setProd B := by
        rw [hMx, Subgroup.mem_map_conj_iff] at hw
        exact hw
      rw [ClassFunction.extendZero_apply_of_mem _ hw,
        ClassFunction.extendZero_apply_of_mem _ hw']
      obtain ⟨h, hh, n, hn, hwn⟩ := ddA.exists_mul_of_mem_setProd hB hw'
      have hxh : x * h * x⁻¹ ∈ ddA.setSignalizer Bx := by
        rw [hBx, ddA.setSignalizer_image_conj hx hB, Subgroup.mem_map_conj_iff]
        rwa [show x⁻¹ * (x * h * x⁻¹) * x = h by group]
      have hxn : x * n * x⁻¹ ∈ setNormalizer L Bx := by
        rw [hBx, setNormalizer_image_conj hx B, Subgroup.mem_map_conj_iff]
        rwa [show x⁻¹ * (x * n * x⁻¹) * x = n by group]
      have hwmul : w = (x * h * x⁻¹) * (x * n * x⁻¹) := by
        have : w = x * (x⁻¹ * w * x) * x⁻¹ := by group
        rw [this, hwn]
        group
      have hsub : (⟨w, hw⟩ : ↥(ddA.setProd Bx))
          = ⟨(x * h * x⁻¹) * (x * n * x⁻¹), hwmul ▸ hw⟩ := Subtype.ext hwmul
      have hsub' : (⟨x⁻¹ * w * x, hw'⟩ : ↥(ddA.setProd B))
          = ⟨h * n, hwn ▸ hw'⟩ := Subtype.ext hwn
      rw [hsub, hsub', ddA.dadeRestriction_apply_mul α hBx' hxh hxn _,
        ddA.dadeRestriction_apply_mul α ⟨hB, hne⟩ hh hn _]
      -- `α (x n x⁻¹) = α n` since `α` is a class function of `L`
      have hxL : (⟨x * n * x⁻¹, setNormalizer_le hxn⟩ : ↥L)
          = ⟨x, hx⟩ * ⟨n, setNormalizer_le hn⟩ * (⟨x, hx⟩ : ↥L)⁻¹ := by
        ext
        push_cast
        rfl
      rw [hxL, ClassFunction.conj_apply]
    · have hw' : x⁻¹ * w * x ∉ ddA.setProd B := by
        intro hmem
        apply hw
        rw [hMx, Subgroup.mem_map_conj_iff]
        exact hmem
      rw [ClassFunction.extendZero_apply_of_not_mem _ hw,
        ClassFunction.extendZero_apply_of_not_mem _ hw']
  -- compare the two averaging sums
  ext g
  rw [ClassFunction.ind_apply, ClassFunction.ind_apply]
  have hcard : Nat.card (ddA.setProd Bx) = Nat.card (ddA.setProd B) := by
    rw [hMx]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj x).injective).toEquiv).symm
  rw [hcard]
  congr 1
  calc ∑ z : G, ClassFunction.extendZero (ddA.dadeRestriction Bx α) (z⁻¹ * g * z)
      = ∑ z : G, ClassFunction.extendZero (ddA.dadeRestriction B α)
          (x⁻¹ * (z⁻¹ * g * z) * x) := by
        exact Finset.sum_congr rfl fun z _ => hval _
    _ = ∑ z : G, ClassFunction.extendZero (ddA.dadeRestriction B α) (z⁻¹ * g * z) := by
        refine Fintype.sum_equiv (Equiv.mulRight x) _ _ fun z => ?_
        simp only [Equiv.coe_mulRight]
        congr 1
        group

end ConjTransport

end DadeHypothesis

end SetSignalizer

end PF2
