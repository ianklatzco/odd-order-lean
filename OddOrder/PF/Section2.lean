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

end DadeHypothesis

end PF2
