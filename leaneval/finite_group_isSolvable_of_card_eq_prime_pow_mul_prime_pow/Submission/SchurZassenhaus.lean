/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Solvable

/-!
# Schur–Zassenhaus conjugacy for solvable kernels

Mathlib proves the existence half of the Schur–Zassenhaus theorem
(`Subgroup.exists_right_complement'_of_coprime`).  This file proves the
conjugacy half in the case where the normal subgroup is solvable: if `N` is a
finite solvable normal subgroup whose order is coprime to its index, then any
two complements of `N` are conjugate.

## Main results

* `Subgroup.IsComplement'.exists_conj_of_coprime`: **Schur–Zassenhaus
  conjugacy, solvable case**.  Corresponds to MathComp's
  `SchurZassenhaus_trans_sol`.

## Proof outline

Strong induction on `Nat.card N`.  If `N` is abelian, complements of `N` are
exactly the stabilizers of points of `N.QuotientDiff` (Mathlib's internal
transversal quotient from the existence proof): every complement `C` fixes its
own class in `N.QuotientDiff` and has the right cardinality by
`Subgroup.isComplement'_stabilizer_of_coprime`, and the action of `N` on
`N.QuotientDiff` is transitive (`Subgroup.exists_smul_eq`), so any two
complements are conjugate by an element of `N`.  If `N` is not abelian, then
`N' := ⁅N, N⁆` is a proper nontrivial subgroup of `N` that is normal in `G`;
the images of the complements in `G ⧸ N'` are conjugate by induction, and
after adjusting by that conjugation the two complements are complements of
`N'` inside the preimage `M` of the common image, hence conjugate by
induction again.

The file also contains general subgroup/cardinality helpers used by this
induction and by the Hall conjugacy theorems in
`OddOrder.Mathlib.GroupTheory.Hall`.
-/

namespace Subgroup

section Card

variable {G : Type*} [Group G]

/-- A proper subgroup of a finite group has strictly smaller order. -/
theorem card_lt_card_of_ne_top [Finite G] {K : Subgroup G} (hK : K ≠ ⊤) :
    Nat.card K < Nat.card G := by
  conv_rhs => rw [← K.card_mul_index]
  exact (lt_mul_iff_one_lt_right Nat.card_pos).mpr (one_lt_index_of_ne_top hK)

/-- The quotient of a finite group by a nontrivial subgroup is strictly smaller. -/
theorem card_quotient_lt_card_of_ne_bot [Finite G] {N : Subgroup G} (hN : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  conv_rhs => rw [card_eq_card_quotient_mul_card_subgroup N]
  exact (lt_mul_iff_one_lt_right Nat.card_pos).mpr (N.one_lt_card_iff_ne_bot.mpr hN)

/-- The preimage under `QuotientGroup.mk'` of a subgroup `H ≤ G ⧸ N` has order
`Nat.card N * Nat.card H`. -/
theorem card_comap_mk' (N : Subgroup G) [N.Normal] (H : Subgroup (G ⧸ N)) :
    Nat.card (H.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card H :=
  (Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet N H)).trans (Nat.card_prod _ _)

/-- Viewing a subgroup `H ≤ M` as a subgroup of `M` does not change its order. -/
theorem card_subgroupOf {H M : Subgroup G} (h : H ≤ M) :
    Nat.card (H.subgroupOf M) = Nat.card H :=
  Nat.card_congr (subgroupOfEquivOfLe h).toEquiv

/-- A subgroup meeting the kernel of `f` trivially has the same order as its image. -/
theorem card_map_of_disjoint_ker {G' : Type*} [Group G'] {f : G →* G'} {K : Subgroup G}
    (h : Disjoint f.ker K) : Nat.card (K.map f) = Nat.card K := by
  have hinj : Function.Injective (f.restrict K) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_restrict, subgroupOf_eq_bot]
    exact h
  rw [← MonoidHom.restrict_range]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Card

section Solvable

variable {G : Type*} [Group G]

/-- A subgroup contained in a solvable subgroup is solvable. -/
theorem isSolvable_of_le {H K : Subgroup G} (hK : IsSolvable K) (hle : H ≤ K) :
    IsSolvable H := by
  haveI := hK
  exact solvable_of_surjective (f := (subgroupOfEquivOfLe hle).toMonoidHom)
    (subgroupOfEquivOfLe hle).surjective

end Solvable

section Conj

variable {G : Type*} [Group G]

/-- Two successive conjugations are a conjugation by the product. -/
theorem map_conj_map_conj (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom
      = H.map (MulAut.conj (b * a)).toMonoidHom := by
  have h : (MulAut.conj b).toMonoidHom.comp (MulAut.conj a).toMonoidHom
      = (MulAut.conj (b * a)).toMonoidHom :=
    MonoidHom.ext fun x => by simp [MulAut.conj_apply, mul_assoc]
  rw [map_map, h]

/-- Conjugation commutes with taking images in a quotient group. -/
theorem map_conj_map_mk' (N : Subgroup G) [N.Normal] (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' N)
      = (H.map (QuotientGroup.mk' N)).map
        (MulAut.conj (QuotientGroup.mk' N g)).toMonoidHom := by
  have h : (QuotientGroup.mk' N).comp (MulAut.conj g).toMonoidHom
      = (MulAut.conj (QuotientGroup.mk' N g)).toMonoidHom.comp (QuotientGroup.mk' N) :=
    MonoidHom.ext fun x => by simp [MulAut.conj_apply]
  rw [map_map, map_map, h]

/-- Conjugating `X.subgroupOf M` by `m : M` and passing back to `G` is conjugating `X`
by `(m : G)`. -/
theorem map_conj_subgroupOf_map_subtype {M X : Subgroup G} (hX : X ≤ M) (m : M) :
    ((X.subgroupOf M).map (MulAut.conj m).toMonoidHom).map M.subtype
      = X.map (MulAut.conj (m : G)).toMonoidHom := by
  have h : M.subtype.comp (MulAut.conj m).toMonoidHom
      = (MulAut.conj (m : G)).toMonoidHom.comp M.subtype :=
    MonoidHom.ext fun x => by simp [MulAut.conj_apply]
  rw [map_map, h, ← map_map, subgroupOf_map_subtype, inf_of_le_left hX]

/-- Push an equality of conjugate subgroups of `M` down to `G`. -/
theorem eq_map_conj_of_subgroupOf_eq_map_conj {M X Y : Subgroup G} (hX : X ≤ M) (hY : Y ≤ M)
    {m : M} (h : Y.subgroupOf M = (X.subgroupOf M).map (MulAut.conj m).toMonoidHom) :
    Y = X.map (MulAut.conj (m : G)).toMonoidHom := by
  have hmap := congrArg (map M.subtype) h
  rwa [subgroupOf_map_subtype, inf_of_le_left hY, map_conj_subgroupOf_map_subtype hX] at hmap

/-- Push an inclusion into a conjugate subgroup of `M` down to `G`. -/
theorem le_map_conj_of_subgroupOf_le_map_conj {M X Y : Subgroup G} (hX : X ≤ M) (hY : Y ≤ M)
    {m : M} (h : Y.subgroupOf M ≤ (X.subgroupOf M).map (MulAut.conj m).toMonoidHom) :
    Y ≤ X.map (MulAut.conj (m : G)).toMonoidHom := by
  have hmap := map_mono (f := M.subtype) h
  rwa [subgroupOf_map_subtype, inf_of_le_left hY, map_conj_subgroupOf_map_subtype hX] at hmap

end Conj

section Complement

variable {G : Type*} [Group G]

/-- A complement of `N` meets every intermediate subgroup `N ≤ L` in a complement of `N`
inside `L`. -/
theorem IsComplement'.inf_subgroupOf {N K L : Subgroup G} (h : IsComplement' N K)
    (hNL : N ≤ L) : IsComplement' (N.subgroupOf L) ((K ⊓ L).subgroupOf L) := by
  have h' := isComplement_iff_existsUnique_inv_mul_mem.mp h
  rw [isComplement'_def, isComplement_iff_existsUnique_inv_mul_mem]
  intro l
  obtain ⟨n, hn, huniq⟩ := h' (l : G)
  have hnL : (n : G) ∈ L := hNL n.2
  refine ⟨⟨⟨(n : G), hnL⟩, mem_subgroupOf.mpr n.2⟩, ?_, ?_⟩
  · exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hn, L.mul_mem (L.inv_mem hnL) l.2⟩)
  · rintro ⟨s, hs⟩ hprop
    have hsK : (s : G)⁻¹ * (l : G) ∈ K := (mem_inf.mp (mem_subgroupOf.mp hprop)).1
    have heq := huniq ⟨(s : G), mem_subgroupOf.mp hs⟩ hsK
    have hval : (s : G) = (n : G) := Subtype.ext_iff.mp heq
    exact Subtype.ext (Subtype.ext hval)

end Complement

/-!
### Schur–Zassenhaus conjugacy, solvable case

The abelian base case reuses Mathlib's `Subgroup.QuotientDiff` machinery from the
existence proof: for coprime order and index, `Subgroup.isComplement'_stabilizer_of_coprime`
shows stabilizers of transversal classes are complements, and every complement is such a
stabilizer (of its own class).  Transitivity of the `N`-action
(`Subgroup.exists_smul_eq`) then conjugates any complement to any other.
-/

section SchurZassenhaus

open MulAction MulOpposite

open scoped Pointwise commutatorElement

universe u

variable {G : Type*} [Group G]

private theorem exists_conj_of_coprime_of_isMulCommutative [Finite G] {N H K : Subgroup G}
    [N.Normal] [IsMulCommutative N] (hco : (Nat.card N).Coprime N.index)
    (hH : IsComplement' N H) (hK : IsComplement' N K) :
    ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
  -- The action of `G` on `N.QuotientDiff`, computed on the class of a transversal.
  -- NB: this `rfl` relies on a defeq of Mathlib's `MulAction G H.QuotientDiff` instance
  -- (`Quotient.map'` computing on `Quotient.mk''`); if a Mathlib bump breaks it,
  -- re-prove via `Quotient.map'_mk''`.
  have hact : ∀ (c : G) (q : N.QuotientDiff) (β : N.LeftTransversal), q = Quotient.mk'' β →
      c • q = Quotient.mk'' (op c⁻¹ • β) := by
    rintro c q β rfl
    rfl
  -- Every complement `C` of `N` is the stabilizer of its own class in `N.QuotientDiff`.
  have key : ∀ {C : Subgroup G} (hC : IsComplement' N C) (q : N.QuotientDiff),
      q = Quotient.mk'' ⟨(C : Set G), isComplement'_def.mp hC.symm⟩ →
      stabilizer G q = C := by
    intro C hC q hq
    have hle : C ≤ stabilizer G q := by
      intro c hc
      have hset : op c⁻¹ • (⟨(C : Set G), isComplement'_def.mp hC.symm⟩ : N.LeftTransversal)
          = ⟨(C : Set G), isComplement'_def.mp hC.symm⟩ := by
        refine Subtype.ext ?_
        change op c⁻¹ • (C : Set G) = (C : Set G)
        ext x
        rw [Set.mem_smul_set]
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [op_smul_eq_mul]
          exact C.mul_mem hy (C.inv_mem hc)
        · intro hx
          exact ⟨x * c, C.mul_mem hx hc, by rw [op_smul_eq_mul, mul_inv_cancel_right]⟩
      rw [mem_stabilizer_iff, hact c q _ hq, hset, ← hq]
    have hstab : IsComplement' N (stabilizer G q) := isComplement'_stabilizer_of_coprime hco
    refine (eq_of_le_of_card_ge hle (le_of_eq ?_)).symm
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hstab.card_mul.trans hC.card_mul.symm)
  -- Transitivity of the `N`-action conjugates one stabilizer to the other.
  obtain ⟨qH, hqH⟩ : ∃ q : N.QuotientDiff,
      q = Quotient.mk'' ⟨(H : Set G), isComplement'_def.mp hH.symm⟩ := ⟨_, rfl⟩
  obtain ⟨qK, hqK⟩ : ∃ q : N.QuotientDiff,
      q = Quotient.mk'' ⟨(K : Set G), isComplement'_def.mp hK.symm⟩ := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ := exists_smul_eq hco qH qK
  refine ⟨(n : G), ?_⟩
  rw [← key hK qK hqK, ← hn, smul_def, stabilizer_smul_eq_stabilizer_map_conj, key hH qH hqH]

/-- Auxiliary strong induction on `Nat.card N` for
`Subgroup.IsComplement'.exists_conj_of_coprime`, phrased with an explicit bound `n` so that
the induction hypothesis applies to quotients of `G` and subgroups of `G` (which live in
different types). -/
private theorem exists_conj_of_coprime_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], ∀ {N H K : Subgroup G} [N.Normal] [IsSolvable N],
      Nat.card N ≤ n → (Nat.card N).Coprime N.index →
      IsComplement' N H → IsComplement' N K →
      ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
  induction n with
  | zero =>
    intro G _ _ N H K _ _ hn
    exact absurd (Nat.le_zero.mp hn) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ N H K _ _ hn hco hH hK
    by_cases habel : ⁅N, N⁆ = ⊥
    -- Base case: `N` abelian.
    · haveI : IsMulCommutative N := ⟨⟨fun a b => Subtype.ext <| by
        have h1 : ⁅(a : G), (b : G)⁆ ∈ ⁅N, N⁆ := commutator_mem_commutator a.2 b.2
        rw [habel, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1⟩⟩
      exact exists_conj_of_coprime_of_isMulCommutative hco hH hK
    -- Inductive case: `N' := ⁅N, N⁆` is proper, nontrivial and normal in `G`.
    · obtain ⟨N', hN'⟩ : ∃ N', N' = ⁅N, N⁆ := ⟨_, rfl⟩
      haveI hN'normal : N'.Normal := hN' ▸ commutator_normal N N
      have hN'le : N' ≤ N := hN' ▸ commutator_le.mpr fun a ha b hb =>
        N.mul_mem (N.mul_mem (N.mul_mem ha hb) (N.inv_mem ha)) (N.inv_mem hb)
      have hN'ne : N' ≠ ⊥ := hN' ▸ habel
      have hNne : N ≠ ⊥ := fun h => hN'ne (le_bot_iff.mp (h ▸ hN'le))
      haveI : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hNne
      have hN'lt : N' < N := by
        rw [hN', ← N.range_subtype, MonoidHom.range_eq_map, ← map_commutator,
          map_subtype_lt_map_subtype]
        exact IsSolvable.commutator_lt_top_of_nontrivial ↥N
      -- Complement bookkeeping.
      have hkerφ : (QuotientGroup.mk' N').ker = N' := QuotientGroup.ker_mk' N'
      have hdisjH : Disjoint (QuotientGroup.mk' N').ker H := by
        rw [hkerφ]; exact hH.disjoint.mono_left hN'le
      have hdisjK : Disjoint (QuotientGroup.mk' N').ker K := by
        rw [hkerφ]; exact hK.disjoint.mono_left hN'le
      have hHidx : Nat.card H = N.index := hH.symm.index_eq_card.symm
      have hKidx : Nat.card K = N.index := hK.symm.index_eq_card.symm
      have hcardN : Nat.card N = Nat.card N' * Nat.card (N.map (QuotientGroup.mk' N')) := by
        rw [← card_comap_mk' N' (N.map (QuotientGroup.mk' N')), comap_map_eq, hkerφ,
          sup_of_le_left hN'le]
      have hcardG : Nat.card N' * Nat.card (G ⧸ N') = Nat.card G := by
        rw [card_eq_card_quotient_mul_card_subgroup N', mul_comm]
      -- Step 1: the images in `G ⧸ N'` are complements of `N.map (mk' N')`.
      have himg : ∀ {C : Subgroup G}, IsComplement' N C →
          Disjoint (QuotientGroup.mk' N').ker C → Nat.card C = N.index →
          IsComplement' (N.map (QuotientGroup.mk' N')) (C.map (QuotientGroup.mk' N')) := by
        intro C hC hdisj hCidx
        have hCcard : Nat.card (C.map (QuotientGroup.mk' N')) = N.index := by
          rw [card_map_of_disjoint_ker hdisj, hCidx]
        refine isComplement'_of_coprime (Nat.eq_of_mul_eq_mul_left
          (Nat.card_pos (α := N')) ?_) ?_
        · rw [← mul_assoc, ← hcardN, card_map_of_disjoint_ker hdisj, hC.card_mul, hcardG]
        · have h1 := hco.coprime_dvd_left (N.card_map_dvd (QuotientGroup.mk' N'))
          rwa [← hCcard] at h1
      haveI : (N.map (QuotientGroup.mk' N')).Normal :=
        Normal.map ‹N.Normal› _ (QuotientGroup.mk'_surjective N')
      haveI : IsSolvable (N.map (QuotientGroup.mk' N')) :=
        solvable_of_surjective ((QuotientGroup.mk' N').subgroupMap_surjective N)
      have hbarbound : Nat.card (N.map (QuotientGroup.mk' N')) ≤ n := by
        have hlt : Nat.card (N.map (QuotientGroup.mk' N')) < Nat.card N := by
          conv_rhs => rw [hcardN]
          exact (lt_mul_iff_one_lt_left Nat.card_pos).mpr (N'.one_lt_card_iff_ne_bot.mpr hN'ne)
        omega
      have hcobar : (Nat.card (N.map (QuotientGroup.mk' N'))).Coprime
          (N.map (QuotientGroup.mk' N')).index := by
        rw [(himg hH hdisjH hHidx).symm.index_eq_card, card_map_of_disjoint_ker hdisjH, hHidx]
        exact hco.coprime_dvd_left (N.card_map_dvd (QuotientGroup.mk' N'))
      -- Step 2: conjugate the images in the quotient, and lift the conjugating element.
      obtain ⟨gbar, hgbar⟩ := ih (G ⧸ N') hbarbound hcobar
        (himg hH hdisjH hHidx) (himg hK hdisjK hKidx)
      obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective N' gbar
      have hconjinj : Function.Injective (MulAut.conj g₁).toMonoidHom :=
        (MulAut.conj g₁).injective
      have hH₁card : Nat.card (H.map (MulAut.conj g₁).toMonoidHom) = N.index := by
        rw [card_map_of_injective hconjinj, hHidx]
      have hH₁bar : (H.map (MulAut.conj g₁).toMonoidHom).map (QuotientGroup.mk' N')
          = K.map (QuotientGroup.mk' N') :=
        (map_conj_map_mk' N' H g₁).trans hgbar.symm
      -- Step 3: `H.map (conj g₁)` and `K` are complements of `N'` inside the preimage `M`
      -- of the common image; conclude by induction on `Nat.card N'`.
      set M := (K.map (QuotientGroup.mk' N')).comap (QuotientGroup.mk' N') with hMdef
      have hKM : K ≤ M := by
        rw [hMdef]; exact le_comap_map _ K
      have hH₁M : H.map (MulAut.conj g₁).toMonoidHom ≤ M := by
        rw [hMdef, ← hH₁bar]; exact le_comap_map _ _
      have hN'M : N' ≤ M := by
        rw [hMdef]; exact hkerφ.symm.trans_le (ker_le_comap _ _)
      have hMcard : Nat.card M = Nat.card N' * N.index := by
        rw [hMdef, card_comap_mk', card_map_of_disjoint_ker hdisjK, hKidx]
      have hsub : ∀ {C : Subgroup G}, C ≤ M → Nat.card C = N.index →
          IsComplement' (N'.subgroupOf M) (C.subgroupOf M) := by
        intro C hCM hCcard
        refine isComplement'_of_coprime ?_ ?_
        · rw [card_subgroupOf hN'M, card_subgroupOf hCM, hCcard, hMcard]
        · rw [card_subgroupOf hN'M, card_subgroupOf hCM, hCcard]
          exact hco.coprime_dvd_left (card_dvd_of_le hN'le)
      haveI : IsSolvable N' := isSolvable_of_le ‹IsSolvable N› hN'le
      haveI : IsSolvable (N'.subgroupOf M) :=
        solvable_of_solvable_injective (f := (subgroupOfEquivOfLe hN'M).toMonoidHom)
          (subgroupOfEquivOfLe hN'M).injective
      have hcoM : (Nat.card (N'.subgroupOf M)).Coprime (N'.subgroupOf M).index := by
        rw [(hsub hKM hKidx).symm.index_eq_card, card_subgroupOf hN'M, card_subgroupOf hKM,
          hKidx]
        exact hco.coprime_dvd_left (card_dvd_of_le hN'le)
      have hMbound : Nat.card (N'.subgroupOf M) ≤ n := by
        rw [card_subgroupOf hN'M]
        have hlt : Nat.card N' < Nat.card N :=
          lt_of_le_of_ne (card_le_of_le hN'le) fun h =>
            hN'lt.ne (eq_of_le_of_card_ge hN'le h.ge)
        omega
      obtain ⟨m, hm⟩ := ih M hMbound hcoM (hsub hH₁M hH₁card) (hsub hKM hKidx)
      refine ⟨(m : G) * g₁, ?_⟩
      rw [← map_conj_map_conj H g₁ (m : G)]
      exact eq_map_conj_of_subgroupOf_eq_map_conj hH₁M hKM hm

/-- **Schur–Zassenhaus conjugacy, solvable case**: if `N` is a finite solvable normal
subgroup whose order is coprime to its index, then any two complements of `N` are
conjugate.

This corresponds to MathComp's `SchurZassenhaus_trans_sol`. -/
theorem IsComplement'.exists_conj_of_coprime [Finite G] {N H K : Subgroup G} [N.Normal]
    [IsSolvable N] (hco : (Nat.card N).Coprime N.index)
    (hH : IsComplement' N H) (hK : IsComplement' N K) :
    ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom :=
  exists_conj_of_coprime_aux (Nat.card N) G le_rfl hco hH hK

end SchurZassenhaus

end Subgroup
