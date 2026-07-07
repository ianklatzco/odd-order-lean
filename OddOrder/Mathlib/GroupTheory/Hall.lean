/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import OddOrder.Mathlib.GroupTheory.ChiefFactor
import OddOrder.Mathlib.GroupTheory.PiGroup
import OddOrder.Mathlib.GroupTheory.SchurZassenhaus

/-!
# Hall π-subgroups

A subgroup `H` of `G` is a *Hall π-subgroup* if `H` is a π-group and the index
of `H` in `G` is a π'-number, that is, no prime factor of `H.index` lies in `π`.
For a finite group this is equivalent to `Nat.card H` and `H.index` being
coprime with `H` a π-group; Sylow p-subgroups are exactly the Hall
`{p}`-subgroups.

## Main definitions

* `Subgroup.IsHall π H`: `H` is a Hall π-subgroup.

## Main results

* `Subgroup.IsHall.coprime`: the order and index of a Hall subgroup are coprime.
* `Sylow.isHall`: a Sylow p-subgroup is a Hall `{p}`-subgroup.
* `Subgroup.IsHall.map`: the Hall property is preserved by group isomorphisms,
  in particular by conjugation (`Subgroup.IsHall.conj`).
* `Subgroup.exists_isHall`: **P. Hall's existence theorem** (1928): a finite
  solvable group has a Hall π-subgroup for every set of primes `π`.
* `Subgroup.isHall_conj`: **P. Hall's conjugacy theorem**: two Hall π-subgroups
  of a finite solvable group are conjugate.
* `Subgroup.IsPiGroup.le_isHall_conj`: **P. Hall's covering theorem**: in a
  finite solvable group, every π-subgroup is contained in a conjugate of any
  Hall π-subgroup.

This corresponds to MathComp's `pHall` (`π.-Hall(G) H`) with `G := ⊤` and
`Hall_exists`, `Hall_trans`, `Hall_superset`.
-/

namespace Subgroup

variable {G G' : Type*} [Group G] [Group G'] {π : Set ℕ} {H : Subgroup G}

/-- `H` is a *Hall π-subgroup*: a π-group whose index is a π'-number. -/
def IsHall (π : Set ℕ) (H : Subgroup G) : Prop :=
  Nat.IsPiNumber π (Nat.card H) ∧ ∀ p ∈ H.index.primeFactors, p ∉ π

/-- A Hall π-subgroup is a π-group. -/
theorem IsHall.isPiGroup (h : H.IsHall π) : H.IsPiGroup π :=
  h.1

/-- The order and index of a Hall subgroup of a finite group are coprime. -/
theorem IsHall.coprime [Finite G] (h : H.IsHall π) : (Nat.card H).Coprime H.index :=
  h.1.coprime h.2 Nat.card_pos.ne' index_ne_zero_of_finite

@[simp]
theorem isHall_top_iff : (⊤ : Subgroup G).IsHall π ↔ Nat.IsPiNumber π (Nat.card G) := by
  simp [IsHall, index_top]

/-- The Hall property is preserved by group isomorphisms. -/
theorem IsHall.map (h : H.IsHall π) (e : G ≃* G') : (H.map e.toMonoidHom).IsHall π := by
  have hcard : Nat.card (H.map e.toMonoidHom) = Nat.card H :=
    card_map_of_injective e.injective
  have hindex : (H.map e.toMonoidHom).index = H.index := index_map_equiv H e
  exact ⟨hcard ▸ h.1, hindex ▸ h.2⟩

/-- The Hall property is preserved by conjugation. -/
theorem IsHall.conj (h : H.IsHall π) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).IsHall π :=
  h.map (MulAut.conj g)

end Subgroup

namespace Sylow

variable {G : Type*} [Group G] {p : ℕ}

/-- A Sylow p-subgroup of a finite group is a Hall `{p}`-subgroup. -/
theorem isHall [Finite G] [Fact p.Prime] (P : Sylow p G) : (P : Subgroup G).IsHall {p} := by
  constructor
  · intro q hq
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [hn] at hq
    have hq' := Nat.prime_of_mem_primeFactors hq
    exact (Nat.prime_dvd_prime_iff_eq hq' Fact.out).mp
      (hq'.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq))
  · intro q hq hqp
    rw [Set.mem_singleton_iff] at hqp
    subst hqp
    exact P.not_dvd_index (Nat.dvd_of_mem_primeFactors hq)

end Sylow

/-!
### P. Hall's existence theorem

Every finite solvable group has a Hall π-subgroup, by strong induction on the
group order (Hall 1928): pick a minimal normal subgroup `N`, an elementary
abelian `p`-group. If `p ∈ π`, pull a Hall π-subgroup of `G ⧸ N` back to `G`.
If `p ∉ π`, the pullback `K` of a Hall π-subgroup of `G ⧸ N` either is proper,
and a Hall π-subgroup of `K` works, or equals `G`, in which case `N` is a
normal Hall π'-subgroup and a Schur–Zassenhaus complement of `N` works.
-/

namespace Subgroup

universe u

/-- Auxiliary induction for `Subgroup.exists_isHall`: strong induction on `Nat.card G`,
phrased with an explicit bound `n` so that the induction hypothesis can be applied to
the quotients and subgroups (which live in different types) arising in the proof. -/
private theorem exists_isHall_aux (π : Set ℕ) (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G] [IsSolvable G],
      Nat.card G ≤ n → ∃ H : Subgroup G, H.IsHall π := by
  induction n with
  | zero =>
    intro G _ _ _ hG
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ _ hG
    rcases subsingleton_or_nontrivial G with hG₁ | hG₁
    -- Trivial group: `⊤` is a Hall π-subgroup.
    · have h1 : Nat.card G = 1 := Nat.card_unique
      exact ⟨⊤, isHall_top_iff.mpr (by rw [h1]; exact Nat.isPiNumber_one)⟩
    -- Take a minimal normal subgroup `N`; it is an elementary abelian `p`-group,
    -- so its order is `p ^ k`.
    obtain ⟨N, hN⟩ := exists_isMinNormal G
    haveI := hN.normal
    obtain ⟨p, hp, hpN⟩ := hN.isElementaryAbelian
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpN.isPGroup
    -- The quotient `G ⧸ N` is strictly smaller, so by induction it has a Hall
    -- π-subgroup `Hbar`; let `K` be the preimage of `Hbar` in `G`.
    obtain ⟨Hbar, hHbar⟩ := ih (G ⧸ N)
      (Nat.le_of_lt_succ ((card_quotient_lt_card_of_ne_bot hN.ne_bot).trans_le hG))
    obtain ⟨K, hK⟩ : ∃ K, K = Hbar.comap (QuotientGroup.mk' N) := ⟨_, rfl⟩
    have hKindex : K.index = Hbar.index := by
      rw [hK]
      exact Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective N)
    by_cases hpπ : p ∈ π
    -- Case `p ∈ π`: `K` is a Hall π-subgroup of `G`, since
    -- `Nat.card K = p ^ k * Nat.card Hbar` is a π-number and `K.index = Hbar.index`
    -- is a π'-number.
    · refine ⟨K, ?_, ?_⟩
      · show Nat.IsPiNumber π (Nat.card K)
        rw [hK, card_comap_mk', hk]
        exact ((hp.isPiNumber hpπ).pow k).mul hHbar.1
      · intro q hq
        rw [hKindex] at hq
        exact hHbar.2 q hq
    · by_cases hKtop : K = ⊤
      -- Case `p ∉ π` and `K = ⊤`: then `Hbar = ⊤`, so `G ⧸ N` is a π-group and `N`
      -- is a normal Hall π'-subgroup; a Schur–Zassenhaus complement `H` of `N` has
      -- π-number order `N.index` and π'-number index `Nat.card N = p ^ k`.
      · have hHtop : Hbar = ⊤ := by
          rw [← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Hbar, ← hK,
            hKtop, map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
        have hNindex : Nat.IsPiNumber π N.index := by
          rw [index_eq_card]
          exact isHall_top_iff.mp (hHtop ▸ hHbar)
        have hNcard : Nat.IsPiNumber πᶜ (Nat.card N) := by
          rw [hk]
          exact (hp.isPiNumber hpπ).pow k
        obtain ⟨H, hH⟩ := exists_right_complement'_of_coprime
          (hNindex.coprime hNcard index_ne_zero_of_finite Nat.card_pos.ne').symm
        refine ⟨H, ?_, ?_⟩
        · show Nat.IsPiNumber π (Nat.card H)
          rw [← hH.symm.index_eq_card]
          exact hNindex
        · intro q hq
          rw [hH.index_eq_card] at hq
          exact hNcard q hq
      -- Case `p ∉ π` and `K ≠ ⊤`: `K` is strictly smaller than `G`, so by induction
      -- it has a Hall π-subgroup `H`, which is also one of `G` because
      -- `(H.map K.subtype).index = H.index * K.index` is a π'-number.
      · obtain ⟨H, hH⟩ := ih K
          (Nat.le_of_lt_succ ((card_lt_card_of_ne_top hKtop).trans_le hG))
        refine ⟨H.map K.subtype, ?_, ?_⟩
        · show Nat.IsPiNumber π (Nat.card (H.map K.subtype))
          rw [card_subtype]
          exact hH.1
        · change Nat.IsPiNumber πᶜ (H.map K.subtype).index
          rw [index_map_subtype, hKindex]
          exact Nat.IsPiNumber.mul (fun q hq => hH.2 q hq) (fun q hq => hHbar.2 q hq)

/-- **P. Hall's existence theorem** (1928): a finite solvable group has a Hall
π-subgroup for every set of primes `π`.

This corresponds to MathComp's `Hall_exists`. -/
theorem exists_isHall (π : Set ℕ) (G : Type*) [Group G] [Finite G] [IsSolvable G] :
    ∃ H : Subgroup G, H.IsHall π :=
  exists_isHall_aux π (Nat.card G) G le_rfl

/-!
### P. Hall's conjugacy and covering theorems

Same bounded induction on `Nat.card G` as for existence (Gorenstein 6.4.1): pick a
minimal normal subgroup `N`, an elementary abelian `p`-group; conjugate the images in
`G ⧸ N` by induction, so that after replacing `H` by a conjugate the two subgroups have
the same image; let `M` be the preimage of the common image.  If `p ∈ π` then `M` is a
π-group and both Hall π-subgroups equal `M` by maximality (`IsHall.eq_of_le`).  If
`p ∉ π` and `M` is proper, induct inside `M`.  If `p ∉ π` and `M = G`, both subgroups
are complements of `N` (order and disjointness), and Schur–Zassenhaus conjugacy
(`IsComplement'.exists_conj_of_coprime`) applies.
-/

section Conjugacy

variable {G : Type*} [Group G] {π : Set ℕ}

/-- The image of a Hall π-subgroup in a quotient is a Hall π-subgroup of the quotient. -/
theorem IsHall.map_mk' [Finite G] {H : Subgroup G} (h : H.IsHall π) (N : Subgroup G)
    [N.Normal] : (H.map (QuotientGroup.mk' N)).IsHall π := by
  have h2 : Nat.IsPiNumber πᶜ H.index := h.2
  constructor
  · show Nat.IsPiNumber π (Nat.card (H.map (QuotientGroup.mk' N)))
    exact h.1.of_dvd (H.card_map_dvd (QuotientGroup.mk' N)) Nat.card_pos.ne'
  · change Nat.IsPiNumber πᶜ (H.map (QuotientGroup.mk' N)).index
    exact h2.of_dvd (H.index_map_dvd (QuotientGroup.mk'_surjective N)) index_ne_zero_of_finite

/-- A Hall π-subgroup of `G` contained in a subgroup `M` is a Hall π-subgroup of `M`. -/
theorem IsHall.subgroupOf [Finite G] {H M : Subgroup G} (h : H.IsHall π) (hle : H ≤ M) :
    (H.subgroupOf M).IsHall π := by
  have h2 : Nat.IsPiNumber πᶜ H.index := h.2
  constructor
  · show Nat.IsPiNumber π (Nat.card (H.subgroupOf M))
    rw [card_subgroupOf hle]
    exact h.1
  · change Nat.IsPiNumber πᶜ (H.subgroupOf M).index
    exact h2.of_dvd (relIndex_dvd_index_of_le hle) index_ne_zero_of_finite

/-- Hall π-subgroups are maximal π-subgroups: a Hall π-subgroup contained in a π-subgroup
`M` equals `M`. -/
theorem IsHall.eq_of_le [Finite G] {H M : Subgroup G} (h : H.IsHall π) (hle : H ≤ M)
    (hM : M.IsPiGroup π) : H = M := by
  have hsub := h.subgroupOf hle
  have h2 : Nat.IsPiNumber πᶜ (H.subgroupOf M).index := hsub.2
  have hdvd : (H.subgroupOf M).index ∣ Nat.card M :=
    ⟨Nat.card (H.subgroupOf M), ((H.subgroupOf M).index_mul_card).symm⟩
  have hπ : Nat.IsPiNumber π (H.subgroupOf M).index :=
    Nat.IsPiNumber.of_dvd hM hdvd Nat.card_pos.ne'
  -- The relative index is both a π-number and a π'-number, hence `1`.
  have hgcd : Nat.gcd (H.subgroupOf M).index (H.subgroupOf M).index = 1 :=
    hπ.coprime h2 index_ne_zero_of_finite index_ne_zero_of_finite
  rw [Nat.gcd_self] at hgcd
  exact le_antisymm hle (subgroupOf_eq_top.mp (index_eq_one.mp hgcd))

/-- Auxiliary induction for `Subgroup.isHall_conj`: strong induction on `Nat.card G`,
phrased with an explicit bound `n` so that the induction hypothesis can be applied to the
quotients and subgroups (which live in different types) arising in the proof. -/
private theorem isHall_conj_aux (π : Set ℕ) (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G] [IsSolvable G],
      Nat.card G ≤ n → ∀ {H K : Subgroup G}, H.IsHall π → K.IsHall π →
      ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
  induction n with
  | zero =>
    intro G _ _ _ hG
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ _ hG H K hH hK
    rcases subsingleton_or_nontrivial G with hGs | hGn
    -- Trivial group: all subgroups are equal.
    · haveI : Subsingleton (Subgroup G) := subsingleton_iff.mpr hGs
      exact ⟨1, Subsingleton.elim K _⟩
    -- Take a minimal normal subgroup `N`, an elementary abelian `p`-group.
    obtain ⟨N, hN⟩ := exists_isMinNormal G
    haveI := hN.normal
    obtain ⟨p, hp, hpN⟩ := hN.isElementaryAbelian
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpN.isPGroup
    -- Conjugate the images in `G ⧸ N` by induction, and lift the conjugating element.
    obtain ⟨gbar, hgbar⟩ := ih (G ⧸ N)
      (Nat.le_of_lt_succ ((card_quotient_lt_card_of_ne_bot hN.ne_bot).trans_le hG))
      (hH.map_mk' N) (hK.map_mk' N)
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective N gbar
    have hH₁ : (H.map (MulAut.conj g₁).toMonoidHom).IsHall π := hH.conj g₁
    have hH₁bar : (H.map (MulAut.conj g₁).toMonoidHom).map (QuotientGroup.mk' N)
        = K.map (QuotientGroup.mk' N) :=
      (map_conj_map_mk' N H g₁).trans hgbar.symm
    -- `M` := the common preimage of the images of `H₁ := H.map (conj g₁)` and `K`.
    set M := (K.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) with hMdef
    have hKM : K ≤ M := by rw [hMdef]; exact le_comap_map _ K
    have hH₁M : H.map (MulAut.conj g₁).toMonoidHom ≤ M := by
      rw [hMdef, ← hH₁bar]; exact le_comap_map _ _
    have hMcard : Nat.card M = Nat.card N * Nat.card (K.map (QuotientGroup.mk' N)) := by
      rw [hMdef, card_comap_mk']
    by_cases hpπ : p ∈ π
    -- Case `p ∈ π`: `M` is a π-group, so both Hall π-subgroups equal `M` by maximality.
    · have hMπ : M.IsPiGroup π := by
        change Nat.IsPiNumber π (Nat.card M)
        rw [hMcard, hk]
        exact ((hp.isPiNumber hpπ).pow k).mul
          (hK.1.of_dvd (K.card_map_dvd (QuotientGroup.mk' N)) Nat.card_pos.ne')
      exact ⟨g₁, (hK.eq_of_le hKM hMπ).trans (hH₁.eq_of_le hH₁M hMπ).symm⟩
    · have hNπ' : Nat.IsPiNumber πᶜ (Nat.card N) := by
        rw [hk]; exact (hp.isPiNumber hpπ).pow k
      by_cases hMtop : M = ⊤
      -- Case `p ∉ π` and `M = ⊤`: `H₁` and `K` are complements of `N`, and
      -- Schur–Zassenhaus conjugacy applies.
      · have hcomp : ∀ {C : Subgroup G}, C.IsHall π →
            C.map (QuotientGroup.mk' N) = K.map (QuotientGroup.mk' N) →
            IsComplement' N C := by
          intro C hC hCbar
          have hdisj : Disjoint N C := disjoint_of_coprime_natCard
            (hC.1.coprime hNπ' Nat.card_pos.ne' Nat.card_pos.ne').symm
          have hdker : Disjoint (QuotientGroup.mk' N).ker C := by
            rw [QuotientGroup.ker_mk']; exact hdisj
          refine isComplement'_of_card_mul_and_disjoint ?_ hdisj
          have hMG : Nat.card M = Nat.card G := by rw [hMtop, card_top]
          rw [← hMG, hMcard, ← hCbar, card_map_of_disjoint_ker hdker]
        have hKcomp : IsComplement' N K := hcomp hK rfl
        have hH₁comp : IsComplement' N (H.map (MulAut.conj g₁).toMonoidHom) :=
          hcomp hH₁ hH₁bar
        have hco : (Nat.card N).Coprime N.index := by
          rw [hKcomp.symm.index_eq_card]
          exact (hK.1.coprime hNπ' Nat.card_pos.ne' Nat.card_pos.ne').symm
        obtain ⟨g₂, hg₂⟩ := hH₁comp.exists_conj_of_coprime hco hKcomp
        exact ⟨g₂ * g₁, hg₂.trans (map_conj_map_conj H g₁ g₂)⟩
      -- Case `p ∉ π` and `M ≠ ⊤`: both are Hall π-subgroups of `M`; induct inside `M`.
      · obtain ⟨m, hm⟩ := ih M
          (Nat.le_of_lt_succ ((card_lt_card_of_ne_top hMtop).trans_le hG))
          (hH₁.subgroupOf hH₁M) (hK.subgroupOf hKM)
        refine ⟨(m : G) * g₁, ?_⟩
        rw [← map_conj_map_conj H g₁ (m : G)]
        exact eq_map_conj_of_subgroupOf_eq_map_conj hH₁M hKM hm

/-- **P. Hall's conjugacy theorem** (1928): two Hall π-subgroups of a finite solvable
group are conjugate.

This corresponds to MathComp's `Hall_trans`. -/
theorem isHall_conj [Finite G] [IsSolvable G] {H K : Subgroup G}
    (hH : H.IsHall π) (hK : K.IsHall π) :
    ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom :=
  isHall_conj_aux π (Nat.card G) G le_rfl hH hK

/-- Auxiliary induction for `Subgroup.IsPiGroup.le_isHall_conj`, with the same shape as
`Subgroup.isHall_conj_aux`. -/
private theorem le_isHall_conj_aux (π : Set ℕ) (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G] [IsSolvable G],
      Nat.card G ≤ n → ∀ {H K : Subgroup G}, H.IsPiGroup π → K.IsHall π →
      ∃ g : G, H ≤ K.map (MulAut.conj g).toMonoidHom := by
  induction n with
  | zero =>
    intro G _ _ _ hG
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ _ hG H K hH hK
    rcases subsingleton_or_nontrivial G with hGs | hGn
    · haveI : Subsingleton (Subgroup G) := subsingleton_iff.mpr hGs
      exact ⟨1, (Subsingleton.elim H _).le⟩
    obtain ⟨N, hN⟩ := exists_isMinNormal G
    haveI := hN.normal
    obtain ⟨p, hp, hpN⟩ := hN.isElementaryAbelian
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpN.isPGroup
    -- Push into `G ⧸ N` and conjugate there by induction.
    have hHbar : (H.map (QuotientGroup.mk' N)).IsPiGroup π :=
      Nat.IsPiNumber.of_dvd hH (H.card_map_dvd (QuotientGroup.mk' N)) Nat.card_pos.ne'
    obtain ⟨gbar, hgbar⟩ := ih (G ⧸ N)
      (Nat.le_of_lt_succ ((card_quotient_lt_card_of_ne_bot hN.ne_bot).trans_le hG))
      hHbar (hK.map_mk' N)
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective N gbar
    have hK₁ : (K.map (MulAut.conj g₁).toMonoidHom).IsHall π := hK.conj g₁
    have hHbar_le : H.map (QuotientGroup.mk' N)
        ≤ (K.map (MulAut.conj g₁).toMonoidHom).map (QuotientGroup.mk' N) := by
      rw [map_conj_map_mk' N K g₁]
      exact hgbar
    -- `M` := the preimage of the image of `K₁ := K.map (conj g₁)`; it contains `H`.
    set M := ((K.map (MulAut.conj g₁).toMonoidHom).map (QuotientGroup.mk' N)).comap
      (QuotientGroup.mk' N) with hMdef
    have hK₁M : K.map (MulAut.conj g₁).toMonoidHom ≤ M := by
      rw [hMdef]; exact le_comap_map _ _
    have hHM : H ≤ M := by
      rw [hMdef]
      exact (le_comap_map _ H).trans (comap_mono hHbar_le)
    have hMcard : Nat.card M = Nat.card N
        * Nat.card ((K.map (MulAut.conj g₁).toMonoidHom).map (QuotientGroup.mk' N)) := by
      rw [hMdef, card_comap_mk']
    by_cases hpπ : p ∈ π
    -- Case `p ∈ π`: `M` is a π-group, so `K₁ = M ⊇ H` by maximality.
    · have hMπ : M.IsPiGroup π := by
        change Nat.IsPiNumber π (Nat.card M)
        rw [hMcard, hk]
        exact ((hp.isPiNumber hpπ).pow k).mul (hK₁.1.of_dvd
          ((K.map (MulAut.conj g₁).toMonoidHom).card_map_dvd (QuotientGroup.mk' N))
          Nat.card_pos.ne')
      refine ⟨g₁, ?_⟩
      rw [hK₁.eq_of_le hK₁M hMπ]
      exact hHM
    · have hNπ' : Nat.IsPiNumber πᶜ (Nat.card N) := by
        rw [hk]; exact (hp.isPiNumber hpπ).pow k
      by_cases hMtop : M = ⊤
      -- Case `p ∉ π` and `M = ⊤`: `K₁` is a complement of `N` in `G`, and `H` is a
      -- complement of `N` in `L := HN`; `K₁ ⊓ L` is another complement of `N` in `L`,
      -- so `H` and `K₁ ⊓ L` are conjugate in `L` by Schur–Zassenhaus.
      · have hK₁disj : Disjoint N (K.map (MulAut.conj g₁).toMonoidHom) :=
          disjoint_of_coprime_natCard
            (hK₁.1.coprime hNπ' Nat.card_pos.ne' Nat.card_pos.ne').symm
        have hK₁dker : Disjoint (QuotientGroup.mk' N).ker
            (K.map (MulAut.conj g₁).toMonoidHom) := by
          rw [QuotientGroup.ker_mk']; exact hK₁disj
        have hK₁comp : IsComplement' N (K.map (MulAut.conj g₁).toMonoidHom) := by
          refine isComplement'_of_card_mul_and_disjoint ?_ hK₁disj
          have hMG : Nat.card M = Nat.card G := by rw [hMtop, card_top]
          rw [← hMG, hMcard, card_map_of_disjoint_ker hK₁dker]
        have hHdisj : Disjoint N H := disjoint_of_coprime_natCard
          (Nat.IsPiNumber.coprime hH hNπ' Nat.card_pos.ne' Nat.card_pos.ne').symm
        have hHdker : Disjoint (QuotientGroup.mk' N).ker H := by
          rw [QuotientGroup.ker_mk']; exact hHdisj
        set L := (H.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) with hLdef
        have hHL : H ≤ L := by rw [hLdef]; exact le_comap_map _ H
        have hNL : N ≤ L := by
          rw [hLdef]
          exact (QuotientGroup.ker_mk' N).symm.trans_le (ker_le_comap _ _)
        have hLcard : Nat.card L = Nat.card N * Nat.card H := by
          rw [hLdef, card_comap_mk', card_map_of_disjoint_ker hHdker]
        have hHcompL : IsComplement' (N.subgroupOf L) (H.subgroupOf L) := by
          refine isComplement'_of_coprime ?_ ?_
          · rw [card_subgroupOf hNL, card_subgroupOf hHL, hLcard]
          · rw [card_subgroupOf hNL, card_subgroupOf hHL]
            exact (Nat.IsPiNumber.coprime hH hNπ' Nat.card_pos.ne' Nat.card_pos.ne').symm
        have hK₂compL := hK₁comp.inf_subgroupOf hNL
        have hcoL : (Nat.card (N.subgroupOf L)).Coprime (N.subgroupOf L).index := by
          rw [hHcompL.symm.index_eq_card, card_subgroupOf hNL, card_subgroupOf hHL]
          exact (Nat.IsPiNumber.coprime hH hNπ' Nat.card_pos.ne' Nat.card_pos.ne').symm
        obtain ⟨l, hl⟩ := hK₂compL.exists_conj_of_coprime hcoL hHcompL
        have hHeq : H = ((K.map (MulAut.conj g₁).toMonoidHom) ⊓ L).map
            (MulAut.conj (l : G)).toMonoidHom :=
          eq_map_conj_of_subgroupOf_eq_map_conj inf_le_right hHL hl
        refine ⟨(l : G) * g₁, ?_⟩
        rw [hHeq, ← map_conj_map_conj K g₁ (l : G)]
        exact map_mono inf_le_left
      -- Case `p ∉ π` and `M ≠ ⊤`: induct inside `M`.
      · have hH' : (H.subgroupOf M).IsPiGroup π := by
          change Nat.IsPiNumber π (Nat.card (H.subgroupOf M))
          rw [card_subgroupOf hHM]
          exact hH
        obtain ⟨m, hm⟩ := ih M
          (Nat.le_of_lt_succ ((card_lt_card_of_ne_top hMtop).trans_le hG))
          hH' (hK₁.subgroupOf hK₁M)
        refine ⟨(m : G) * g₁, ?_⟩
        rw [← map_conj_map_conj K g₁ (m : G)]
        exact le_map_conj_of_subgroupOf_le_map_conj hK₁M hHM hm

/-- **P. Hall's covering theorem**: in a finite solvable group, every π-subgroup is
contained in a conjugate of any Hall π-subgroup.

This corresponds to MathComp's `Hall_superset`. -/
theorem IsPiGroup.le_isHall_conj [Finite G] [IsSolvable G] {H K : Subgroup G}
    (hH : H.IsPiGroup π) (hK : K.IsHall π) :
    ∃ g : G, H ≤ K.map (MulAut.conj g).toMonoidHom :=
  le_isHall_conj_aux π (Nat.card G) G le_rfl hH hK

end Conjugacy

end Subgroup
