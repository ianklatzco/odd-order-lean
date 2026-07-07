/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import Mathlib.GroupTheory.SchurZassenhaus
import OddOrder.Mathlib.GroupTheory.ChiefFactor
import OddOrder.Mathlib.GroupTheory.PiGroup

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

This corresponds to MathComp's `pHall` (`π.-Hall(G) H`) with `G := ⊤` and
`Hall_exists`.
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

end Card

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

end Subgroup
