/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import Mathlib.GroupTheory.Sylow

/-!
# π-numbers and π-groups

Layer-0 infrastructure for the Feit–Thompson odd order theorem port.

Given a set of primes `π`, a natural number is a *π-number* if all of its prime
factors belong to `π`, and a subgroup is a *π-group* if its order is a π-number.

## Main definitions

* `Nat.IsPiNumber π n`: every prime factor of `n` belongs to `π`.
* `Subgroup.IsPiGroup π H`: the order `Nat.card H` of `H` is a π-number.
* `Subgroup.pcore π G`: the π-core `O_π(G)`, the join of all normal
  π-subgroups of `G`.

## Main results

* `Subgroup.Normal.isPiGroup_sup`: the join of a π-subgroup with a normal
  π-subgroup is a π-group.
* `Subgroup.pcore_isPiGroup`: for a finite group, the π-core is a π-group,
  hence (with `Subgroup.pcore_normal` and `Subgroup.pcore_max`) the largest
  normal π-subgroup.

These correspond to MathComp's `pnat` (`π.-nat n`), `pgroup` (`π.-group H`)
and `pcore` (`'O_π(G)`).
Unlike MathComp's `pnat`, `Nat.IsPiNumber` does not require `n ≠ 0`: both `0`
and `1` are π-numbers for every `π`, since they have no prime factors.
-/

namespace Nat

variable {π : Set ℕ} {m n p : ℕ}

/-- A natural number `n` is a *π-number* if all of its prime factors belong to `π`. -/
def IsPiNumber (π : Set ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ∈ π

@[simp]
theorem isPiNumber_zero : IsPiNumber π 0 := by
  simp [IsPiNumber]

@[simp]
theorem isPiNumber_one : IsPiNumber π 1 := by
  simp [IsPiNumber]

/-- Divisors of nonzero π-numbers are π-numbers. -/
protected theorem IsPiNumber.of_dvd (hn : IsPiNumber π n) (hmn : m ∣ n) (hn₀ : n ≠ 0) :
    IsPiNumber π m :=
  fun p hp => hn p (primeFactors_mono hmn hn₀ hp)

/-- A prime belonging to `π` is a π-number. -/
protected theorem Prime.isPiNumber (hp : p.Prime) (hpπ : p ∈ π) : IsPiNumber π p := by
  intro q hq
  rw [hp.primeFactors, Finset.mem_singleton] at hq
  exact hq ▸ hpπ

/-- The product of two π-numbers is a π-number. -/
protected theorem IsPiNumber.mul (hm : IsPiNumber π m) (hn : IsPiNumber π n) :
    IsPiNumber π (m * n) := by
  rcases eq_or_ne m 0 with rfl | hm₀
  · simp
  rcases eq_or_ne n 0 with rfl | hn₀
  · simp
  intro p hp
  rw [primeFactors_mul hm₀ hn₀, Finset.mem_union] at hp
  exact hp.elim (hm p) (hn p)

/-- Powers of π-numbers are π-numbers. -/
protected theorem IsPiNumber.pow (hn : IsPiNumber π n) (k : ℕ) : IsPiNumber π (n ^ k) := by
  cases k with
  | zero => simp
  | succ k => exact fun p hp => hn p (by rwa [primeFactors_pow_succ] at hp)

/-- A π-number and a π'-number are coprime.

This corresponds to MathComp's `pnat_coprime`. -/
protected theorem IsPiNumber.coprime (hm : IsPiNumber π m) (hn : IsPiNumber πᶜ n)
    (hm₀ : m ≠ 0) (hn₀ : n ≠ 0) : m.Coprime n :=
  (disjoint_primeFactors hm₀ hn₀).mp <|
    Finset.disjoint_left.mpr fun p hpm hpn => hn p hpn (hm p hpm)

end Nat

namespace Subgroup

variable {G : Type*} [Group G] {π : Set ℕ}

/-- A subgroup `H` is a *π-group* if its order is a π-number. -/
def IsPiGroup (π : Set ℕ) (H : Subgroup G) : Prop := Nat.IsPiNumber π (Nat.card H)

/-- Subgroups of finite π-groups are π-groups. -/
theorem IsPiGroup.of_le {H K : Subgroup G} [Finite K] (hK : K.IsPiGroup π) (hHK : H ≤ K) :
    H.IsPiGroup π :=
  Nat.IsPiNumber.of_dvd hK (card_dvd_of_le hHK) Nat.card_pos.ne'

/-- The order of the join of a subgroup `H` with a normal subgroup `N` divides
`Nat.card H * Nat.card N`.

This is the cardinality part of the product-subgroup calculus (for normal `N`
the join `H ⊔ N` is the product set `H * N`); it follows from Noether's second
isomorphism theorem `QuotientGroup.quotientInfEquivProdNormalQuotient`. -/
theorem card_sup_dvd_card_mul_card (H N : Subgroup G) [N.Normal] :
    Nat.card ↥(H ⊔ N) ∣ Nat.card H * Nat.card N :=
  calc Nat.card ↥(H ⊔ N)
      = Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) * Nat.card (N.subgroupOf (H ⊔ N)) :=
        card_eq_card_quotient_mul_card_subgroup _
    _ = Nat.card (H ⧸ N.subgroupOf H) * Nat.card N := by
        rw [Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H N).symm.toEquiv,
          Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv]
    _ ∣ Nat.card H * Nat.card N :=
        mul_dvd_mul_right (card_quotient_dvd_card _) _

/-- The join of a finite π-subgroup with a finite normal π-subgroup is a
π-group; note that only `N` needs to be normal.  This is the join-stability
property behind `Subgroup.pcore`.

MathComp works with the product set `H * N` instead and derives this from
`pgroupM`. -/
theorem Normal.isPiGroup_sup {H N : Subgroup G} [Finite H] [Finite N] (hN : N.Normal)
    (hHπ : H.IsPiGroup π) (hNπ : N.IsPiGroup π) : (H ⊔ N).IsPiGroup π :=
  haveI := hN
  Nat.IsPiNumber.of_dvd (Nat.IsPiNumber.mul hHπ hNπ) (card_sup_dvd_card_mul_card H N)
    (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')

end Subgroup

/-- Quotients of finite π-groups are π-groups, stated for `Nat.card`.
For a normal subgroup `N` this says that `G ⧸ N` is a π-group whenever `G` is. -/
theorem Nat.IsPiNumber.card_quotient {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    (hG : Nat.IsPiNumber π (Nat.card G)) (N : Subgroup G) :
    Nat.IsPiNumber π (Nat.card (G ⧸ N)) :=
  hG.of_dvd (Subgroup.card_quotient_dvd_card N) Nat.card_pos.ne'

/-!
### The π-core `O_π(G)`

`Subgroup.pcore π G` is the join of all normal π-subgroups of `G`.  For a
finite group it is itself a π-group (`Subgroup.pcore_isPiGroup`), because the
join of two normal π-subgroups is again one (`Subgroup.Normal.isPiGroup_sup`)
and the subgroup lattice is well-founded, so it is the largest normal
π-subgroup.
-/

namespace Subgroup

/-- `O_π(G)`: the *π-core* of `G`, the join of all normal π-subgroups.  For a
finite group this is the largest normal π-subgroup: it is a π-group by
`Subgroup.pcore_isPiGroup` and contains every normal π-subgroup by
`Subgroup.pcore_max`.

This corresponds to MathComp's `pcore` (`'O_π(G)`). -/
def pcore (π : Set ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨆ (N : Subgroup G) (_ : N.Normal) (_ : N.IsPiGroup π), N

variable {G : Type*} [Group G] {π : Set ℕ}

/-- Every normal π-subgroup is contained in the π-core.

This corresponds to MathComp's `pcore_max`. -/
theorem pcore_max {N : Subgroup G} [hN : N.Normal] (h : N.IsPiGroup π) : N ≤ pcore π G :=
  le_iSup_of_le N (le_iSup_of_le hN (le_iSup_of_le h le_rfl))

/-- The π-core is contained in every subgroup containing all normal π-subgroups. -/
theorem pcore_le {H : Subgroup G} (h : ∀ N : Subgroup G, N.Normal → N.IsPiGroup π → N ≤ H) :
    pcore π G ≤ H :=
  iSup_le fun N => iSup_le fun hN => iSup_le fun hNπ => h N hN hNπ

/-- The π-core is a characteristic subgroup: automorphisms permute the normal
π-subgroups, hence fix their join.

This corresponds to MathComp's `pcore_char`. -/
instance pcore_characteristic : (pcore π G).Characteristic := by
  refine characteristic_iff_map_le.mpr fun φ => ?_
  rw [map_le_iff_le_comap]
  refine pcore_le fun N hN hNπ => ?_
  rw [← map_le_iff_le_comap]
  haveI := hN.map φ.toMonoidHom φ.surjective
  refine pcore_max (show Nat.IsPiNumber π (Nat.card (N.map φ.toMonoidHom)) from ?_)
  rw [card_map_of_injective φ.injective]
  exact hNπ

/-- The π-core is a normal subgroup.

This corresponds to MathComp's `pcore_normal`. -/
instance pcore_normal : (pcore π G).Normal := inferInstance

/-- For a finite group `G`, the π-core is a π-group — hence, together with
`Subgroup.pcore_normal` and `Subgroup.pcore_max`, the largest normal
π-subgroup.

This corresponds to MathComp's `pcore_pgroup`. -/
theorem pcore_isPiGroup [Finite G] : (pcore π G).IsPiGroup π := by
  -- Choose a maximal normal π-subgroup `M` (the normal π-subgroup `⊥` exists).
  obtain ⟨M, ⟨hM, hMπ⟩, hMmax⟩ :=
    exists_maximal_of_wellFoundedGT (fun N : Subgroup G ↦ N.Normal ∧ N.IsPiGroup π)
      ⟨⊥, inferInstance, show Nat.IsPiNumber π (Nat.card (⊥ : Subgroup G)) by
        rw [card_bot]; exact Nat.isPiNumber_one⟩
  -- `M` absorbs every normal π-subgroup `N`, since `M ⊔ N` is again one; hence
  -- the π-core equals `M`.
  haveI := hM
  have hcore : pcore π G = M := by
    refine le_antisymm (pcore_le fun N hN hNπ => ?_) (pcore_max hMπ)
    haveI := hN
    exact le_sup_right.trans (hMmax ⟨inferInstance, hN.isPiGroup_sup hMπ hNπ⟩ le_sup_left)
  rw [hcore]
  exact hMπ

end Subgroup
