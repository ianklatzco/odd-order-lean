/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
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

This corresponds to MathComp's `pHall` (`π.-Hall(G) H`) with `G := ⊤`.
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
  (Nat.disjoint_primeFactors Nat.card_pos.ne' index_ne_zero_of_finite).mp <|
    Finset.disjoint_left.mpr fun p hp hp' => h.2 p hp' (h.1 p hp)

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
