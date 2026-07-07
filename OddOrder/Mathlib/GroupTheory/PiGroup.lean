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

These correspond to MathComp's `pnat` (`π.-nat n`) and `pgroup` (`π.-group H`).
Unlike MathComp's `pnat`, `Nat.IsPiNumber` does not require `n ≠ 0`: both `0`
and `1` are π-numbers for every `π`, since they have no prime factors.
-/

namespace Nat

variable {π : Set ℕ} {m n : ℕ}

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

end Nat

namespace Subgroup

variable {G : Type*} [Group G] {π : Set ℕ}

/-- A subgroup `H` is a *π-group* if its order is a π-number. -/
def IsPiGroup (π : Set ℕ) (H : Subgroup G) : Prop := Nat.IsPiNumber π (Nat.card H)

/-- Subgroups of finite π-groups are π-groups. -/
theorem IsPiGroup.of_le {H K : Subgroup G} [Finite K] (hK : K.IsPiGroup π) (hHK : H ≤ K) :
    H.IsPiGroup π :=
  Nat.IsPiNumber.of_dvd hK (card_dvd_of_le hHK) Nat.card_pos.ne'

end Subgroup

/-- Quotients of finite π-groups are π-groups, stated for `Nat.card`.
For a normal subgroup `N` this says that `G ⧸ N` is a π-group whenever `G` is. -/
theorem Nat.IsPiNumber.card_quotient {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    (hG : Nat.IsPiNumber π (Nat.card G)) (N : Subgroup G) :
    Nat.IsPiNumber π (Nat.card (G ⧸ N)) :=
  hG.of_dvd (Subgroup.card_quotient_dvd_card N) Nat.card_pos.ne'
