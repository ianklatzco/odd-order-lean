/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Sylow

/-!
# Minimal normal subgroups and elementary abelian groups

A *minimal normal subgroup* of a group `G` is a nontrivial normal subgroup that
contains no nontrivial normal subgroup of `G` other than itself. A group is
*elementary abelian* for a prime `p` if it is commutative and every element `g`
satisfies `g ^ p = 1`.

The main result of this file is the first step in the chief-series analysis of
finite solvable groups: every minimal normal subgroup of a finite solvable
group is elementary abelian for some prime `p`.

## Main definitions

* `IsElementaryAbelian p G`: `G` is commutative and every element satisfies `g ^ p = 1`.
* `Subgroup.IsMinNormal N`: `N` is a minimal normal subgroup of `G`.

## Main results

* `Subgroup.exists_isMinNormal`: every nontrivial finite group has a minimal
  normal subgroup.
* `Subgroup.IsMinNormal.isElementaryAbelian`: every minimal normal subgroup of
  a finite solvable group is elementary abelian for some prime `p`.

These correspond to MathComp's `minnormal`, `p.-abelem` and
`minnormal_solvable_abelem` (`minnormal_solvable`).
-/

/-- A group `G` is *elementary abelian* for `p` if it is commutative and every
element `g` satisfies `g ^ p = 1`.  For a prime `p` these are exactly the
groups expressible as vector spaces over `ZMod p`: the additivization of an
elementary abelian group is a `Module (ZMod p)` via `AddCommGroup.zmodModule`.
(That transport is deliberately not set up here.)

For a subgroup `N : Subgroup G`, apply this to the coercion: `IsElementaryAbelian p N`.

This corresponds to MathComp's `p.-abelem`. -/
def IsElementaryAbelian (p : ℕ) (G : Type*) [Group G] : Prop :=
  (∀ a b : G, a * b = b * a) ∧ ∀ g : G, g ^ p = 1

/-- An elementary abelian `p`-group is a `p`-group: every element is killed by
`p = p ^ 1`.

This corresponds to MathComp's `abelem_pgroup`. -/
theorem IsElementaryAbelian.isPGroup {p : ℕ} {G : Type*} [Group G]
    (h : IsElementaryAbelian p G) : IsPGroup p G :=
  fun g => ⟨1, by rw [pow_one p]; exact h.2 g⟩

open scoped commutatorElement

namespace Subgroup

variable {G : Type*} [Group G]

/-- A *minimal normal subgroup* of `G`: a nontrivial normal subgroup that is
minimal among nontrivial normal subgroups of `G`, i.e. an atom in the lattice
of normal subgroups of `G`.

This corresponds to MathComp's `minnormal` (with ambient group `G`). -/
def IsMinNormal (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup G, M.Normal → M ≤ N → M ≠ ⊥ → M = N

/-- A minimal normal subgroup is normal. -/
theorem IsMinNormal.normal {N : Subgroup G} (hN : N.IsMinNormal) : N.Normal :=
  hN.1

/-- A minimal normal subgroup is nontrivial. -/
theorem IsMinNormal.ne_bot {N : Subgroup G} (hN : N.IsMinNormal) : N ≠ ⊥ :=
  hN.2.1

/-- A nontrivial normal subgroup contained in a minimal normal subgroup `N`
equals `N`. -/
theorem IsMinNormal.eq_of_le {N M : Subgroup G} (hN : N.IsMinNormal) (hM : M.Normal)
    (hle : M ≤ N) (hbot : M ≠ ⊥) : M = N :=
  hN.2.2 M hM hle hbot

/-- Every nontrivial finite group has a minimal normal subgroup. -/
theorem exists_isMinNormal (G : Type*) [Group G] [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, N.IsMinNormal := by
  obtain ⟨N, ⟨hnorm, hbot⟩, hmin⟩ :=
    exists_minimal_of_wellFoundedLT (fun N : Subgroup G ↦ N.Normal ∧ N ≠ ⊥)
      ⟨⊤, inferInstance, top_ne_bot⟩
  exact ⟨N, hnorm, hbot, fun M hM hle hbot' ↦ le_antisymm hle (hmin ⟨hM, hbot'⟩ hle)⟩

/-- **Minimal normal subgroups of finite solvable groups are elementary
abelian**: if `N` is a minimal normal subgroup of a finite solvable group `G`,
then there is a prime `p` such that `N` is commutative and every element of
`N` satisfies `g ^ p = 1`.

This corresponds to MathComp's `minnormal_solvable_abelem`. -/
theorem IsMinNormal.isElementaryAbelian [Finite G] [IsSolvable G] {N : Subgroup G}
    (hN : N.IsMinNormal) : ∃ p, p.Prime ∧ IsElementaryAbelian p N := by
  obtain ⟨hnorm, hbot, hmin⟩ := hN
  haveI := hnorm
  -- Step 1: `N` is abelian, since `⁅N, N⁆` is a proper (by solvability) normal
  -- subgroup of `G` contained in `N`, hence trivial by minimality.
  have hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    have hlt : ⁅N, N⁆ < N := IsSolvable.commutator_lt_of_ne_bot hbot
    have hcb : ⁅N, N⁆ = ⊥ := by
      by_contra h
      exact hlt.ne (hmin _ inferInstance hlt.le h)
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ (⊥ : Subgroup G) := hcb ▸ commutator_mem_commutator ha hb
    rwa [mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  -- Step 2: pick a prime `p` dividing the order of `N`.
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (N.one_lt_card_iff_ne_bot.mpr hbot).ne'
  haveI : Fact p.Prime := ⟨hp⟩
  -- Step 3: the elements of `N` killed by `p` form a subgroup of `G` (as `N` is
  -- abelian), normal in `G` (as `N` is), and nontrivial by Cauchy's theorem;
  -- by minimality it is all of `N`, so `N` has exponent `p`.
  let Ω : Subgroup G :=
    { carrier := {g | g ∈ N ∧ g ^ p = 1}
      one_mem' := ⟨N.one_mem, one_pow p⟩
      mul_mem' := fun {a b} ha hb ↦ ⟨N.mul_mem ha.1 hb.1, by
        rw [Commute.mul_pow (hcomm a ha.1 b hb.1), ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha ↦ ⟨N.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hΩnorm : Ω.Normal :=
    ⟨fun a ha g ↦ ⟨hnorm.conj_mem a ha.1 g, by
      rw [conj_pow, ha.2, mul_one, mul_inv_cancel]⟩⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpdvd
  have hxΩ : (x : G) ∈ Ω := ⟨x.2, by rw [← hx]; exact_mod_cast pow_orderOf_eq_one x⟩
  have hΩbot : Ω ≠ ⊥ := by
    intro hbot'
    have hx1 : (x : G) = 1 := by rwa [hbot', mem_bot] at hxΩ
    have : x = 1 := by exact_mod_cast hx1
    rw [this, orderOf_one] at hx
    exact hp.ne_one hx.symm
  have hΩN : Ω = N := hmin Ω hΩnorm (fun g hg ↦ hg.1) hΩbot
  refine ⟨p, hp, fun a b ↦ Subtype.ext (hcomm a a.2 b b.2), fun g ↦ ?_⟩
  have hg : (g : G) ∈ Ω := hΩN.symm ▸ g.2
  exact Subtype.ext (by push_cast; exact hg.2)

end Subgroup
