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
* `Subgroup.exists_isMinNormal_le`: every nontrivial normal subgroup of a
  finite group contains a minimal normal subgroup of the ambient group.
* `Subgroup.isElementaryAbelian_of_minimal`: the predicate-parameterized core of
  the minimality argument: a nontrivial finite solvable subgroup that is minimal
  among nontrivial subgroups satisfying a predicate `P` (closed under the derived
  subgroup and under prime-torsion subgroups) is elementary abelian.
* `Subgroup.IsMinNormal.isElementaryAbelian`: every minimal normal subgroup of
  a finite solvable group is elementary abelian for some prime `p` (the core
  lemma with `P := Subgroup.Normal`; `CoprimeAction.lean` instantiates the core
  with `P := fun M => M.Normal ∧ M.SMulInvariant A`).

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

/-- Every nontrivial normal subgroup `H` of a finite group contains a minimal
normal subgroup of the ambient group: a normal subgroup that is minimal among
all nontrivial normal subgroups below `H` is in fact minimal among all
nontrivial normal subgroups. -/
theorem exists_isMinNormal_le [Finite G] {H : Subgroup G} (hH : H.Normal) (hne : H ≠ ⊥) :
    ∃ N : Subgroup G, N.IsMinNormal ∧ N ≤ H := by
  obtain ⟨N, ⟨⟨hnorm, hbot⟩, hle⟩, hmin⟩ :=
    exists_minimal_of_wellFoundedLT (fun N : Subgroup G ↦ (N.Normal ∧ N ≠ ⊥) ∧ N ≤ H)
      ⟨H, ⟨hH, hne⟩, le_rfl⟩
  exact ⟨N, ⟨hnorm, hbot,
    fun M hM hleM hbotM ↦ le_antisymm hleM (hmin ⟨⟨hM, hbotM⟩, hleM.trans hle⟩ hleM)⟩, hle⟩

/-- The commutator subgroup of a nontrivial solvable subgroup is a proper subgroup:
`⁅N, N⁆ < N` when `N ≠ ⊥` and `N` is solvable *as a group* (Mathlib's
`IsSolvable.commutator_lt_of_ne_bot` requires the ambient group to be solvable).

This corresponds to MathComp's `sol_der1_proper`. -/
theorem commutator_lt_of_isSolvable {N : Subgroup G} [IsSolvable N] (hbot : N ≠ ⊥) :
    ⁅N, N⁆ < N := by
  rw [← N.nontrivial_iff_ne_bot] at hbot
  rw [← N.range_subtype, MonoidHom.range_eq_map, ← map_commutator,
    map_subtype_lt_map_subtype]
  exact IsSolvable.commutator_lt_top_of_nontrivial N

/-- **Predicate-parameterized core of the "minimal ⇒ elementary abelian" argument**
(the engine of MathComp's `minnormal_solvable_abelem`): let `M` be a nontrivial
finite solvable subgroup, minimal among nontrivial subgroups of `M` satisfying a
predicate `P`.  If `P` holds for the derived subgroup `⁅M, M⁆` and for every
prime-torsion subgroup `{g ∈ M | g ^ q = 1}` (specified by its membership
predicate, since it is only a subgroup once `M` is known to be abelian), then `M`
is elementary abelian for some prime `p`.

Consumers: `Subgroup.IsMinNormal.isElementaryAbelian` below (`P := Normal`) and
`isElementaryAbelian_of_min_smulInvariant` in `CoprimeAction.lean`
(`P := fun M ↦ M.Normal ∧ M.SMulInvariant A`). -/
theorem isElementaryAbelian_of_minimal {P : Subgroup G → Prop} {M : Subgroup G}
    [Finite M] [IsSolvable M] (hbot : M ≠ ⊥)
    (hmin : ∀ M' : Subgroup G, P M' → M' ≠ ⊥ → M' ≤ M → M' = M)
    (hder : P ⁅M, M⁆)
    (htor : ∀ q : ℕ, q.Prime → ∀ K : Subgroup G,
      (∀ g, g ∈ K ↔ g ∈ M ∧ g ^ q = 1) → P K) :
    ∃ p, p.Prime ∧ IsElementaryAbelian p M := by
  -- Step 1: `M` is abelian, since `⁅M, M⁆` is a proper (by solvability) subgroup
  -- of `M` satisfying `P`, hence trivial by minimality.
  have hcomm : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := by
    have hlt : ⁅M, M⁆ < M := commutator_lt_of_isSolvable hbot
    have hcb : ⁅M, M⁆ = ⊥ := by
      by_contra h
      exact hlt.ne (hmin _ hder h hlt.le)
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ (⊥ : Subgroup G) := hcb ▸ commutator_mem_commutator ha hb
    rwa [mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  -- Step 2: pick a prime `p` dividing the order of `M`.
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (M.one_lt_card_iff_ne_bot.mpr hbot).ne'
  haveI : Fact p.Prime := ⟨hp⟩
  -- Step 3: the elements of `M` killed by `p` form a subgroup of `G` (as `M` is
  -- abelian), satisfying `P` by `htor`, and nontrivial by Cauchy's theorem;
  -- by minimality it is all of `M`, so `M` has exponent `p`.
  let Ω : Subgroup G :=
    { carrier := {g | g ∈ M ∧ g ^ p = 1}
      one_mem' := ⟨M.one_mem, one_pow p⟩
      mul_mem' := fun {a b} ha hb ↦ ⟨M.mul_mem ha.1 hb.1, by
        rw [Commute.mul_pow (hcomm a ha.1 b hb.1), ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha ↦ ⟨M.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hΩP : P Ω := htor p hp Ω fun g ↦ Iff.rfl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) p hpdvd
  have hxΩ : (x : G) ∈ Ω := ⟨x.2, by rw [← hx]; exact_mod_cast pow_orderOf_eq_one x⟩
  have hΩbot : Ω ≠ ⊥ := by
    intro hbot'
    have hx1 : (x : G) = 1 := by rwa [hbot', mem_bot] at hxΩ
    have : x = 1 := by exact_mod_cast hx1
    rw [this, orderOf_one] at hx
    exact hp.ne_one hx.symm
  have hΩM : Ω = M := hmin Ω hΩP hΩbot fun g hg ↦ hg.1
  refine ⟨p, hp, fun a b ↦ Subtype.ext (hcomm a a.2 b b.2), fun g ↦ ?_⟩
  have hg : (g : G) ∈ Ω := hΩM.symm ▸ g.2
  exact Subtype.ext (by push_cast; exact hg.2)

/-- **Minimal normal subgroups of finite solvable groups are elementary
abelian**: if `N` is a minimal normal subgroup of a finite solvable group `G`,
then there is a prime `p` such that `N` is commutative and every element of
`N` satisfies `g ^ p = 1`.

This corresponds to MathComp's `minnormal_solvable_abelem`. -/
theorem IsMinNormal.isElementaryAbelian [Finite G] [IsSolvable G] {N : Subgroup G}
    (hN : N.IsMinNormal) : ∃ p, p.Prime ∧ IsElementaryAbelian p N := by
  obtain ⟨hnorm, hbot, hmin⟩ := hN
  haveI := hnorm
  refine isElementaryAbelian_of_minimal (P := fun M ↦ M.Normal) hbot
    (fun M' h1 h2 h3 ↦ hmin M' h1 h3 h2) inferInstance fun q _hq K hK ↦ ?_
  refine ⟨fun a ha g ↦ ?_⟩
  rw [hK] at ha ⊢
  exact ⟨hnorm.conj_mem a ha.1 g, by rw [conj_pow, ha.2, mul_one, mul_inv_cancel]⟩

end Subgroup
