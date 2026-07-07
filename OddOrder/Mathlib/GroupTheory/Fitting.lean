/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import Mathlib.GroupTheory.Nilpotent
import OddOrder.Mathlib.GroupTheory.ChiefFactor
import OddOrder.Mathlib.GroupTheory.PiGroup

/-!
# The Fitting subgroup

The *Fitting subgroup* `F(G)` of a group `G` is the join of all normal
nilpotent subgroups of `G`.  For a finite group it is itself nilpotent
(Fitting's theorem), hence the largest normal nilpotent subgroup, and it
equals the join of the `p`-cores `O_p(G)` over the primes `p` dividing the
order of `G`.

The main result of this file is the key self-centralizing property of the
Fitting subgroup of a finite *solvable* group: `C_G(F(G)) ≤ F(G)`
(Bender–Glauberman 1.3).

## Main definitions

* `Fitting G`: the join of all normal nilpotent subgroups of `G`.

## Main results

* `Fitting.max`: every normal nilpotent subgroup is contained in `Fitting G`.
* `Fitting.characteristic`, `Fitting.normal`: `Fitting G` is characteristic,
  hence normal.
* `Fitting_eq_iSup_pcore`: for a finite group,
  `Fitting G = ⨆ p ∈ (Nat.card G).primeFactors, O_p(G)`.
* `Fitting.isNilpotent` (**Fitting's theorem**): the Fitting subgroup of a
  finite group is nilpotent.
* `Fitting.centralizer_le` (**B&G 1.3**): in a finite solvable group,
  `C_G(F(G)) ≤ F(G)`.

These correspond to MathComp's `'F(G)` (`Fitting`), `Fitting_max`,
`Fitting_char`/`Fitting_normal`, `Fitting_nil`, `FittingEgen` and
`cent_sub_Fitting`.

The internal-direct-product refinement of `Fitting_eq_iSup_pcore`
(`F(G) = ∏_p O_p(G)` as an internal direct product) is not ported yet; the
join form suffices for the odd-order development.

## Implementation notes

Fitting's theorem is proved via the `p`-core description rather than by the
classical `[M, N] ≤ M ⊓ N` induction: every normal nilpotent subgroup is the
join of (the images of) its Sylow subgroups, which are normal `p`-subgroups
of `G`, so it lies in the join `K` of the `p`-cores; conversely `K` is
nilpotent because each `O_p(G)` is its unique — hence normal — Sylow
`p`-subgroup, and a finite group all of whose Sylow subgroups are normal is
nilpotent (`Group.isNilpotent_of_finite_tfae`).

`Fitting.centralizer_le` follows Hall's argument (Isaacs, *Finite Group
Theory*, 3.10, adapted to avoid chief series): write `F = F(G)`,
`C = C_G(F)` and `Z = C ⊓ F`, which is normal in `G` (so `G ⧸ Z` makes sense)
and contained in both `C` and `F`.  If `C ≰ F`, the
image of `C` in `G ⧸ Z` is a nontrivial normal subgroup, so it contains a
minimal normal subgroup `M/Z` of `G ⧸ Z` (`Subgroup.exists_isMinNormal_le`),
which is abelian by solvability (`Subgroup.IsMinNormal.isElementaryAbelian`).
The preimage `M ≤ C` then satisfies `⁅M, M⁆ ≤ Z ≤ F`, and `M` centralizes
`F`, so `⁅M, M⁆ ≤ Z(M)`; hence `M` is nilpotent of class at most two and
normal, so `M ≤ F` by maximality, forcing `M ≤ Z` — contradicting the
nontriviality of `M/Z`.
-/

open scoped commutatorElement

/-!
### Prerequisites missing from Mathlib

One general fact used below: a group whose commutator subgroup is central is
nilpotent (of class at most two).
-/

/-- A group whose commutator subgroup is contained in its center is nilpotent
(of class at most `2`). -/
theorem Group.isNilpotent_of_commutator_le_center {G : Type*} [Group G]
    (h : commutator G ≤ Subgroup.center G) : Group.IsNilpotent G := by
  refine ⟨1 + 1, eq_top_iff.mpr fun g _ => ?_⟩
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro y
  rw [Subgroup.upperCentralSeries_one]
  exact h (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top y))

/-- A finite group is the join of (any choice of) its Sylow subgroups: the
join has order divisible by the full `p`-part of the group order for every
prime `p`. -/
theorem Sylow.biSup_eq_top (G : Type*) [Group G] [Finite G] (P : ∀ p : ℕ, Sylow p G) :
    ⨆ p ∈ (Nat.card G).primeFactors, (P p : Subgroup G) = ⊤ := by
  refine Subgroup.eq_top_of_card_eq _
    (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card _) ?_)
  rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne']
  refine (Finsupp.le_iff _ _).mpr fun p hp => ?_
  rw [Nat.support_factorization] at hp
  haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  refine (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp ?_
  rw [← (P p).card_eq_multiplicity]
  exact Subgroup.card_dvd_of_le (le_biSup (fun q => (P q : Subgroup G)) hp)

/-!
### The Fitting subgroup
-/

/-- The *Fitting subgroup* `F(G)`: the join of all normal nilpotent subgroups
of `G`.  For a finite group this is the largest normal nilpotent subgroup: it
is nilpotent by `Fitting.isNilpotent` and contains every normal nilpotent
subgroup by `Fitting.max`.

This corresponds to MathComp's `'F(G)` (`Fitting`). -/
def Fitting (G : Type*) [Group G] : Subgroup G :=
  ⨆ (N : Subgroup G) (_ : N.Normal) (_ : Group.IsNilpotent N), N

namespace Fitting

variable {G : Type*} [Group G]

/-- Every normal nilpotent subgroup is contained in the Fitting subgroup.

This corresponds to MathComp's `Fitting_max`. -/
theorem max {N : Subgroup G} [hN : N.Normal] (h : Group.IsNilpotent N) : N ≤ Fitting G :=
  le_iSup_of_le N (le_iSup_of_le hN (le_iSup_of_le h le_rfl))

/-- The Fitting subgroup is contained in every subgroup containing all normal
nilpotent subgroups. -/
theorem le {H : Subgroup G} (h : ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → N ≤ H) :
    Fitting G ≤ H :=
  iSup_le fun N => iSup_le fun hN => iSup_le fun hNnil => h N hN hNnil

/-- The Fitting subgroup is characteristic: automorphisms permute the normal
nilpotent subgroups, hence fix their join.

This corresponds to MathComp's `Fitting_char`. -/
instance characteristic : (Fitting G).Characteristic := by
  refine Subgroup.characteristic_iff_map_le.mpr fun φ => ?_
  rw [Subgroup.map_le_iff_le_comap]
  refine Fitting.le fun N hN hNnil => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  haveI := hN.map φ.toMonoidHom φ.surjective
  haveI := hNnil
  exact Fitting.max
    (Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective N φ.toMonoidHom φ.injective))

/-- The Fitting subgroup is normal.

This corresponds to MathComp's `Fitting_normal`. -/
instance normal : (Fitting G).Normal := inferInstance

end Fitting

/-!
### Fitting's theorem

For a finite group `G`, the Fitting subgroup is the join of the `p`-cores
`O_p(G)` over the primes dividing `Nat.card G`, and it is nilpotent.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- A normal nilpotent subgroup of a finite group is contained in the join of
the `p`-cores: it is the join of (the images of) its Sylow subgroups, each of
which is a normal `p`-subgroup of `G` because it is characteristic in `N`. -/
theorem Normal.le_iSup_pcore [Finite G] {N : Subgroup G} (hN : N.Normal)
    (hnil : Group.IsNilpotent N) :
    N ≤ ⨆ p ∈ (Nat.card G).primeFactors, Subgroup.pcore {p} G := by
  haveI := hN
  haveI := hnil
  -- a choice of Sylow `p`-subgroup of `N` for every `p`
  obtain ⟨P⟩ : Nonempty (∀ p : ℕ, Sylow p N) := ⟨fun _ => Classical.arbitrary _⟩
  -- `N` is the join of the images of its Sylow subgroups
  have hNS : N = ⨆ p ∈ (Nat.card N).primeFactors, (P p : Subgroup N).map N.subtype := by
    calc N = (⊤ : Subgroup N).map N.subtype :=
        ((MonoidHom.range_eq_map _).symm.trans N.range_subtype).symm
    _ = (⨆ p ∈ (Nat.card N).primeFactors, (P p : Subgroup N)).map N.subtype := by
        rw [Sylow.biSup_eq_top]
    _ = ⨆ p ∈ (Nat.card N).primeFactors, (P p : Subgroup N).map N.subtype := by
        simp_rw [Subgroup.map_iSup]
  -- each image is a normal `p`-subgroup of `G`, hence lies in `O_p(G)`
  refine hNS.trans_le (iSup₂_le fun p hp => ?_)
  haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have hpG : p ∈ (Nat.card G).primeFactors :=
    Nat.primeFactors_mono (Subgroup.card_subgroup_dvd_card N) Nat.card_pos.ne' hp
  refine le_trans ?_ (le_biSup (fun q => Subgroup.pcore {q} G) hpG)
  haveI : (P p : Subgroup N).Characteristic := Sylow.characteristic_of_normal (P p) inferInstance
  haveI : ((P p : Subgroup N).map N.subtype).Normal := inferInstance
  exact Subgroup.pcore_max ((P p).isPGroup'.map N.subtype).isPiGroup

/-- The join of the `p`-cores of a finite group over the primes dividing its
order is nilpotent: each `O_p(G)` is its unique, hence normal, Sylow
`p`-subgroup, and a finite group all of whose Sylow subgroups are normal is
nilpotent. -/
theorem isNilpotent_iSup_pcore (G : Type*) [Group G] [Finite G] :
    Group.IsNilpotent ↥(⨆ p ∈ (Nat.card G).primeFactors, Subgroup.pcore {p} G) := by
  set K : Subgroup G := ⨆ p ∈ (Nat.card G).primeFactors, Subgroup.pcore {p} G with hK
  refine ((Group.isNilpotent_of_finite_tfae (G := ↥K)).out 0 3).mpr ?_
  intro p hp P
  haveI := hp
  by_cases hpK : p ∣ Nat.card ↥K
  case neg =>
    -- `p` does not divide `Nat.card K`, so the Sylow `p`-subgroup is trivial
    have hcard : Nat.card (P : Subgroup ↥K) = 1 := by
      rw [P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hpK, pow_zero]
    rw [Subgroup.eq_bot_of_card_le (P : Subgroup ↥K) hcard.le]
    infer_instance
  case pos =>
    -- `O_p(G)`, viewed inside `K`, is a Sylow `p`-subgroup of `K` …
    have hpG : p ∈ (Nat.card G).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hp.out, hpK.trans (Subgroup.card_subgroup_dvd_card K), Nat.card_pos.ne'⟩
    have hle : Subgroup.pcore {p} G ≤ K := by
      rw [hK]
      exact le_biSup (fun q => Subgroup.pcore {q} G) hpG
    haveI : ((Subgroup.pcore {p} G).subgroupOf K).Normal := Subgroup.pcore_normal.subgroupOf K
    have hQp : IsPGroup p ((Subgroup.pcore {p} G).subgroupOf K) :=
      Subgroup.pcore_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
    -- … because every power of `p` dividing `Nat.card K` divides its order:
    -- the orders of the other `q`-cores are coprime to `p`
    have key : ∀ m : ℕ,
        p ^ m ∣ Nat.card ↥K → p ^ m ∣ Nat.card ((Subgroup.pcore {p} G).subgroupOf K) := by
      intro m hm
      have h1 : Nat.card ↥K ∣
          ∏ q ∈ (Nat.card G).primeFactors, Nat.card (Subgroup.pcore {q} G) := by
        rw [hK]
        exact Subgroup.card_biSup_dvd_prod_card _ _ fun _ => inferInstance
      rw [← Finset.mul_prod_erase _ _ hpG] at h1
      have h2 : (p ^ m).Coprime
          (∏ q ∈ (Nat.card G).primeFactors.erase p, Nat.card (Subgroup.pcore {q} G)) := by
        refine Nat.Coprime.prod_right fun q hq => ?_
        refine Nat.IsPiNumber.coprime ((hp.out.isPiNumber (Set.mem_singleton p)).pow m)
          (fun r hr => ?_) (pow_ne_zero m hp.out.pos.ne') Nat.card_pos.ne'
        have hrq : r = q := Subgroup.pcore_isPiGroup r hr
        exact fun hrp : r = p => Finset.ne_of_mem_erase hq (hrq.symm.trans hrp)
      have hcard : Nat.card ((Subgroup.pcore {p} G).subgroupOf K) =
          Nat.card (Subgroup.pcore {p} G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
      rw [hcard]
      exact h2.dvd_of_dvd_mul_right (hm.trans h1)
    -- so its order is the full `p`-part of `Nat.card K`
    have hQcard : Nat.card ((Subgroup.pcore {p} G).subgroupOf K) =
        p ^ (Nat.card ↥K).factorization p := by
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hQp
      refine Nat.dvd_antisymm ?_ (key _ (Nat.ordProj_dvd _ p))
      rw [ha]
      exact pow_dvd_pow p ((Nat.Prime.pow_dvd_iff_le_factorization hp.out Nat.card_pos.ne').mp
        (ha ▸ Subgroup.card_subgroup_dvd_card _))
    -- a normal Sylow subgroup is the unique Sylow subgroup
    haveI := Sylow.unique_of_normal (Sylow.ofCard _ hQcard)
      ‹((Subgroup.pcore {p} G).subgroupOf K).Normal›
    rw [Subsingleton.elim P (Sylow.ofCard _ hQcard), Sylow.coe_ofCard]
    infer_instance

end Subgroup

/-- **The Fitting subgroup of a finite group is the join of its `p`-cores**
over the primes dividing the group order.

This corresponds to MathComp's `FittingEgen` (the internal-direct-product
refinement `F(G) = ∏_p O_p(G)` is not ported). -/
theorem Fitting_eq_iSup_pcore (G : Type*) [Group G] [Finite G] :
    Fitting G = ⨆ p ∈ (Nat.card G).primeFactors, Subgroup.pcore {p} G := by
  refine le_antisymm (Fitting.le fun N hN hnil => hN.le_iSup_pcore hnil) ?_
  refine iSup₂_le fun p hp => ?_
  haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  exact Fitting.max Subgroup.pcore_isPGroup.isNilpotent

/-- **Fitting's theorem**: the Fitting subgroup of a finite group is
nilpotent — hence, together with `Fitting.normal` and `Fitting.max`, the
largest normal nilpotent subgroup.

This corresponds to MathComp's `Fitting_nil`. -/
theorem Fitting.isNilpotent {G : Type*} [Group G] [Finite G] :
    Group.IsNilpotent (Fitting G) := by
  have h := Subgroup.isNilpotent_iSup_pcore G
  rwa [← Fitting_eq_iSup_pcore] at h

/-!
### The Fitting subgroup of a solvable group contains its centralizer
-/

/-- **The centralizer of the Fitting subgroup of a finite solvable group is
contained in the Fitting subgroup** (Bender–Glauberman 1.3).

This corresponds to MathComp's `cent_sub_Fitting`. -/
theorem Fitting.centralizer_le {G : Type*} [Group G] [Finite G] [IsSolvable G] :
    Subgroup.centralizer (Fitting G) ≤ Fitting G := by
  set C : Subgroup G := Subgroup.centralizer (Fitting G)
  by_contra hCF
  -- `Z = C ⊓ F(G)` is normal in `G` and contained in both `C` and `F(G)`
  set Z : Subgroup G := C ⊓ Fitting G
  -- the image of `C` in `G ⧸ Z` is a nontrivial normal subgroup
  set Cbar : Subgroup (G ⧸ Z) := C.map (QuotientGroup.mk' Z) with hCbar
  haveI : Cbar.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
  have hCbar_ne : Cbar ≠ ⊥ := fun h => by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact hCF fun x hx => (h hx).2
  -- pick a minimal normal subgroup `Mbar = M/Z` of `G ⧸ Z` inside `Cbar`;
  -- it is abelian since `G ⧸ Z` is solvable
  obtain ⟨Mbar, hMbar_min, hMbar_le⟩ := Subgroup.exists_isMinNormal_le ‹Cbar.Normal› hCbar_ne
  obtain ⟨p, -, hMbar_ab⟩ := hMbar_min.isElementaryAbelian
  set M : Subgroup G := Mbar.comap (QuotientGroup.mk' Z)
  haveI : M.Normal := hMbar_min.normal.comap _
  have hmapM : M.map (QuotientGroup.mk' Z) = Mbar :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) Mbar
  -- `M ≤ C` since `Mbar ≤ Cbar` and `Z ≤ C`
  have hMC : M ≤ C := by
    have h := Subgroup.comap_mono (f := QuotientGroup.mk' Z) hMbar_le
    rwa [hCbar, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_of_le_left (inf_le_left : Z ≤ C)] at h
  -- `⁅M, M⁆ ≤ Z` since `Mbar` is abelian
  have hMM : ⁅M, M⁆ ≤ Z := by
    have h : (⁅M, M⁆).map (QuotientGroup.mk' Z) = ⊥ := by
      rw [Subgroup.map_commutator, hmapM, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (hMbar_ab.1 ⟨y, hy⟩ ⟨x, hx⟩)
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  -- `M` centralizes `⁅M, M⁆ ≤ F(G)`, so `⁅M, M⁆` is central in `M`
  have hcomm_le : (commutator ↥M).map M.subtype ≤ Z := by
    have htop : (⊤ : Subgroup ↥M).map M.subtype = M :=
      (MonoidHom.range_eq_map _).symm.trans M.range_subtype
    rw [commutator_def, Subgroup.map_commutator, htop]
    exact hMM
  have hcenter : commutator ↥M ≤ Subgroup.center ↥M := by
    intro x hx
    refine Subgroup.mem_center_iff.mpr fun m => ?_
    have hxF : (x : G) ∈ Fitting G :=
      (Subgroup.mem_inf.mp (hcomm_le (Subgroup.mem_map_of_mem _ hx))).2
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hMC m.2) x hxF).symm
  -- hence `M` is nilpotent and normal, so `M ≤ F(G)`, contradicting `Mbar ≠ ⊥`
  have hMF : M ≤ Fitting G := Fitting.max (Group.isNilpotent_of_commutator_le_center hcenter)
  refine hMbar_min.ne_bot ?_
  rw [← hmapM, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact le_inf hMC hMF
