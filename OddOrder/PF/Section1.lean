/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import Mathlib.Analysis.Real.Sqrt
import OddOrder.Mathlib.RepresentationTheory.CharacterArith
import OddOrder.Mathlib.RepresentationTheory.CharacterTransfer
import OddOrder.Mathlib.RepresentationTheory.CharAut
import OddOrder.Mathlib.RepresentationTheory.VirtualChar

/-!
# Peterfalvi, Section 1: Preliminary results

This is the port of `PFsection1.v` — the first of the 34 Coq theory files of the
Feit–Thompson odd-order formalization, a character-theoretic toolkit used throughout the
Peterfalvi half of the proof.  All results live in `namespace PF1`; each carries its
Peterfalvi number and MathComp/Coq name.

## Main results

* `PF1.odd_eq_conj_irr1` — (1.1): in odd order, the principal character is the only
  real-valued irreducible character.
* `PF1.irr_reg_off_ker_0` — (1.2): a nonprincipal-on-`H` irreducible character vanishes at
  any `g` with `C_H(g) = 1`.
* `PF1.equiv_restrict_compl` / `PF1.equiv_restrict_compl_ortho` — (1.3): restriction/induction
  basis criteria for `'CF(H, A)` (stated over a `Basis` of the supported subspace).
* `PF1.vchar_isometry_base` (+ `vchar_isometry_base3`/`base4`) — (1.4): the isometry-extension
  workhorse.
* `PF1.cfResInd_sum_cfclass` / `cfnorm_Ind_irr` / `cfclass_Ind_cases` /
  `scaled_cfResInd_sum_cfclass` / `odd_induced_orthogonal` — (1.5): the Clifford facts for a
  normal subgroup.
* `PF1.cfInd_sum_Inertia` — (1.7)(a): the Clifford correspondence bijection (constituents of
  `Ind_H^T θ` ↔ constituents of `Ind_H^G θ` via induction from the inertia group `T`).
* `PF1.irr1_bound_quo` — (1.8): the `χ(1) ≤ |G:C|·√|C:D|` degree bound.
* `PF1.extend_coprime_Qn_aut` / `dvd_restrict_cfAut` / `make_pi_cfAut` — (1.9): Galois
  automorphisms of `ℂ` acting selectively on character values.
* `PF1.eqAmod`, `PF1.vchar_ker_mod_prim`, `PF1.int_eqAmod_prime_prim` — (1.10): congruences of
  virtual-character values modulo `1 - ε` for a primitive `p`-th root `ε`.

## Conventions and deviations from the Coq

* Irreducible characters are indexed by `Irr H` directly, not by `Iirr` ordinals (per the
  survey's porting note); (1.3)/(1.4) are restated over `Basis`/`Fin`-families accordingly.
* Odd order is `Odd (Nat.card G)`; MathComp: `odd #|G|`.  `'Z[irr G, G^#]`-membership is
  `IsVirtualChar ∧ φ 1 = 0` (`zcharD1E`).
* (1.10) uses the global ring of algebraic integers for `ℤ[ε]` (the Coq's documented
  simplification).
* **Scope note.** (1.7)(b) `cfInd_central_Inertia` and (1.7)(c) `cfInd_Hall_central_Inertia`
  are NOT ported here: they need product-of-irreducible-by-linear-character irreducibility
  (`mul_lin_irr`, hence tensor products of representations — a documented M2 omission),
  `cfDet`, and `extend_solvable_coprime_irr`, none of which exist in the project yet.  The
  (1.7)(a) bijection they build on is fully proved.  (1.8) rests on the character-center
  Schur bound `irr1_bound` (`cfcenter`), also not yet in the project; its one leaf
  (`irr1_bound_charCenter`) is the single budgeted gap in this file (tagged `TODO`).
-/

noncomputable section

open Finset LinearMap Module
open scoped ClassFunction

universe u v


/-- A character of norm `1` is an irreducible character.  A norm-`1` virtual character is
`±` an irreducible character (`vchar_norm1`, `IsVirtualChar.exists_eq_or_eq_neg_of_..`), and
the `-χ` case is impossible for an honest character since `⟪φ, χ⟫` is then a natural number
equal to `-1`.  MathComp: the `irrEchar`/`vchar_norm1P` combination. -/
theorem ClassFunction.IsChar.exists_irr_of_cfInner_self_eq_one {K : Type*} [Group K]
    [Fintype K] {φ : ClassFunction K} (hφ : φ.IsChar) (hnorm : ⟪φ, φ⟫_[K] = 1) :
    ∃ χ : Irr K, (χ : ClassFunction K) = φ := by
  rcases hφ.isVirtualChar.exists_eq_or_eq_neg_of_cfInner_self_eq_one hnorm with
    ⟨χ, hχ⟩ | ⟨χ, hχ⟩
  · exact ⟨χ, hχ.symm⟩
  · exfalso
    obtain ⟨n, hn⟩ := hφ.cfInner_mem_nat χ
    have hneg : ⟪φ, (χ : ClassFunction K)⟫_[K] = -1 := by
      rw [hχ, show (-(χ : ClassFunction K)) = (-1 : ℂ) • (χ : ClassFunction K) from
          (neg_one_smul ℂ _).symm, ClassFunction.cfInner_smul_left, Irr.cfInner_eq]
      simp
    rw [hneg] at hn
    have hz : (n : ℤ) = -1 := by exact_mod_cast hn.symm
    omega


namespace PF1

/-! ### Character values at inverses -/

section CharInv

variable {G : Type u} [Group G] [Fintype G]

/-- `χ(g⁻¹) = conj (χ g)` for an irreducible character.  MathComp: `irr_inv`/`char_inv`
(`character.v`). -/
theorem Irr.apply_inv (χ : Irr G) (g : G) : χ g⁻¹ = starRingEnd ℂ (χ g) := by
  obtain ⟨N, hN, hχ⟩ := χ.exists_simple'
  have hval : ∀ x : G, χ x = (Representation.ofModule' (k := ℂ) (G := G) N).character x := by
    intro x
    have h := congrArg (fun φ : ClassFunction G => φ x) hχ
    simpa [MonoidAlgebra.moduleCharacter_eq_ofModule'_character] using h
  rw [hval g⁻¹, hval g, Representation.char_inv]

/-- **The sum of squares of character values at `g`** equals `|C_G(g)|` when `g` is
conjugate to its inverse; a consequence of the second orthogonality relation and
`χ(g⁻¹) = conj (χ g)`.  MathComp: the `g ~ g⁻¹` specialization of
`second_orthogonality_relation`. -/
theorem sum_sq_apply_of_isConj_inv {g : G} (h : IsConj g g⁻¹) :
    ∑ χ : Irr G, (χ g) ^ 2 = (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  have h2 := Irr.second_orthogonality g g⁻¹
  rw [if_pos h] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun χ _ => by rw [Irr.apply_inv, Complex.conj_conj, sq]

/-- **The sum of squares of character values at `g`** vanishes when `g` is not conjugate to
its inverse.  MathComp: the `g ≁ g⁻¹` specialization of `second_orthogonality_relation`. -/
theorem sum_sq_apply_of_not_isConj_inv {g : G} (h : ¬ IsConj g g⁻¹) :
    ∑ χ : Irr G, (χ g) ^ 2 = 0 := by
  have h2 := Irr.second_orthogonality g g⁻¹
  rw [if_neg h] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun χ _ => by rw [Irr.apply_inv, Complex.conj_conj, sq]

end CharInv

/-! ### (1.1) Odd order: the principal character is the only real irreducible character -/

section OddConj

variable {G : Type u} [Group G]

/-- In a group of odd order, an element conjugate to its own inverse is the identity.  This is
the group-theoretic core of Peterfalvi (1.1). -/
theorem eq_one_of_isConj_inv [Finite G] (hodd : Odd (Nat.card G)) {g : G}
    (h : IsConj g g⁻¹) : g = 1 := by
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  -- `c * c` centralizes `g`
  have step1 : c * c * g * (c * c)⁻¹ = g := by
    have e1 : c * c * g * (c * c)⁻¹ = c * (c * g * c⁻¹) * c⁻¹ := by group
    rw [e1, hc]
    have e2 : c * g⁻¹ * c⁻¹ = (c * g * c⁻¹)⁻¹ := by group
    rw [e2, hc, inv_inv]
  have hcc : c * c * g = g * (c * c) := by
    calc c * c * g = (c * c * g * (c * c)⁻¹) * (c * c) := by rw [inv_mul_cancel_right]
      _ = g * (c * c) := by rw [step1]
  have hcomm2 : Commute (c ^ 2) g := by
    change c ^ 2 * g = g * c ^ 2
    rw [pow_two]
    exact hcc
  -- `orderOf c` is odd, so `c` is an even power of itself, hence a power of `c²`
  have hcard_odd : Odd (Fintype.card G) := by rwa [Nat.card_eq_fintype_card] at hodd
  have hdvd : orderOf c ∣ Fintype.card G := orderOf_dvd_card
  have hn_odd : Odd (orderOf c) :=
    Nat.coprime_two_right.mp
      (Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_two_right.mpr hcard_odd))
  obtain ⟨m, hm⟩ := hn_odd
  have hc_eq : (c ^ 2) ^ (m + 1) = c := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf c + 1 from by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hcomm_c : Commute c g := by
    have := hcomm2.pow_left (m + 1)
    rwa [hc_eq] at this
  -- with `c` centralizing `g`, the conjugation relation forces `g = g⁻¹`
  have hcg : c * g * c⁻¹ = g := by rw [hcomm_c.eq, mul_inv_cancel_right]
  have hgg : g = g⁻¹ := hcg.symm.trans hc
  have hg2 : g * g = 1 := mul_eq_one_iff_eq_inv.mpr hgg
  have ho2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
  have hcop2 : Nat.gcd 2 (Fintype.card G) = 1 := Nat.coprime_two_left.mpr hcard_odd
  have hg1 : orderOf g ∣ 1 := by
    have hd := Nat.dvd_gcd ho2 (orderOf_dvd_card (x := g))
    rwa [hcop2] at hd
  rw [← orderOf_eq_one_iff]
  exact Nat.dvd_one.mp hg1

open scoped Classical in
/-- **Peterfalvi (1.1)**: in a group of odd order, an irreducible character is fixed by
complex conjugation iff it is the principal character (i.e. the only real-valued irreducible
character of an odd-order group is the trivial one).  MathComp/Coq: `odd_eq_conj_irr1`
(`PFsection1.v`). -/
theorem odd_eq_conj_irr1 [Fintype G] (hodd : Odd (Nat.card G)) (χ : Irr G) :
    χ.conj = χ ↔ χ = Irr.one := by
  classical
  have hG0 : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- the number of conjugation-fixed irreducibles, computed two ways
  set R := (Finset.univ.filter fun ψ : Irr G => ψ.conj = ψ).card with hRdef
  -- via orthogonality, `∑ (if ψ.conj = ψ then 1 else 0) = R`
  have hS1 : ∑ ψ : Irr G, (if ψ.conj = ψ then (1 : ℂ) else 0) = (R : ℂ) := by
    rw [Finset.sum_boole]
  -- `|C_G(1)| = |G|`, extracted as a cast identity
  have hC1 : (Nat.card (Subgroup.centralizer ({(1 : G)} : Set G)) : ℂ) = (Fintype.card G : ℂ) := by
    have htop : Subgroup.centralizer ({(1 : G)} : Set G) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_iff]
    rw [htop, Nat.card_congr (Subgroup.topEquiv (G := G)).toEquiv, Nat.card_eq_fintype_card]
  -- via the second orthogonality relation, the same sum is `1`
  have hS2 : ∑ ψ : Irr G, (if ψ.conj = ψ then (1 : ℂ) else 0) = 1 := by
    have hterm : ∀ ψ : Irr G, (if ψ.conj = ψ then (1 : ℂ) else 0)
        = ⟪(ψ.conj : ClassFunction G), (ψ : ClassFunction G)⟫_[G] := by
      intro ψ
      rw [Irr.cfInner_eq]
    rw [Finset.sum_congr rfl fun ψ _ => hterm ψ]
    have hexpand : ∀ ψ : Irr G, ⟪(ψ.conj : ClassFunction G), (ψ : ClassFunction G)⟫_[G]
        = (Fintype.card G : ℂ)⁻¹
            * ∑ g : G, starRingEnd ℂ (ψ g) * starRingEnd ℂ (ψ g) := by
      intro ψ
      simp only [ClassFunction.cfInner_def, Irr.coe_apply, Irr.conj_apply]
    -- the diagonal sum ∑_g ∑_ψ (ψ g)² collapses to |C_G(1)| = |G| in odd order
    have hdiag : ∑ g : G, ∑ ψ : Irr G, (ψ g) ^ 2 = (Fintype.card G : ℂ) := by
      rw [Finset.sum_eq_single (1 : G)]
      · rw [sum_sq_apply_of_isConj_inv (show IsConj (1 : G) (1 : G)⁻¹ by rw [inv_one]), hC1]
      · intro g _ hg1
        exact sum_sq_apply_of_not_isConj_inv fun hcj => hg1 (eq_one_of_isConj_inv hodd hcj)
      · intro h; exact absurd (Finset.mem_univ (1 : G)) h
    calc ∑ ψ : Irr G, ⟪(ψ.conj : ClassFunction G), (ψ : ClassFunction G)⟫_[G]
        = ∑ ψ : Irr G, (Fintype.card G : ℂ)⁻¹
            * ∑ g : G, starRingEnd ℂ (ψ g) * starRingEnd ℂ (ψ g) :=
          Finset.sum_congr rfl fun ψ _ => hexpand ψ
      _ = (Fintype.card G : ℂ)⁻¹
            * ∑ g : G, ∑ ψ : Irr G, starRingEnd ℂ (ψ g) * starRingEnd ℂ (ψ g) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ = (Fintype.card G : ℂ)⁻¹
            * ∑ g : G, starRingEnd ℂ (∑ ψ : Irr G, (ψ g) ^ 2) := by
          congr 1
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [map_sum]
          exact Finset.sum_congr rfl fun ψ _ => by rw [← map_mul, sq]
      _ = (Fintype.card G : ℂ)⁻¹ * starRingEnd ℂ (∑ g : G, ∑ ψ : Irr G, (ψ g) ^ 2) := by
          rw [map_sum]
      _ = (Fintype.card G : ℂ)⁻¹ * (Fintype.card G : ℂ) := by
          rw [hdiag, map_natCast]
      _ = 1 := inv_mul_cancel₀ hG0
  -- so exactly one irreducible character is conjugation-fixed
  have hR1 : R = 1 := by
    have : (R : ℂ) = 1 := hS1.symm.trans hS2
    exact_mod_cast this
  -- and the trivial character is one such, hence the unique one
  have hmemFilter : ∀ ψ : Irr G, ψ ∈ Finset.univ.filter (fun ψ : Irr G => ψ.conj = ψ)
      ↔ ψ.conj = ψ := fun ψ => by simp
  obtain ⟨ψ₀, hψ₀⟩ := Finset.card_eq_one.mp hR1
  have hone_mem : (Irr.one : Irr G).conj = Irr.one := Irr.conj_one
  constructor
  · intro h
    have hχmem : χ ∈ Finset.univ.filter (fun ψ : Irr G => ψ.conj = ψ) :=
      (hmemFilter χ).mpr h
    have honemem : (Irr.one : Irr G) ∈ Finset.univ.filter (fun ψ : Irr G => ψ.conj = ψ) :=
      (hmemFilter Irr.one).mpr hone_mem
    rw [hψ₀, Finset.mem_singleton] at hχmem honemem
    rw [hχmem, honemem]
  · rintro rfl
    exact hone_mem

end OddConj

section

/-! ### Small arithmetic helpers -/

/-- A residue-preserving congruence transports coprimality with the modulus. -/
private theorem coprime_of_modEq {x y m : ℕ} (h : x ≡ y [MOD m]) (hy : y.Coprime m) :
    x.Coprime m := by
  unfold Nat.Coprime at *
  rw [Nat.gcd_comm, Nat.gcd_rec, h, ← Nat.gcd_rec, Nat.gcd_comm]
  exact hy

/-- If `z ^ a = 1` and `p ≡ q [MOD a]`, then `z ^ p = z ^ q`. -/
private theorem pow_eq_pow_of_modEq {z : ℂ} {a p q : ℕ} (hz : z ^ a = 1) (h : p ≡ q [MOD a]) :
    z ^ p = z ^ q := by
  have h' : p % a = q % a := h
  rw [pow_eq_pow_mod p hz, pow_eq_pow_mod q hz, h']

/-! ### Helper lemmas on ring homomorphisms and virtual characters -/

/-- Ring homomorphisms of `ℂ` that agree on `n`-th roots of unity agree on virtual-character
values at elements whose order divides `n`.  The character-theoretic engine behind
`dvd_restrict_cfAut`. -/
theorem ringHom_congr_apply_of_orderOf_dvd {G₀ : Type*} [Group G₀] [Fintype G₀]
    (u v : ℂ →+* ℂ) {n : ℕ} (h : ∀ z : ℂ, z ^ n = 1 → u z = v z)
    {χ : ClassFunction G₀} (hχ : χ.IsVirtualChar) {x : G₀} (hx : orderOf x ∣ n) :
    u (χ x) = v (χ x) := by
  have hirr : ∀ ψ : Irr G₀, u (ψ x) = v (ψ x) := by
    intro ψ
    obtain ⟨N, hN, hψ⟩ := ψ.exists_simple'
    have happ : ψ x = trace ℂ N (MonoidAlgebra.actionEnd (↥N) x) := by
      have hc := congrArg (fun φ : ClassFunction G₀ => φ x) hψ
      simpa [MonoidAlgebra.moduleCharacter_apply] using hc
    have hord : orderOf x ≠ 0 := (orderOf_pos x).ne'
    have hpow1 : (MonoidAlgebra.actionEnd (↥N) x) ^ orderOf x = 1 := by
      rw [← MonoidAlgebra.ofModule'_eq_actionEnd, ← map_pow, pow_orderOf_eq_one, map_one]
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / orderOf x) with hζdef
    have hζ : IsPrimitiveRoot ζ (orderOf x) := Complex.isPrimitiveRoot_exp (orderOf x) hord
    obtain ⟨m, hm⟩ := Module.End.trace_eq_sum_zeta_pow_mul_natCast hord hpow1 hζ
    have h1 : ψ x = ∑ j ∈ range (orderOf x), ζ ^ j * (m j : ℂ) := by
      rw [happ]
      have hh := hm 1
      simpa [pow_one] using hh
    have hroot : ∀ j, (ζ ^ j) ^ n = 1 := by
      intro j
      obtain ⟨k, hk⟩ := hx
      have h2 : (ζ ^ j) ^ (orderOf x * k) = (ζ ^ orderOf x) ^ (j * k) := by
        rw [← pow_mul, ← pow_mul, mul_left_comm j (orderOf x) k]
      rw [hk, h2, hζ.pow_eq_one, one_pow]
    rw [h1, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, map_natCast, map_natCast, h _ (hroot j)]
  obtain ⟨c, hc⟩ := hχ
  have hcx : χ x = ∑ ψ : Irr G₀, (c ψ : ℂ) * ψ x := by
    have hh := congrArg (fun φ : ClassFunction G₀ => φ x) hc
    simpa [ClassFunction.sum_apply, ClassFunction.smul_apply, smul_eq_mul] using hh
  rw [hcx, map_sum, map_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [map_mul, map_mul, map_intCast, map_intCast, hirr ψ]

/-- A ring homomorphism raising `n`-th roots of unity to their `k`-th power sends
virtual-character values `χ x` to `χ (x ^ k)`, for elements `x` whose order divides `n`.
The character-theoretic engine behind the `k`-th power twist of `make_pi_cfAut`. -/
theorem ringHom_apply_eq_apply_pow_of_orderOf_dvd {G₀ : Type*} [Group G₀] [Fintype G₀]
    (v : ℂ →+* ℂ) {n k : ℕ} (hv : ∀ z : ℂ, z ^ n = 1 → v z = z ^ k)
    {χ : ClassFunction G₀} (hχ : χ.IsVirtualChar) {x : G₀} (hx : orderOf x ∣ n) :
    v (χ x) = χ (x ^ k) := by
  have hirr : ∀ ψ : Irr G₀, v (ψ x) = ψ (x ^ k) := by
    intro ψ
    obtain ⟨N, hN, hψ⟩ := ψ.exists_simple'
    have happ : ∀ y : G₀, ψ y = trace ℂ N (MonoidAlgebra.actionEnd (↥N) y) := by
      intro y
      have hc := congrArg (fun φ : ClassFunction G₀ => φ y) hψ
      simpa [MonoidAlgebra.moduleCharacter_apply] using hc
    have hord : orderOf x ≠ 0 := (orderOf_pos x).ne'
    have hpow1 : (MonoidAlgebra.actionEnd (↥N) x) ^ orderOf x = 1 := by
      rw [← MonoidAlgebra.ofModule'_eq_actionEnd, ← map_pow, pow_orderOf_eq_one, map_one]
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / orderOf x) with hζdef
    have hζ : IsPrimitiveRoot ζ (orderOf x) := Complex.isPrimitiveRoot_exp (orderOf x) hord
    obtain ⟨m, hm⟩ := Module.End.trace_eq_sum_zeta_pow_mul_natCast hord hpow1 hζ
    have h1 : ψ x = ∑ j ∈ range (orderOf x), ζ ^ j * (m j : ℂ) := by
      rw [happ x]
      have hh := hm 1
      simpa [pow_one] using hh
    have hk' : ψ (x ^ k) = ∑ j ∈ range (orderOf x), (ζ ^ j) ^ k * (m j : ℂ) := by
      rw [happ (x ^ k), MonoidAlgebra.actionEnd_pow]
      exact hm k
    have hroot : ∀ j, (ζ ^ j) ^ n = 1 := by
      intro j
      obtain ⟨l, hl⟩ := hx
      have h2 : (ζ ^ j) ^ (orderOf x * l) = (ζ ^ orderOf x) ^ (j * l) := by
        rw [← pow_mul, ← pow_mul, mul_left_comm j (orderOf x) l]
      rw [hl, h2, hζ.pow_eq_one, one_pow]
    rw [h1, hk', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_natCast, hv _ (hroot j)]
  obtain ⟨c, hc⟩ := hχ
  have hcx : χ x = ∑ ψ : Irr G₀, (c ψ : ℂ) * ψ x := by
    have hh := congrArg (fun φ : ClassFunction G₀ => φ x) hc
    simpa [ClassFunction.sum_apply, ClassFunction.smul_apply, smul_eq_mul] using hh
  have hcxk : χ (x ^ k) = ∑ ψ : Irr G₀, (c ψ : ℂ) * ψ (x ^ k) := by
    have hh := congrArg (fun φ : ClassFunction G₀ => φ (x ^ k)) hc
    simpa [ClassFunction.sum_apply, ClassFunction.smul_apply, smul_eq_mul] using hh
  rw [hcx, map_sum, hcxk]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [map_mul, map_intCast, hirr ψ]

/-- The value at the identity of a virtual character is an integer cast. -/
theorem ClassFunction.IsVirtualChar.exists_intCast_apply_one {G₀ : Type*} [Group G₀]
    [Fintype G₀] {χ : ClassFunction G₀} (hχ : χ.IsVirtualChar) : ∃ z : ℤ, χ 1 = (z : ℂ) := by
  obtain ⟨c, hc⟩ := hχ
  have hcx : χ 1 = ∑ ψ : Irr G₀, (c ψ : ℂ) * ψ 1 := by
    have hh := congrArg (fun φ : ClassFunction G₀ => φ 1) hc
    simpa [ClassFunction.sum_apply, ClassFunction.smul_apply, smul_eq_mul] using hh
  choose d hd_pos hd using fun ψ : Irr G₀ => ψ.exists_degree
  refine ⟨∑ ψ : Irr G₀, c ψ * (d ψ : ℤ), ?_⟩
  rw [hcx, Int.cast_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [hd ψ, Int.cast_mul, Int.cast_natCast]

/-! ### Peterfalvi (1.9)(a) -/

/-- **Peterfalvi (1.9)(a)** (Coq `extend_coprime_Qn_aut`).  For coprime nonzero `a, b` and a
ring endomorphism `μ` of `ℂ`, there is a ring automorphism `ν` of `ℂ` agreeing with `μ` on
`a`-th roots of unity and fixing every `b`-th root of unity.  Phrased through roots of unity
rather than the abstract number fields `ℚ(w_a)`, `ℚ(w_b)` of MathComp; see the module
docstring. -/
theorem extend_coprime_Qn_aut {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b)
    (μ : ℂ →+* ℂ) :
    ∃ ν : ℂ ≃+* ℂ, (∀ z : ℂ, z ^ a = 1 → ν z = μ z) ∧ (∀ z : ℂ, z ^ b = 1 → ν z = z) := by
  haveI : NeZero a := ⟨ha⟩
  set w : ℂ := Complex.exp (2 * Real.pi * Complex.I / a) with hwdef
  have hw : IsPrimitiveRoot w a := Complex.isPrimitiveRoot_exp a ha
  have hμw : IsPrimitiveRoot (μ w) a := hw.map_of_injective (RingHom.injective μ)
  obtain ⟨k, hk_lt, hk⟩ := hw.eq_pow_of_pow_eq_one hμw.pow_eq_one
  have hka : k.Coprime a :=
    (hw.pow_iff_coprime (Nat.pos_of_ne_zero ha) k).mp (hk ▸ hμw)
  set k1 : ℕ := (Nat.chineseRemainder hab k 1).1 with hk1def
  have hk1a : k1 ≡ k [MOD a] := (Nat.chineseRemainder hab k 1).2.1
  have hk1b : k1 ≡ 1 [MOD b] := (Nat.chineseRemainder hab k 1).2.2
  have hk1cop : k1.Coprime (a * b) :=
    Nat.coprime_mul_iff_right.mpr
      ⟨coprime_of_modEq hk1a hka, coprime_of_modEq hk1b (Nat.coprime_one_left b)⟩
  obtain ⟨ν, hν⟩ := Complex.exists_ringEquiv_pow_of_coprime (mul_ne_zero ha hb) hk1cop
  refine ⟨ν, ?_, ?_⟩
  · intro z hz
    have hzab : z ^ (a * b) = 1 := by rw [pow_mul, hz, one_pow]
    rw [hν z hzab]
    obtain ⟨i, hi_lt, rfl⟩ := hw.eq_pow_of_pow_eq_one hz
    rw [map_pow, ← hk, ← pow_mul, ← pow_mul]
    apply pow_eq_pow_of_modEq hw.pow_eq_one
    rw [mul_comm k i]
    exact hk1a.mul_left i
  · intro z hz
    have hzab : z ^ (a * b) = 1 := by rw [mul_comm, pow_mul, hz, one_pow]
    rw [hν z hzab]
    have hz1 : z ^ k1 = z ^ 1 := pow_eq_pow_of_modEq hz hk1b
    rw [hz1, pow_one]

/-! ### Peterfalvi (1.9)(b), intermediate and full -/

/-- **Intermediate lemma for Peterfalvi (1.9)(b)** (Coq `dvd_restrict_cfAut`; used later by
Peterfalvi (3.9)(c)).  For any `a` and ring endomorphism `v` of `ℂ`, there is a ring
endomorphism `u` of `ℂ` that (uniformly over *all* finite groups `G₀`) acts like `v` on
virtual-character values at elements of order dividing `a`, and acts as the identity on
virtual-character values (over `G`) at elements of order coprime to `a`. -/
theorem dvd_restrict_cfAut {G : Type u} [Group G] [Fintype G] (a : ℕ) (v : ℂ →+* ℂ) :
    ∃ u : ℂ →+* ℂ,
      (∀ (G₀ : Type v) [Group G₀] [Fintype G₀] (χ : ClassFunction G₀) (x : G₀),
        χ.IsVirtualChar → orderOf x ∣ a → u (χ x) = v (χ x)) ∧
      (∀ (χ : ClassFunction G) (x : G), χ.IsVirtualChar → (orderOf x).Coprime a →
        u (χ x) = χ x) := by
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    refine ⟨v, fun G₀ _ _ χ x _ _ => rfl, ?_⟩
    intro χ x hχ hcop
    rw [Nat.coprime_zero_right] at hcop
    have hx1 : x = 1 := orderOf_eq_one_iff.mp hcop
    subst hx1
    obtain ⟨z, hz⟩ := ClassFunction.IsVirtualChar.exists_intCast_apply_one hχ
    rw [hz, map_intCast]
  · have ha : a ≠ 0 := hapos.ne'
    set b : ℕ := ∏ x ∈ Finset.univ.filter (fun x : G => (orderOf x).Coprime a), orderOf x
      with hbdef
    have hb : b ≠ 0 := by
      rw [hbdef, Finset.prod_ne_zero_iff]
      exact fun x _ => (orderOf_pos x).ne'
    have hab : a.Coprime b := by
      rw [hbdef]
      refine Nat.Coprime.prod_right ?_
      intro x hx
      rw [Finset.mem_filter] at hx
      exact hx.2.symm
    obtain ⟨ν, hνa, hνb⟩ := extend_coprime_Qn_aut ha hb hab v
    refine ⟨(ν : ℂ →+* ℂ), ?_, ?_⟩
    · intro G₀ _ _ χ x hχ hdvd
      exact ringHom_congr_apply_of_orderOf_dvd (ν : ℂ →+* ℂ) v (fun z hz => hνa z hz) hχ hdvd
    · intro χ x hχ hcop
      have hmem : x ∈ Finset.univ.filter (fun x : G => (orderOf x).Coprime a) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ x, hcop⟩
      have hdvd : orderOf x ∣ b := by
        rw [hbdef]
        exact Finset.dvd_prod_of_mem _ hmem
      have hval := ringHom_congr_apply_of_orderOf_dvd (ν : ℂ →+* ℂ) (RingHom.id ℂ)
        (fun z hz => (hνb z hz).trans (RingHom.id_apply z).symm) hχ hdvd
      rw [RingHom.id_apply] at hval
      exact hval

/-- **Peterfalvi (1.9)(b)** (Coq `make_pi_cfAut`).  For `k` coprime to `a`, there is a ring
endomorphism `u` of `ℂ` that (uniformly over all finite groups `G₀`) sends virtual-character
values `χ x` to `χ (x ^ k)` at elements of order dividing `a`, and acts as the identity on
virtual-character values (over `G`) at elements of order coprime to `a`.  MathComp's
`cfAut u chi x` is spelled valuewise as `u (chi x)`. -/
theorem make_pi_cfAut {G : Type u} [Group G] [Fintype G] {k a : ℕ} (hka : Nat.Coprime k a) :
    ∃ u : ℂ →+* ℂ,
      (∀ (G₀ : Type v) [Group G₀] [Fintype G₀] (χ : ClassFunction G₀) (x : G₀),
        χ.IsVirtualChar → orderOf x ∣ a → u (χ x) = χ (x ^ k)) ∧
      (∀ (χ : ClassFunction G) (x : G), χ.IsVirtualChar → (orderOf x).Coprime a →
        u (χ x) = χ x) := by
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    have hk1 : k = 1 := (Nat.coprime_zero_right k).mp hka
    subst hk1
    refine ⟨RingHom.id ℂ, ?_, ?_⟩
    · intro G₀ _ _ χ x _ _
      rw [RingHom.id_apply, pow_one]
    · intro χ x _ _
      rw [RingHom.id_apply]
  · have ha : a ≠ 0 := hapos.ne'
    obtain ⟨σ, hσ⟩ := Complex.exists_ringEquiv_pow_of_coprime ha hka
    obtain ⟨u, hu1, hu2⟩ := dvd_restrict_cfAut (G := G) a (σ : ℂ →+* ℂ)
    refine ⟨u, ?_, ?_⟩
    · intro G₀ _ _ χ x hχ hdvd
      rw [hu1 G₀ χ x hχ hdvd]
      exact ringHom_apply_eq_apply_pow_of_orderOf_dvd (σ : ℂ →+* ℂ)
        (fun z hz => hσ z hz) hχ hdvd
    · intro χ x hχ hcop
      exact hu2 χ x hχ hcop

/-! ### The `eqAmod` mini-API -/

/-- `x ≡ y %[mod e]` over the ring of algebraic integers: `x - y = e * z` for an algebraic
integer `z`.  MathComp: `eqAmod` (`algnum.v`), with the global ring of algebraic integers
substituted for `ℤ[η]` per the Coq Section ANT header note. -/
def eqAmod (e x y : ℂ) : Prop := ∃ z : ℂ, IsIntegral ℤ z ∧ x - y = e * z

theorem eqAmod_refl (e x : ℂ) : eqAmod e x x :=
  ⟨0, isIntegral_zero, by rw [sub_self, mul_zero]⟩

theorem eqAmod.symm {e x y : ℂ} (h : eqAmod e x y) : eqAmod e y x := by
  obtain ⟨z, hz, hzeq⟩ := h
  exact ⟨-z, hz.neg, by rw [mul_neg, ← hzeq]; ring⟩

theorem eqAmod.trans {e x y z' : ℂ} (h1 : eqAmod e x y) (h2 : eqAmod e y z') :
    eqAmod e x z' := by
  obtain ⟨z, hz, hzeq⟩ := h1
  obtain ⟨w, hw, hweq⟩ := h2
  exact ⟨z + w, hz.add hw, by rw [mul_add, ← hzeq, ← hweq]; ring⟩

theorem eqAmod.add {e x y x' y' : ℂ} (h1 : eqAmod e x y) (h2 : eqAmod e x' y') :
    eqAmod e (x + x') (y + y') := by
  obtain ⟨z, hz, hzeq⟩ := h1
  obtain ⟨w, hw, hweq⟩ := h2
  exact ⟨z + w, hz.add hw, by rw [mul_add, ← hzeq, ← hweq]; ring⟩

/-- MathComp: `eqAmodMl`. -/
theorem eqAmod.mul_left {e x y : ℂ} (c : ℂ) (hc : IsIntegral ℤ c) (h : eqAmod e x y) :
    eqAmod e (c * x) (c * y) := by
  obtain ⟨z, hz, hzeq⟩ := h
  refine ⟨c * z, hc.mul hz, ?_⟩
  have hd : c * x - c * y = c * (x - y) := by ring
  rw [hd, hzeq]; ring

theorem eqAmod_of_eq {e x y : ℂ} (h : x = y) : eqAmod e x y :=
  ⟨0, isIntegral_zero, by rw [h, sub_self, mul_zero]⟩

theorem eqAmod_sum {ι : Type*} {e : ℂ} (s : Finset ι) (f g : ι → ℂ)
    (h : ∀ i ∈ s, eqAmod e (f i) (g i)) : eqAmod e (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  choose! z hz hzeq using h
  refine ⟨∑ i ∈ s, z i, IsIntegral.sum _ fun i hi => hz i hi, ?_⟩
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => hzeq i hi

theorem eqAmod.zsmul {e x y : ℂ} (n : ℤ) (h : eqAmod e x y) :
    eqAmod e ((n : ℂ) * x) ((n : ℂ) * y) :=
  h.mul_left (n : ℂ) (isIntegral_intCast n)

/-! ### Peterfalvi (1.10)(b) -/

/-- **Peterfalvi (1.10)(b)** (Coq `int_eqAmod_prime_prim`; the primality condition is only
needed here).  If `n : ℤ` is congruent to `0` modulo `1 - ε` (over the algebraic integers)
for a primitive `p`-th root of unity `ε` with `p` prime, then `p ∣ n`. -/
theorem int_eqAmod_prime_prim {p : ℕ} (hp : p.Prime) {ε : ℂ} (hε : IsPrimitiveRoot ε p)
    {n : ℤ} (h : eqAmod (1 - ε) (n : ℂ) 0) : (p : ℤ) ∣ n := by
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  obtain ⟨z, hz, hzeq⟩ := h
  rw [sub_zero] at hzeq
  have hp0 : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  have hεint : IsIntegral ℤ ε := hε.isIntegral hp0
  -- product identity: `p = ∏ i ∈ Ico 1 p, (1 - ε ^ i)`
  have hprod : (p : ℂ) = ∏ i ∈ Finset.Ico 1 p, (1 - ε ^ i) := by
    have h1 : (∏ μ ∈ primitiveRoots p ℂ, (1 - μ)) = (p : ℂ) := by
      have hcyc := Polynomial.eval_one_cyclotomic_prime (p := p) (R := ℂ)
      rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hε, Polynomial.eval_prod] at hcyc
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hcyc
      exact hcyc
    rw [← h1]
    refine (Finset.prod_bij (fun i _ => ε ^ i) (fun i hi => ?_) (fun i1 hi1 i2 hi2 he => ?_)
      (fun μ hμ => ?_) (fun i _ => rfl)).symm
    · rw [Finset.mem_Ico] at hi
      rw [mem_primitiveRoots hp0]
      exact hε.pow_of_coprime i
        (Nat.coprime_of_lt_prime (Nat.one_le_iff_ne_zero.mp hi.1) hi.2 hp).symm
    · rw [Finset.mem_Ico] at hi1 hi2
      exact hε.pow_inj hi1.2 hi2.2 he
    · have hμp : IsPrimitiveRoot μ p := (mem_primitiveRoots hp0).mp hμ
      obtain ⟨i, hi_lt, hi_eq⟩ := hε.eq_pow_of_pow_eq_one hμp.pow_eq_one
      have hi1 : 1 ≤ i := by
        by_contra hcon
        have hi0 : i = 0 := by omega
        subst hi0
        rw [pow_zero] at hi_eq
        rw [← hi_eq] at hμp
        have hdvd1 : p ∣ 1 := hμp.dvd_of_pow_eq_one 1 (one_pow 1)
        have hple : p ≤ 1 := Nat.le_of_dvd one_pos hdvd1
        omega
      exact ⟨i, Finset.mem_Ico.mpr ⟨hi1, hi_lt⟩, hi_eq⟩
  -- factor `1 - ε` through each `1 - ε ^ i`
  have hfac : ∀ i ∈ Finset.Ico 1 p, ∃ w : ℂ, IsIntegral ℤ w ∧ 1 - ε = w * (1 - ε ^ i) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hcop : i.Coprime p :=
      (Nat.coprime_of_lt_prime (Nat.one_le_iff_ne_zero.mp hi.1) hi.2 hp).symm
    have hεi : IsPrimitiveRoot (ε ^ i) p := hε.pow_of_coprime i hcop
    obtain ⟨r, hr_lt, hr_eq⟩ := hεi.eq_pow_of_pow_eq_one hε.pow_eq_one
    refine ⟨∑ j ∈ Finset.range r, (ε ^ i) ^ j, IsIntegral.sum _ fun j _ => (hεint.pow i).pow j,
      ?_⟩
    have hgeom := geom_sum_mul (ε ^ i) r
    rw [hr_eq] at hgeom
    have hkey : (∑ j ∈ Finset.range r, (ε ^ i) ^ j) * (1 - ε ^ i)
        = -((∑ j ∈ Finset.range r, (ε ^ i) ^ j) * (ε ^ i - 1)) := by ring
    rw [hkey, hgeom]; ring
  choose! w hw hweq using hfac
  set W : ℂ := ∏ i ∈ Finset.Ico 1 p, w i with hWdef
  have hWint : IsIntegral ℤ W := IsIntegral.prod _ fun i hi => hw i hi
  have hcard : (Finset.Ico 1 p).card = p - 1 := by rw [Nat.card_Ico]
  have hpow_eq : (∏ _i ∈ Finset.Ico 1 p, (1 - ε)) = (1 - ε) ^ (p - 1) := by
    rw [Finset.prod_const, hcard]
  have hprod2 : (∏ _i ∈ Finset.Ico 1 p, (1 - ε))
      = W * ∏ i ∈ Finset.Ico 1 p, (1 - ε ^ i) := by
    rw [hWdef, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i hi => hweq i hi
  have hfinal : (1 - ε) ^ (p - 1) = W * (p : ℂ) := by
    rw [← hpow_eq, hprod2, ← hprod]
  have hMint : IsIntegral ℤ (W * z ^ (p - 1)) := hWint.mul (hz.pow _)
  have hn_pow : (n : ℂ) ^ (p - 1) = (p : ℂ) * (W * z ^ (p - 1)) := by
    rw [hzeq, mul_pow, hfinal]; ring
  set q : ℚ := (n : ℚ) ^ (p - 1) / (p : ℚ) with hqdef
  have hq_map : algebraMap ℚ ℂ q = W * z ^ (p - 1) := by
    rw [hqdef, map_div₀, map_pow, map_intCast, map_natCast, div_eq_iff hpC, hn_pow]; ring
  have hqint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp (hq_map ▸ hMint)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqint
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  have hyq : (n : ℚ) ^ (p - 1) = (p : ℚ) * (y : ℚ) := by
    have hyc : (y : ℚ) = q := by rw [← hy]; exact (eq_intCast (algebraMap ℤ ℚ) y).symm
    rw [hqdef, eq_div_iff hpQ] at hyc
    rw [← hyc]; ring
  have hyz : n ^ (p - 1) = (p : ℤ) * y := by exact_mod_cast hyq
  exact (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow ⟨y, hyz⟩

end

/-! ### (1.10)(a) Congruence of virtual-character values modulo `1 - ε` -/

section ANT

variable {G : Type u} [Group G] [Fintype G]

/-- **Peterfalvi (1.10)(a)**: for `x` of prime order `p`, `y` commuting with `x`, `ε` a
primitive `p`-th root of unity, and `χ` a virtual character of `G`,
`χ (x * y) ≡ χ y  (mod 1 - ε)` in the ring of algebraic integers.  MathComp/Coq:
`vchar_ker_mod_prim` (`PFsection1.v`).  We use the global ring of algebraic integers for
`ℤ[ε]` (the Coq's documented simplification). -/
theorem vchar_ker_mod_prim {p : ℕ} {ε : ℂ} (hε : IsPrimitiveRoot ε p)
    {χ : ClassFunction G} (hχ : χ.IsVirtualChar) {x y : G}
    (hx : orderOf x = p) (hxy : Commute x y) :
    eqAmod (1 - ε) (χ (x * y)) (χ y) := by
  classical
  have hp0 : p ≠ 0 := by rw [← hx]; exact (orderOf_pos x).ne'
  haveI : NeZero p := ⟨hp0⟩
  have hεI : IsIntegral ℤ ε :=
    ⟨Polynomial.X ^ p - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hp0, by
      simp [hε.pow_eq_one]⟩
  set X := Subgroup.closure ({x, y} : Set G) with hXdef
  haveI : Fintype ↥X := Fintype.ofFinite _
  have hxX : x ∈ X := Subgroup.subset_closure (by simp)
  have hyX : y ∈ X := Subgroup.subset_closure (by simp)
  have hxyX : x * y ∈ X := X.mul_mem hxX hyX
  -- every element of `X` commutes with `x` and with `y`
  have hgen : ∀ a ∈ X, Commute a x ∧ Commute a y := by
    intro a ha
    refine Subgroup.closure_induction ?_ ⟨Commute.one_left x, Commute.one_left y⟩
      (fun u v _ _ ihu ihv => ⟨ihu.1.mul_left ihv.1, ihu.2.mul_left ihv.2⟩)
      (fun u _ ihu => ⟨ihu.1.inv_left, ihu.2.inv_left⟩) ha
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨Commute.refl z, hxy⟩
    · exact ⟨hxy.symm, Commute.refl z⟩
  -- hence `X` is commutative
  have hXcomm : ∀ a b : ↥X, a * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have hcomm : Commute a b := by
      refine Subgroup.closure_induction ?_ (Commute.one_right a)
        (fun u v _ _ ihu ihv => ihu.mul_right ihv) (fun u _ ihu => ihu.inv_right) hb
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact (hgen a ha).1
      · exact (hgen a ha).2
    exact Subtype.ext hcomm
  -- the restriction of `χ` to `X` is a virtual character of `X`
  have hχ'v : (ClassFunction.res X χ).IsVirtualChar := by
    obtain ⟨φ₁, φ₂, h1, h2, hsub⟩ := hχ.exists_isChar_sub
    rw [hsub, map_sub]
    exact (h1.res).sub_isVirtualChar h2.res
  obtain ⟨c, hc⟩ := hχ'v
  -- per-linear-character congruence: `ξ (x*y) ≡ ξ y (mod 1 - ε)`
  have hper : ∀ ξ : Irr ↥X,
      eqAmod (1 - ε) (ξ ⟨x * y, hxyX⟩) (ξ ⟨y, hyX⟩) := by
    intro ξ
    have hlin : ξ.IsLinear := Irr.isLinear_of_comm hXcomm ξ
    have hxp : (ξ ⟨x, hxX⟩) ^ p = 1 := by
      have hpow := hlin.apply_pow_orderOf_eq_one ⟨x, hxX⟩
      rwa [Subgroup.orderOf_mk x hxX, hx] at hpow
    obtain ⟨k, -, hk⟩ := hε.eq_pow_of_pow_eq_one hxp
    have hmul : ξ ⟨x * y, hxyX⟩ = ε ^ k * ξ ⟨y, hyX⟩ := by
      have hsplit : (⟨x * y, hxyX⟩ : ↥X) = ⟨x, hxX⟩ * ⟨y, hyX⟩ := Subtype.ext rfl
      rw [hsplit, hlin.map_mul, hk]
    refine ⟨-(∑ j ∈ Finset.range k, ε ^ j) * ξ ⟨y, hyX⟩, ?_, ?_⟩
    · exact IsIntegral.mul
        (IsIntegral.neg (IsIntegral.sum _ fun j _ => hεI.pow j))
        (Irr.isIntegral_apply ξ ⟨y, hyX⟩)
    · rw [hmul]
      linear_combination (-(ξ ⟨y, hyX⟩)) * geom_sum_mul ε k
  -- expand `χ` on `X` in the basis of irreducible characters of `X`
  have hval : ∀ (a : G) (ha : a ∈ X), χ a = ∑ ξ : Irr ↥X, (c ξ : ℂ) * ξ ⟨a, ha⟩ := by
    intro a ha
    have h := congrArg (fun φ : ClassFunction ↥X => φ ⟨a, ha⟩) hc
    rw [ClassFunction.res_apply] at h
    rw [h, ClassFunction.sum_apply]
    exact Finset.sum_congr rfl fun ξ _ => by
      rw [ClassFunction.smul_apply, smul_eq_mul, Irr.coe_apply]
  rw [hval (x * y) hxyX, hval y hyX]
  exact eqAmod_sum Finset.univ _ _ fun ξ _ =>
    eqAmod.mul_left (c ξ : ℂ) (isIntegral_intCast (c ξ)) (hper ξ)

end ANT

section

variable {G : Type u} [Group G] [Fintype G] {H : Subgroup G} [hHN : H.Normal] [Fintype H]

omit [Fintype G] in
/-- The relative index `H.relIndex θ.inertia` (MathComp `#|'I_G['chi_t] : H|`) is nonzero,
since `H ≤ inertia θ` inside the finite group `θ.inertia`. -/
theorem relIndex_ne_zero [Finite G] (θ : Irr H) : H.relIndex θ.inertia ≠ 0 := by
  have h : (H.subgroupOf θ.inertia).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  exact h

/-- **Peterfalvi (1.5)(a)** (`cfResInd_sum_cfclass`): the restriction of an induced
irreducible character is the scaled sum over the conjugation orbit,
`'Res[H] ('Ind[G] 'chi_t) = #|'I_G['chi_t] : H| • ∑_{ξ ∈ 'chi_t ^: G} ξ`. -/
theorem cfResInd_sum_cfclass (θ : Irr H) :
    ClassFunction.res H (ClassFunction.ind H (θ : ClassFunction H))
      = (H.relIndex θ.inertia : ℂ) • ∑ ξ ∈ θ.cfclass, (ξ : ClassFunction H) :=
  θ.res_ind_eq_smul_sum_cfclass

/-- **Peterfalvi (1.5)(b)**, main formula (`cfnorm_Ind_irr`):
`'['Ind[G] 'chi_t] = #|'I_G['chi_t] : H|`.  Frobenius reciprocity turns the norm into
`⟪'Res ('Ind θ), θ⟫`, which is the relative index by `Irr.cfInner_res_ind_self`. -/
theorem cfnorm_Ind_irr (θ : Irr H) :
    ⟪ClassFunction.ind H (θ : ClassFunction H),
        ClassFunction.ind H (θ : ClassFunction H)⟫_[G]
      = (H.relIndex θ.inertia : ℂ) := by
  rw [ClassFunction.cfInner_ind_eq_cfInner_res, ClassFunction.cfInner_conj_symm,
    θ.cfInner_res_ind_self, map_natCast]

/-- **Peterfalvi (1.5)(b)**, irreducibility remark (`inertia_Ind_irr`): if the inertia group
of `θ` is contained in `H` then `'Ind[G] 'chi_t` is irreducible, i.e. equals some
`χ : Irr G`.  Then `θ.inertia = H`, so the norm is `1`, and a norm-`1` character is
irreducible. -/
theorem exists_irr_ind_of_inertia_le (θ : Irr H) (hIH : θ.inertia ≤ H) :
    ∃ χ : Irr G, (χ : ClassFunction G) = ClassFunction.ind H (θ : ClassFunction H) := by
  have heq : θ.inertia = H := le_antisymm hIH θ.le_inertia
  have hnorm : ⟪ClassFunction.ind H (θ : ClassFunction H),
      ClassFunction.ind H (θ : ClassFunction H)⟫_[G] = 1 := by
    rw [cfnorm_Ind_irr, heq, Subgroup.relIndex_self, Nat.cast_one]
  exact (Irr.isChar θ).ind.exists_irr_of_cfInner_self_eq_one hnorm

/-- **Peterfalvi (1.5)(c)** (`cfclass_Ind_cases`): either `θ₂` lies in the conjugation orbit
of `θ₁`, and then their inductions agree, or it does not, and then the inductions are
orthogonal.  (MathComp returns an `if`-`then`-`else` bool; this disjunction is the faithful
shape.) -/
theorem cfclass_Ind_cases (θ₁ θ₂ : Irr H) :
    (θ₂ ∈ θ₁.cfclass ∧ ClassFunction.ind H (θ₁ : ClassFunction H)
        = ClassFunction.ind H (θ₂ : ClassFunction H)) ∨
      (θ₂ ∉ θ₁.cfclass ∧
        ⟪ClassFunction.ind H (θ₁ : ClassFunction H),
          ClassFunction.ind H (θ₂ : ClassFunction H)⟫_[G] = 0) := by
  by_cases h : θ₂ ∈ θ₁.cfclass
  · exact Or.inl ⟨h, (Irr.ind_eq_of_mem_cfclass h).symm⟩
  · refine Or.inr ⟨h, ?_⟩
    rw [ClassFunction.cfInner_ind_right_eq_cfInner_res_left,
      θ₁.res_ind_eq_smul_sum_cfclass, ClassFunction.cfInner_smul_left,
      ClassFunction.cfInner_sum_left]
    have hz : ∑ ξ ∈ θ₁.cfclass, ⟪(ξ : ClassFunction H), (θ₂ : ClassFunction H)⟫_[H] = 0 := by
      refine Finset.sum_eq_zero fun ξ hξ => ?_
      have hne : ξ ≠ θ₂ := by rintro rfl; exact h hξ
      rw [Irr.cfInner_eq, if_neg hne]
    rw [hz, mul_zero]

/-- Consequence of (1.5)(c) (`not_cfclass_Ind_ortho`): inductions of characters in distinct
conjugation orbits are orthogonal. -/
theorem not_cfclass_Ind_ortho {θ₁ θ₂ : Irr H} (h : θ₁ ∉ θ₂.cfclass) :
    ⟪ClassFunction.ind H (θ₁ : ClassFunction H),
      ClassFunction.ind H (θ₂ : ClassFunction H)⟫_[G] = 0 := by
  rcases cfclass_Ind_cases θ₁ θ₂ with ⟨hmem, _⟩ | ⟨_, hortho⟩
  · exact absurd (Irr.mem_cfclass_symm hmem) h
  · exact hortho

/-- Consequence of (1.5)(c) (`cfclass_Ind_irrP`): two irreducible characters of `H` induce the
same class function iff they are `G`-conjugate. -/
theorem cfclass_Ind_irr_iff (θ₁ θ₂ : Irr H) :
    ClassFunction.ind H (θ₁ : ClassFunction H) = ClassFunction.ind H (θ₂ : ClassFunction H)
      ↔ θ₂ ∈ θ₁.cfclass := by
  constructor
  · intro heq
    by_contra hnot
    rcases cfclass_Ind_cases θ₁ θ₂ with ⟨hmem, _⟩ | ⟨_, hortho⟩
    · exact hnot hmem
    · rw [← heq, cfnorm_Ind_irr] at hortho
      exact relIndex_ne_zero θ₁ (by exact_mod_cast hortho)
  · intro h
    exact (Irr.ind_eq_of_mem_cfclass h).symm

/-- **Peterfalvi (1.5)(d)** (`scaled_cfResInd_sum_cfclass`):
`(chiG 1 / '[chiG]) • 'Res chiG = #|G : H| • ∑_{ξ ∈ 'chi_t ^: G} ξ 1 • ξ`, where
`chiG = 'Ind[G] 'chi_t`.  Note the scalar is `H.index` (MathComp's `#|G : H|`), the full
index of `H` in `G`. -/
theorem scaled_cfResInd_sum_cfclass (θ : Irr H) :
    (ClassFunction.ind H (θ : ClassFunction H) 1
        / ⟪ClassFunction.ind H (θ : ClassFunction H),
            ClassFunction.ind H (θ : ClassFunction H)⟫_[G])
      • ClassFunction.res H (ClassFunction.ind H (θ : ClassFunction H))
      = (H.index : ℂ) •
          ∑ ξ ∈ θ.cfclass, (ξ 1 : ℂ) • (ξ : ClassFunction H) := by
  have hr : (H.relIndex θ.inertia : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (relIndex_ne_zero θ)
  have hRHS : ∑ ξ ∈ θ.cfclass, (ξ 1 : ℂ) • (ξ : ClassFunction H)
      = (θ 1 : ℂ) • ∑ ξ ∈ θ.cfclass, (ξ : ClassFunction H) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun ξ hξ => ?_
    obtain ⟨y, rfl⟩ := Irr.mem_cfclass_iff.mp hξ
    congr 1
    rw [Irr.conjg_apply, map_one]
  rw [hRHS, cfnorm_Ind_irr, ClassFunction.ind_apply_one, θ.res_ind_eq_smul_sum_cfclass,
    smul_smul, smul_smul, div_mul_cancel₀ _ hr, Irr.coe_apply]

/-- **Peterfalvi (1.5)(e)** (`odd_induced_orthogonal`): in a group of odd order, an induced
irreducible character from a nonprincipal `θ` is orthogonal to its complex conjugate.  The
Coq proof invokes (1.1) for `H`; here it is discharged internally from `odd_eq_conj_irr1`
(odd order of `H` follows from odd order of `G`). -/
theorem odd_induced_orthogonal (hodd : Odd (Nat.card G)) {θ : Irr H} (hθ : θ ≠ Irr.one) :
    ⟪ClassFunction.ind H (θ : ClassFunction H),
      (ClassFunction.ind H (θ : ClassFunction H)).conjC⟫_[G] = 0 := by
  -- odd order passes to the subgroup `H`, giving (1.1) for `H`
  have oddH : Odd (Nat.card H) :=
    Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_left
      ⟨H.index, (Subgroup.card_mul_index H).symm⟩ (Nat.coprime_two_right.mpr hodd))
  have h11H : ∀ χ : Irr H, χ.conj = χ → χ = Irr.one :=
    fun χ hχ => (odd_eq_conj_irr1 oddH χ).mp hχ
  have hconjC : (ClassFunction.ind H (θ : ClassFunction H)).conjC
      = ClassFunction.ind H (θ.conj : ClassFunction H) := by
    rw [ClassFunction.conjC_ind, Irr.coe_conj]
  rw [hconjC]
  refine not_cfclass_Ind_ortho ?_
  intro hmem
  have hmem' : θ.conj ∈ θ.cfclass := Irr.mem_cfclass_symm hmem
  obtain ⟨g, hg⟩ := Irr.mem_cfclass_iff.mp hmem'
  -- F1: `θ` is fixed by conjugation by `g ^ 2`.
  have F1 : θ.conjg (g * g) = θ := by
    rw [Irr.conjg_mul, hg, ← Irr.conj_conjg, hg, Irr.conj_conj]
  -- Odd order writes `g` as a power of `g ^ 2`, so `g` fixes `θ` too.
  obtain ⟨m, hm⟩ := hodd
  have hg2_mem : g * g ∈ θ.inertia := Irr.mem_inertia.mpr F1
  have hgpow : (g * g) ^ (m + 1) = g := by
    have hcard : g ^ Nat.card G = 1 := pow_card_eq_one'
    have hexp : 2 * (m + 1) = Nat.card G + 1 := by omega
    rw [← pow_two, ← pow_mul, hexp, pow_succ, hcard, one_mul]
  have hg_mem : g ∈ θ.inertia := by
    rw [← hgpow]; exact pow_mem hg2_mem (m + 1)
  have hgθ : θ.conjg g = θ := Irr.mem_inertia.mp hg_mem
  have hconj_eq : θ.conj = θ := by rw [← hg, hgθ]
  exact hθ (h11H θ hconj_eq)

omit [Fintype H] in
/-- **Peterfalvi (1.2)** (`irr_reg_off_ker_0`): if `H ⊴ G`, an irreducible character `χ`
whose kernel does not contain `H`, and `g` centralizes no nontrivial element of `H`, then
`χ g = 0`.

The column of the character table at `g` has squared length `|C_G(g)|` (second
orthogonality).  The sub-column over the characters with `H ≤ ker` reindexes, via the
quotient correspondence, to the column of `G / H` at `gH`, of squared length `|C_{G/H}(gH)|`.
The hypothesis on `g` forces `|C_G(g)| ≤ |C_{G/H}(gH)|`, so the remaining (nonnegative)
squared terms must all vanish — in particular `|χ g|² = 0`. -/
theorem irr_reg_off_ker_0 [Finite (G ⧸ H)] (χ : Irr G) (g : G)
    (hker : ¬ (H ≤ χ.ker))
    (hCH : ∀ h : G, h ∈ H → h * g = g * h → h = 1) :
    χ g = 0 := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  -- Second orthogonality: the squared column length at `g` is `|C_G(g)|`.
  have htotal : ∑ ψ : Irr G, ψ g * starRingEnd ℂ (ψ g)
      = (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
    have h := Irr.second_orthogonality (G := G) g g
    rwa [if_pos (IsConj.refl g)] at h
  -- The sub-column over `{χ | H ≤ ker χ}` is the `G / H`-column at `gH`.
  have hquotfilter : ∑ χ ∈ Finset.univ.filter (fun χ : Irr G => H ≤ χ.ker),
      χ g * starRingEnd ℂ (χ g)
      = (Nat.card (Subgroup.centralizer ({(g : G ⧸ H)} : Set (G ⧸ H))) : ℂ) := by
    haveI hFin : Fintype {χ : Irr G // H ≤ χ.ker} := Fintype.ofFinite _
    have hsub : ∑ χ ∈ Finset.univ.filter (fun χ : Irr G => H ≤ χ.ker),
        χ g * starRingEnd ℂ (χ g)
        = ∑ χ : {χ : Irr G // H ≤ χ.ker},
            (χ : Irr G) g * starRingEnd ℂ ((χ : Irr G) g) :=
      Finset.sum_subtype _ (fun χ => by simp) _
    have hequiv : ∑ ψ : Irr (G ⧸ H), ψ (g : G ⧸ H) * starRingEnd ℂ (ψ (g : G ⧸ H))
        = ∑ χ : {χ : Irr G // H ≤ χ.ker},
            (χ : Irr G) g * starRingEnd ℂ ((χ : Irr G) g) :=
      Fintype.sum_equiv (Irr.quotientKerEquiv H) _ _
        (fun ψ => by simp [Irr.quotientKerEquiv_apply, Irr.mod_apply])
    have hso : ∑ ψ : Irr (G ⧸ H), ψ (g : G ⧸ H) * starRingEnd ℂ (ψ (g : G ⧸ H))
        = (Nat.card (Subgroup.centralizer ({(g : G ⧸ H)} : Set (G ⧸ H))) : ℂ) := by
      have h := Irr.second_orthogonality (G := G ⧸ H) (g : G ⧸ H) (g : G ⧸ H)
      rwa [if_pos (IsConj.refl _)] at h
    rw [hsub, ← hequiv, hso]
  -- The two centralizer counts are related by an injection of `C_G(g)` into `C_{G/H}(gH)`.
  have hcard_le : Nat.card (Subgroup.centralizer ({g} : Set G))
      ≤ Nat.card (Subgroup.centralizer ({(g : G ⧸ H)} : Set (G ⧸ H))) := by
    have hmemc : ∀ c : G, c ∈ Subgroup.centralizer ({g} : Set G) →
        (c : G ⧸ H) ∈ Subgroup.centralizer ({(g : G ⧸ H)} : Set (G ⧸ H)) := by
      intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]
    refine Nat.card_le_card_of_injective
      (fun c => ⟨((c : G) : G ⧸ H), hmemc (c : G) c.2⟩) ?_
    intro c₁ c₂ hceq
    have heq : ((c₁ : G) : G ⧸ H) = ((c₂ : G) : G ⧸ H) := congrArg Subtype.val hceq
    rw [QuotientGroup.eq] at heq
    have hmem_cent : (c₁ : G)⁻¹ * (c₂ : G) ∈ Subgroup.centralizer ({g} : Set G) :=
      mul_mem (inv_mem c₁.2) c₂.2
    have hcomm : ((c₁ : G)⁻¹ * (c₂ : G)) * g = g * ((c₁ : G)⁻¹ * (c₂ : G)) :=
      Subgroup.mem_centralizer_singleton_iff.mp hmem_cent
    have hone : (c₁ : G)⁻¹ * (c₂ : G) = 1 := hCH _ heq hcomm
    have hval : (c₁ : G) = (c₂ : G) := by
      rw [← mul_one (c₁ : G), ← hone, mul_inv_cancel_left]
    exact Subtype.ext hval
  -- Recast the two column lengths as real sums of `|·|²`.
  have hfr_total : ∑ ψ : Irr G, Complex.normSq (ψ g)
      = (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℝ) := by
    have hc : ((∑ ψ : Irr G, Complex.normSq (ψ g) : ℝ) : ℂ)
        = (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
      rw [Complex.ofReal_sum, ← htotal]
      exact Finset.sum_congr rfl fun ψ _ => (Complex.mul_conj (ψ g)).symm
    exact_mod_cast hc
  have hfr_filter : ∑ χ ∈ Finset.univ.filter (fun χ : Irr G => H ≤ χ.ker),
      Complex.normSq (χ g)
      = (Nat.card (Subgroup.centralizer ({(g : G ⧸ H)} : Set (G ⧸ H))) : ℝ) := by
    have hc : ((∑ χ ∈ Finset.univ.filter (fun χ : Irr G => H ≤ χ.ker),
          Complex.normSq (χ g) : ℝ) : ℂ)
        = (Nat.card (Subgroup.centralizer ({(g : G ⧸ H)} : Set (G ⧸ H))) : ℂ) := by
      rw [Complex.ofReal_sum, ← hquotfilter]
      exact Finset.sum_congr rfl fun χ _ => (Complex.mul_conj (χ g)).symm
    exact_mod_cast hc
  -- The sub-column is at most the full column, and the reverse inequality holds too.
  have hsub_le : ∑ χ ∈ Finset.univ.filter (fun χ : Irr G => H ≤ χ.ker),
      Complex.normSq (χ g) ≤ ∑ ψ : Irr G, Complex.normSq (ψ g) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => Complex.normSq_nonneg _)
  have hle2 : ∑ ψ : Irr G, Complex.normSq (ψ g)
      ≤ ∑ χ ∈ Finset.univ.filter (fun χ : Irr G => H ≤ χ.ker), Complex.normSq (χ g) := by
    rw [hfr_total, hfr_filter]
    exact_mod_cast hcard_le
  have heqsum := le_antisymm hle2 hsub_le
  -- Hence the complementary squared terms all vanish.
  have hsdiff : ∀ χ' ∈ Finset.univ \ Finset.univ.filter (fun χ : Irr G => H ≤ χ.ker),
      Complex.normSq (χ' g) = 0 := by
    have hs := Finset.sum_sdiff (f := fun χ : Irr G => Complex.normSq (χ g))
      (Finset.filter_subset (fun χ : Irr G => H ≤ χ.ker) Finset.univ)
    rw [heqsum] at hs
    have hz : ∑ χ ∈ Finset.univ \ Finset.univ.filter (fun χ : Irr G => H ≤ χ.ker),
        Complex.normSq (χ g) = 0 := by
      have h3 := eq_sub_of_add_eq hs
      rwa [sub_self] at h3
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).mp hz
  have hmemsdiff : χ ∈ Finset.univ \ Finset.univ.filter (fun χ' : Irr G => H ≤ χ'.ker) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ χ, fun hmem => hker (Finset.mem_filter.mp hmem).2⟩
  exact Complex.normSq_eq_zero.mp (hsdiff χ hmemsdiff)

end

section

/-! ### (1.4) sub-lemmas: `vchar_isometry_base3` and `vchar_isometry_base4` -/

section Base

variable {G : Type u} [Group G] [Fintype G]

/-- Peterfalvi (1.4), first section-local lemma; MathComp/Coq: `vchar_isometry_base3`
(`PFsection1.v`).  Two norm-`2` virtual characters vanishing at `1` with inner product `1`
are `ε`-scaled differences sharing a common top constituent. -/
theorem vchar_isometry_base3 {f f' : ClassFunction G}
    (hf : f.IsVirtualChar) (hf1 : f 1 = 0) (hnf : ⟪f, f⟫_[G] = 2)
    (hf' : f'.IsVirtualChar) (hf'1 : f' 1 = 0) (hnf' : ⟪f', f'⟫_[G] = 2)
    (hff' : ⟪f, f'⟫_[G] = 1) :
    ∃ (χi χj χk : Irr G) (ε : ℤˣ),
      f = ((ε : ℤ) : ℂ) • ((χj : ClassFunction G) - (χi : ClassFunction G)) ∧
      f' = ((ε : ℤ) : ℂ) • ((χj : ClassFunction G) - (χk : ClassFunction G)) ∧
      χi ≠ χj ∧ χi ≠ χk ∧ χj ≠ χk := by
  classical
  have hone : (((1 : ℤˣ) : ℤ) : ℂ) = 1 := by rw [Units.val_one, Int.cast_one]
  have hmone : (((-1 : ℤˣ) : ℤ) : ℂ) = -1 := by
    rw [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
  obtain ⟨a, b, hab, hf_eq⟩ := hf.exists_sub_of_cfInner_self_eq_two hnf hf1
  obtain ⟨c, d, hcd, hf'_eq⟩ := hf'.exists_sub_of_cfInner_self_eq_two hnf' hf'1
  rw [hf_eq, hf'_eq, ClassFunction.cfInner_sub_left, ClassFunction.cfInner_sub_right,
    ClassFunction.cfInner_sub_right] at hff'
  simp only [Irr.cfInner_eq] at hff'
  rcases eq_or_ne a c with hac | hac
  · subst hac
    rcases eq_or_ne b d with hbd | hbd
    · exfalso
      rw [if_pos rfl, if_neg hcd, if_neg (fun h : b = a => hab h.symm), if_pos hbd] at hff'
      norm_num at hff'
    · refine ⟨b, a, d, 1, ?_, ?_, Ne.symm hab, hbd, hcd⟩
      · rw [hf_eq, hone, one_smul]
      · rw [hf'_eq, hone, one_smul]
  · rcases eq_or_ne b d with hbd | hbd
    · subst hbd
      refine ⟨a, b, c, -1, ?_, ?_, hab, hac, Ne.symm hcd⟩
      · rw [hf_eq, hmone, neg_one_smul, neg_sub]
      · rw [hf'_eq, hmone, neg_one_smul, neg_sub]
    · exfalso
      rw [if_neg hac, if_neg hbd] at hff'
      split_ifs at hff' <;> norm_num at hff'

/-- Peterfalvi (1.4), second section-local lemma; MathComp/Coq: `vchar_isometry_base4`
(`PFsection1.v`).  Convention: the Coq `(-1)^+eps` with `eps : bool` maps `eps = false`
to `ε = 1` (concluding `m == i`) and `eps = true` to `ε = -1` (concluding `n == i`). -/
theorem vchar_isometry_base4 {ε : ℤˣ} {χi χj χk χn χm : Irr G} (hjk : χj ≠ χk)
    (h1 : ⟪(χn : ClassFunction G) - (χm : ClassFunction G),
        (χj : ClassFunction G) - (χi : ClassFunction G)⟫_[G] = ((ε : ℤ) : ℂ))
    (h2 : ⟪(χn : ClassFunction G) - (χm : ClassFunction G),
        (χk : ClassFunction G) - (χi : ClassFunction G)⟫_[G] = ((ε : ℤ) : ℂ)) :
    (ε = 1 ∧ χm = χi) ∨ (ε = -1 ∧ χn = χi) := by
  classical
  rw [ClassFunction.cfInner_sub_left, ClassFunction.cfInner_sub_right,
    ClassFunction.cfInner_sub_right] at h1 h2
  simp only [Irr.cfInner_eq] at h1 h2
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp only [Units.val_one, Int.cast_one] at h1 h2
    refine Or.inl ⟨rfl, ?_⟩
    by_contra hmi
    rw [if_neg hmi] at h1 h2
    have hnj : χn = χj := by
      by_contra hnj
      rw [if_neg hnj] at h1
      split_ifs at h1 <;> norm_num at h1
    have hnk : χn = χk := by
      by_contra hnk
      rw [if_neg hnk] at h2
      split_ifs at h2 <;> norm_num at h2
    exact hjk (hnj ▸ hnk)
  · simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] at h1 h2
    refine Or.inr ⟨rfl, ?_⟩
    by_contra hni
    rw [if_neg hni] at h1 h2
    have hmj : χm = χj := by
      by_contra hmj
      rw [if_neg hmj] at h1
      split_ifs at h1 <;> norm_num at h1
    have hmk : χm = χk := by
      by_contra hmk
      rw [if_neg hmk] at h2
      split_ifs at h2 <;> norm_num at h2
    exact hjk (hmj ▸ hmk)

end Base

/-! ### (1.3): restriction versus the complement -/

section Restrict

variable {G : Type u} [Group G] [Fintype G] {H : Subgroup G} [Fintype H]

/-- Peterfalvi (1.3)(a); MathComp/Coq: `equiv_restrict_compl` (`PFsection1.v`).

Reformulation note: the Coq quantifies over an `m.-tuple` basis of `'CF(H, A)`; here the
basis is an arbitrary `Basis ι ℂ` of the `supportedOn` subspace, and irreducibles are
indexed by `Irr ↥H` itself rather than by ordinals (per the survey's porting note;
consumption sites PFsection3.v:1484, PFsection4.v:360 pass a basis and use the two clauses
of (b), shape-checked). -/
theorem equiv_restrict_compl {A : Set ↥H} (hA : ∀ (h a : ↥H), a ∈ A → h * a * h⁻¹ ∈ A)
    {ι : Type*} [Finite ι] (Φ : Basis ι ℂ ↥(ClassFunction.supportedOn ↥H A))
    (μ : ClassFunction G) (d : Irr ↥H → ℂ) :
    (∀ a : ↥H, a ∈ A → μ ↑a = ∑ χ : Irr ↥H, d χ * χ a) ↔
      (∀ j : ι, ∑ χ : Irr ↥H, ⟪((Φ j : ClassFunction ↥H)), (χ : ClassFunction ↥H)⟫_[↥H]
          * starRingEnd ℂ (d χ)
        = ⟪ClassFunction.ind H (Φ j : ClassFunction ↥H), μ⟫_[G]) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  -- membership in `A` is stable both ways under conjugation
  have hAiff : ∀ (h a : ↥H), (h * a * h⁻¹ ∈ A ↔ a ∈ A) := by
    intro h a
    refine ⟨fun hmem => ?_, hA h a⟩
    have := hA h⁻¹ (h * a * h⁻¹) hmem
    rwa [show h⁻¹ * (h * a * h⁻¹) * h⁻¹⁻¹ = a by group] at this
  set D : ClassFunction ↥H :=
    ClassFunction.res H μ - ∑ χ : Irr ↥H, d χ • (χ : ClassFunction ↥H) with hDdef
  -- evaluation of `D` on `↥H`
  have hDa : ∀ a : ↥H, D a = μ (a : G) - ∑ χ : Irr ↥H, d χ * χ a := by
    intro a
    rw [hDdef]
    change ClassFunction.res H μ a - (∑ χ : Irr ↥H, d χ • (χ : ClassFunction ↥H)) a
      = μ (a : G) - ∑ χ : Irr ↥H, d χ * χ a
    rw [ClassFunction.res_apply, ClassFunction.sum_apply]
    refine congrArg _ (Finset.sum_congr rfl fun χ _ => ?_)
    rw [ClassFunction.smul_apply, smul_eq_mul, Irr.coe_apply]
  -- the left-hand side is equivalent to `D` being supported off `A`
  have hstep1 : (∀ a : ↥H, a ∈ A → μ ↑a = ∑ χ : Irr ↥H, d χ * χ a)
      ↔ D ∈ ClassFunction.supportedOn ↥H (Aᶜ : Set ↥H) := by
    rw [ClassFunction.mem_supportedOn]
    constructor
    · intro h g hg
      rw [hDa g, h g (by simpa using hg), sub_self]
    · intro h a ha
      have hDa0 : D a = 0 := h a (by simpa using ha)
      rw [hDa a] at hDa0
      exact sub_eq_zero.mp hDa0
  -- each clause of the right-hand side is equivalent to an orthogonality of `D`
  have hj : ∀ j : ι,
      (∑ χ : Irr ↥H, ⟪((Φ j : ClassFunction ↥H)), (χ : ClassFunction ↥H)⟫_[↥H]
            * starRingEnd ℂ (d χ)
          = ⟪ClassFunction.ind H (Φ j : ClassFunction ↥H), μ⟫_[G])
        ↔ ⟪(Φ j : ClassFunction ↥H), D⟫_[↥H] = 0 := by
    intro j
    have hexp : ⟪(Φ j : ClassFunction ↥H), D⟫_[↥H]
        = ⟪ClassFunction.ind H (Φ j : ClassFunction ↥H), μ⟫_[G]
          - ∑ χ : Irr ↥H, ⟪((Φ j : ClassFunction ↥H)), (χ : ClassFunction ↥H)⟫_[↥H]
              * starRingEnd ℂ (d χ) := by
      rw [hDdef, ClassFunction.cfInner_sub_right, ClassFunction.cfInner_sum_right,
        ← ClassFunction.cfInner_ind_eq_cfInner_res]
      refine congrArg _ (Finset.sum_congr rfl fun χ _ => ?_)
      rw [ClassFunction.cfInner_smul_right, mul_comm]
    rw [hexp, sub_eq_zero]
    exact eq_comm
  -- the key disjoint-support argument
  have hkey : D ∈ ClassFunction.supportedOn ↥H (Aᶜ : Set ↥H)
      ↔ ∀ j : ι, ⟪(Φ j : ClassFunction ↥H), D⟫_[↥H] = 0 := by
    constructor
    · intro hDsupp j
      exact ClassFunction.cfInner_eq_zero_of_supportedOn_disjoint (SetLike.coe_mem (Φ j)) hDsupp
        disjoint_compl_right
    · intro hz
      -- the truncation of `D` to `A`
      have hfconj : ∀ g b : ↥H,
          (if (b * g * b⁻¹) ∈ A then D (b * g * b⁻¹) else 0) = (if g ∈ A then D g else 0) := by
        intro g b
        by_cases hg : g ∈ A
        · rw [if_pos ((hAiff b g).mpr hg), if_pos hg, D.conj_apply]
        · rw [if_neg (fun hc => hg ((hAiff b g).mp hc)), if_neg hg]
      set f : ClassFunction ↥H := ⟨fun h => if h ∈ A then D h else 0, hfconj⟩ with hfdef
      have hfapp : ∀ h : ↥H, f h = if h ∈ A then D h else 0 := fun _ => rfl
      have hfsupp : f ∈ ClassFunction.supportedOn ↥H A := by
        rw [ClassFunction.mem_supportedOn]
        intro g hg
        rw [hfapp g, if_neg hg]
      have hg'supp : (D - f) ∈ ClassFunction.supportedOn ↥H (Aᶜ : Set ↥H) := by
        rw [ClassFunction.mem_supportedOn]
        intro g hg
        have hgA : g ∈ A := by simpa using hg
        change D g - f g = 0
        rw [hfapp g, if_pos hgA, sub_self]
      -- `f` lies in the span of the basis, so `⟪f, D⟫ = 0`
      have hfrepr : (f : ClassFunction ↥H)
          = ∑ i : ι, (Φ.repr ⟨f, hfsupp⟩ i) • (Φ i : ClassFunction ↥H) := by
        have h := congrArg (fun x : ↥(ClassFunction.supportedOn ↥H A) => (x : ClassFunction ↥H))
          (Φ.sum_repr ⟨f, hfsupp⟩)
        simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul] at h
        exact h.symm
      have hfD : ⟪f, D⟫_[↥H] = 0 := by
        rw [hfrepr, ClassFunction.cfInner_sum_left]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [ClassFunction.cfInner_smul_left, hz i, mul_zero]
      -- but `⟪f, D⟫ = ⟪f, f⟫`, so `f = 0`
      have hff : ⟪f, f⟫_[↥H] = 0 := by
        have hfg0 : ⟪f, D - f⟫_[↥H] = 0 :=
          ClassFunction.cfInner_eq_zero_of_supportedOn_disjoint hfsupp hg'supp disjoint_compl_right
        have hsplit : f + (D - f) = D := by abel
        have hchain : ⟪f, f⟫_[↥H] + ⟪f, D - f⟫_[↥H] = ⟪f, D⟫_[↥H] := by
          rw [← ClassFunction.cfInner_add_right, hsplit]
        rw [hfg0, add_zero, hfD] at hchain
        exact hchain
      have hf0 : f = 0 := ClassFunction.cfInner_self_eq_zero.mp hff
      -- hence `D` vanishes on `A`
      rw [ClassFunction.mem_supportedOn]
      intro g hg
      have hgA : g ∈ A := by simpa using hg
      have hfg : f g = D g := by rw [hfapp g, if_pos hgA]
      rw [← hfg, hf0]
      rfl
  constructor
  · intro hL j
    exact (hj j).mpr (hkey.mp (hstep1.mp hL) j)
  · intro hR
    exact hstep1.mpr (hkey.mpr fun j => (hj j).mp (hR j))

open scoped Classical in
/-- Peterfalvi (1.3)(b); MathComp/Coq: `equiv_restrict_compl_ortho` (`PFsection1.v`).
Both clauses follow from the reverse implication of (1.3)(a). -/
theorem equiv_restrict_compl_ortho {A : Set ↥H}
    (hA : ∀ (h a : ↥H), a ∈ A → h * a * h⁻¹ ∈ A)
    {ι : Type*} [Finite ι] (Φ : Basis ι ℂ ↥(ClassFunction.supportedOn ↥H A))
    (μ : Irr ↥H → ClassFunction G)
    (hortho : ∀ χ ψ : Irr ↥H, ⟪μ χ, μ ψ⟫_[G] = if χ = ψ then 1 else 0)
    (hInd : ∀ j : ι, ClassFunction.ind H (Φ j : ClassFunction ↥H)
        = ∑ χ : Irr ↥H, ⟪((Φ j : ClassFunction ↥H)), (χ : ClassFunction ↥H)⟫_[↥H] • μ χ) :
    (∀ χ : Irr ↥H, ∀ a : ↥H, a ∈ A → μ χ ↑a = χ a) ∧
      (∀ ν : ClassFunction G, (∀ χ : Irr ↥H, ⟪ν, μ χ⟫_[G] = 0) →
        ∀ a : ↥H, a ∈ A → ν ↑a = 0) := by
  classical
  refine ⟨fun χ₀ => ?_, fun ν hν => ?_⟩
  · -- first clause: apply (1.3)(a) with `μ := μ χ₀`, `d := indicator of χ₀`
    have hRHS : ∀ j : ι, ∑ χ : Irr ↥H,
        ⟪((Φ j : ClassFunction ↥H)), (χ : ClassFunction ↥H)⟫_[↥H]
          * starRingEnd ℂ (if χ = χ₀ then (1 : ℂ) else 0)
        = ⟪ClassFunction.ind H (Φ j : ClassFunction ↥H), μ χ₀⟫_[G] := by
      intro j
      have hlhs : ∑ χ : Irr ↥H, ⟪((Φ j : ClassFunction ↥H)), (χ : ClassFunction ↥H)⟫_[↥H]
            * starRingEnd ℂ (if χ = χ₀ then (1 : ℂ) else 0)
          = ⟪((Φ j : ClassFunction ↥H)), (χ₀ : ClassFunction ↥H)⟫_[↥H] := by
        have hterm : ∀ χ : Irr ↥H,
            ⟪((Φ j : ClassFunction ↥H)), (χ : ClassFunction ↥H)⟫_[↥H]
              * starRingEnd ℂ (if χ = χ₀ then (1 : ℂ) else 0)
            = if χ = χ₀ then ⟪((Φ j : ClassFunction ↥H)), (χ₀ : ClassFunction ↥H)⟫_[↥H]
              else 0 := by
          intro χ
          by_cases h : χ = χ₀
          · rw [if_pos h, if_pos h, map_one, mul_one, h]
          · rw [if_neg h, if_neg h, map_zero, mul_zero]
        rw [Finset.sum_congr rfl fun χ _ => hterm χ, Finset.sum_ite_eq' Finset.univ χ₀ _,
          if_pos (Finset.mem_univ χ₀)]
      have hrhs : ⟪ClassFunction.ind H (Φ j : ClassFunction ↥H), μ χ₀⟫_[G]
          = ⟪((Φ j : ClassFunction ↥H)), (χ₀ : ClassFunction ↥H)⟫_[↥H] := by
        rw [hInd j, ClassFunction.cfInner_sum_left]
        have hterm : ∀ χ : Irr ↥H,
            ⟪⟪((Φ j : ClassFunction ↥H)), (χ : ClassFunction ↥H)⟫_[↥H] • μ χ, μ χ₀⟫_[G]
            = if χ = χ₀ then ⟪((Φ j : ClassFunction ↥H)), (χ₀ : ClassFunction ↥H)⟫_[↥H]
              else 0 := by
          intro χ
          rw [ClassFunction.cfInner_smul_left, hortho χ χ₀]
          by_cases h : χ = χ₀
          · rw [if_pos h, if_pos h, mul_one, h]
          · rw [if_neg h, if_neg h, mul_zero]
        rw [Finset.sum_congr rfl fun χ _ => hterm χ, Finset.sum_ite_eq' Finset.univ χ₀ _,
          if_pos (Finset.mem_univ χ₀)]
      rw [hlhs, hrhs]
    have hL := (equiv_restrict_compl hA Φ (μ χ₀) (fun χ => if χ = χ₀ then 1 else 0)).mpr hRHS
    intro a ha
    rw [hL a ha]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · -- second clause: apply (1.3)(a) with `μ := ν`, `d := 0`
    have hRHS : ∀ j : ι, ∑ χ : Irr ↥H,
        ⟪((Φ j : ClassFunction ↥H)), (χ : ClassFunction ↥H)⟫_[↥H]
          * starRingEnd ℂ ((fun _ => (0 : ℂ)) χ)
        = ⟪ClassFunction.ind H (Φ j : ClassFunction ↥H), ν⟫_[G] := by
      intro j
      have hindzero : ⟪ClassFunction.ind H (Φ j : ClassFunction ↥H), ν⟫_[G] = 0 := by
        rw [hInd j, ClassFunction.cfInner_sum_left]
        refine Finset.sum_eq_zero fun χ _ => ?_
        rw [ClassFunction.cfInner_smul_left, ClassFunction.cfInner_conj_symm ν (μ χ), hν χ,
          map_zero, mul_zero]
      rw [hindzero]
      refine Finset.sum_eq_zero fun χ _ => ?_
      simp
    have hL := (equiv_restrict_compl hA Φ ν (fun _ => (0 : ℂ))).mpr hRHS
    intro a ha
    rw [hL a ha]
    simp

end Restrict

/-! ### (1.4): the base of a coherent isometry -/

section Main

variable {H : Type u} [Group H] [Fintype H] {G : Type v} [Group G] [Fintype G]

open scoped Classical in
/-- Peterfalvi (1.4); MathComp/Coq: `vchar_isometry_base` (`PFsection1.v`).

Porting notes: the Coq `m.-tuple` of free members of `irr H` becomes an injective
`Fin m`-family of `Irr H`; `'Z[irr G, G^#]`-membership is spelled `IsVirtualChar ∧ φ 1 = 0`
(MathComp `zcharD1E`); the equal-degrees hypothesis `hdeg` is carried for statement fidelity
with the Coq even though the proof does not use it (the Coq proof does not either). -/
theorem vchar_isometry_base {m : ℕ} [NeZero m] (hm : 1 < m) (Chi : Fin m → Irr H)
    (hChi : Function.Injective Chi) {L : Set H}
    (hdeg : ∀ i, Chi i 1 = Chi 0 1)
    (hL : ∀ i, ((Chi i : ClassFunction H) - (Chi 0 : ClassFunction H))
        ∈ ClassFunction.supportedOn H L)
    (τ : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hiso : ∀ φ ψ : ClassFunction H,
      φ ∈ Z[Finset.univ.image fun i => ((Chi i : ClassFunction H)), L] →
      ψ ∈ Z[Finset.univ.image fun i => ((Chi i : ClassFunction H)), L] →
      ⟪τ φ, τ ψ⟫_[G] = ⟪φ, ψ⟫_[H])
    (hto : ∀ φ : ClassFunction H,
      φ ∈ Z[Finset.univ.image fun i => ((Chi i : ClassFunction H)), L] →
      (τ φ).IsVirtualChar ∧ τ φ 1 = 0) :
    ∃ μ : Fin m → Irr G, Function.Injective μ ∧ ∃ ε : ℤˣ, ∀ i : Fin m,
      τ ((Chi i : ClassFunction H) - (Chi 0 : ClassFunction H))
        = ((ε : ℤ) : ℂ) • ((μ i : ClassFunction G) - (μ 0 : ClassFunction G)) := by
  classical
  set S : Finset (ClassFunction H) := Finset.univ.image fun i => (Chi i : ClassFunction H)
    with hSdef
  have hSmem : ∀ i : Fin m, (Chi i : ClassFunction H) ∈ (↑S : Set (ClassFunction H)) := by
    intro i
    rw [hSdef, Finset.mem_coe]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  -- the differences all lie in the virtual-character lattice
  have hmem : ∀ i j : Fin m,
      ((Chi i : ClassFunction H) - (Chi j : ClassFunction H)) ∈ Z[S, L] := by
    intro i j
    have hspan : ((Chi i : ClassFunction H) - (Chi j : ClassFunction H))
        ∈ Submodule.span ℤ (↑S : Set (ClassFunction H)) :=
      Submodule.sub_mem _ (Submodule.subset_span (hSmem i)) (Submodule.subset_span (hSmem j))
    have hsupp : ((Chi i : ClassFunction H) - (Chi j : ClassFunction H))
        ∈ ClassFunction.supportedOn H L := by
      rw [show (Chi i : ClassFunction H) - (Chi j : ClassFunction H)
          = ((Chi i : ClassFunction H) - (Chi 0 : ClassFunction H))
            - ((Chi j : ClassFunction H) - (Chi 0 : ClassFunction H)) from by abel]
      exact Submodule.sub_mem _ (hL i) (hL j)
    rw [ClassFunction.VirtualChar, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup,
      Submodule.mem_toAddSubgroup]
    exact ⟨hspan, hsupp⟩
  -- orthonormality of the Chi
  have hdot : ∀ i j : Fin m,
      ⟪(Chi i : ClassFunction H), (Chi j : ClassFunction H)⟫_[H] = if i = j then 1 else 0 := by
    intro i j
    rw [Irr.cfInner_eq]
    simp only [hChi.eq_iff]
  -- the images of the differences under τ have norm 2 ...
  have htau2 : ∀ i j : Fin m, i ≠ j →
      ⟪τ ((Chi i : ClassFunction H) - (Chi j : ClassFunction H)),
        τ ((Chi i : ClassFunction H) - (Chi j : ClassFunction H))⟫_[G] = 2 := by
    intro i j hij
    rw [hiso _ _ (hmem i j) (hmem i j), ClassFunction.cfInner_sub_left,
      ClassFunction.cfInner_sub_right, ClassFunction.cfInner_sub_right, hdot, hdot, hdot, hdot,
      if_pos rfl, if_pos rfl, if_neg hij, if_neg (Ne.symm hij)]
    norm_num
  -- ... and the correct cross inner products
  have htau1 : ∀ i j : Fin m, j ≠ 0 → j ≠ i → i ≠ 0 →
      ⟪τ ((Chi i : ClassFunction H) - (Chi 0 : ClassFunction H)),
        τ ((Chi j : ClassFunction H) - (Chi 0 : ClassFunction H))⟫_[G] = 1 := by
    intro i j hj0 hji hi0
    rw [hiso _ _ (hmem i 0) (hmem j 0), ClassFunction.cfInner_sub_left,
      ClassFunction.cfInner_sub_right, ClassFunction.cfInner_sub_right, hdot, hdot, hdot, hdot,
      if_neg (Ne.symm hji), if_neg hi0, if_neg (Ne.symm hj0), if_pos rfl]
    norm_num
  -- basic index facts (valid for any `1 < m`)
  have hv0 : (0 : Fin m).val = 0 := by simp
  have hv1 : (1 : Fin m).val = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have h10 : (1 : Fin m) ≠ 0 := fun h => by
    have := congrArg Fin.val h; rw [hv1, hv0] at this; omega
  by_cases hm2 : m = 2
  · -- base case m = 2
    subst hm2
    obtain ⟨χa, χb, hχab, hτ⟩ :=
      (hto _ (hmem 1 0)).1.exists_sub_of_cfInner_self_eq_two (htau2 1 0 h10)
        (hto _ (hmem 1 0)).2
    refine ⟨fun i => if i = 0 then χb else χa, ?_, 1, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i
      fin_cases i
      · simp
      · simpa using hτ
  · -- inductive case 2 < m
    have hm3 : 2 < m := by omega
    set i2 : Fin m := ⟨2, hm3⟩ with hi2def
    have hi2val : i2.val = 2 := rfl
    have hi20 : i2 ≠ 0 := fun h => by
      have := congrArg Fin.val h; rw [hi2val, hv0] at this; omega
    have hi21 : i2 ≠ 1 := fun h => by
      have := congrArg Fin.val h; rw [hi2val, hv1] at this; omega
    obtain ⟨k1, k0, k2, ε0, hf10, hfi20, hk1k0, hk1k2, hk0k2⟩ :=
      vchar_isometry_base3
        (hto _ (hmem 1 0)).1 (hto _ (hmem 1 0)).2 (htau2 1 0 h10)
        (hto _ (hmem i2 0)).1 (hto _ (hmem i2 0)).2 (htau2 i2 0 hi20)
        (htau1 1 i2 hi20 hi21 h10)
    set d : ℂ := ((ε0 : ℤ) : ℂ) with hddef
    have hdconj : starRingEnd ℂ d = d := by rw [hddef]; exact map_intCast (starRingEnd ℂ) _
    have hd2 : d * d = 1 := by
      rcases Int.units_eq_one_or ε0 with h | h <;> rw [hddef, h] <;> simp
    have hnegd : (((-ε0 : ℤˣ) : ℤ) : ℂ) = -d := by
      rw [hddef, Units.val_neg, Int.cast_neg]
    have hone : (((1 : ℤˣ) : ℤ) : ℂ) = 1 := by rw [Units.val_one, Int.cast_one]
    have hmone : (((-1 : ℤˣ) : ℤ) : ℂ) = -1 := by
      rw [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    -- each difference is `d`-scaled with common top constituent `k0`
    have muP : ∀ i : Fin m, ∃ k : Irr G, (i = 0 → k = k0) ∧
        τ ((Chi i : ClassFunction H) - (Chi 0 : ClassFunction H))
          = d • ((k0 : ClassFunction G) - (k : ClassFunction G)) := by
      intro i
      by_cases hi0 : i = 0
      · refine ⟨k0, fun _ => rfl, ?_⟩
        rw [hi0, sub_self, map_zero, sub_self, smul_zero]
      · by_cases hi1 : i = 1
        · exact ⟨k1, fun h => absurd h hi0, by rw [hi1]; exact hf10⟩
        · by_cases hi2 : i = i2
          · exact ⟨k2, fun h => absurd h hi0, by rw [hi2]; exact hfi20⟩
          · obtain ⟨a, b, hab, hiab⟩ :=
              (hto _ (hmem i 0)).1.exists_sub_of_cfInner_self_eq_two (htau2 i 0 hi0)
                (hto _ (hmem i 0)).2
            have hc1 := htau1 i 1 h10 (Ne.symm hi1) hi0
            have hc2 := htau1 i i2 hi20 (Ne.symm hi2) hi0
            have h1 : ⟪(a : ClassFunction G) - (b : ClassFunction G),
                (k1 : ClassFunction G) - (k0 : ClassFunction G)⟫_[G]
                = (((-ε0 : ℤˣ) : ℤ) : ℂ) := by
              rw [hiab, hf10, ClassFunction.cfInner_smul_right, hdconj] at hc1
              have hX : ⟪(a : ClassFunction G) - (b : ClassFunction G),
                  (k0 : ClassFunction G) - (k1 : ClassFunction G)⟫_[G] = d := by
                have hmul : d * (d * ⟪(a : ClassFunction G) - (b : ClassFunction G),
                    (k0 : ClassFunction G) - (k1 : ClassFunction G)⟫_[G]) = d * 1 := by rw [hc1]
                rwa [← mul_assoc, hd2, one_mul, mul_one] at hmul
              have hsum0 : ⟪(a : ClassFunction G) - (b : ClassFunction G),
                  (k1 : ClassFunction G) - (k0 : ClassFunction G)⟫_[G]
                  + ⟪(a : ClassFunction G) - (b : ClassFunction G),
                    (k0 : ClassFunction G) - (k1 : ClassFunction G)⟫_[G] = 0 := by
                rw [← ClassFunction.cfInner_add_right,
                  show ((k1 : ClassFunction G) - (k0 : ClassFunction G))
                      + ((k0 : ClassFunction G) - (k1 : ClassFunction G)) = 0 from by abel,
                  ClassFunction.cfInner_zero_right]
              rw [hX] at hsum0
              rw [hnegd]
              exact eq_neg_of_add_eq_zero_left hsum0
            have h2 : ⟪(a : ClassFunction G) - (b : ClassFunction G),
                (k2 : ClassFunction G) - (k0 : ClassFunction G)⟫_[G]
                = (((-ε0 : ℤˣ) : ℤ) : ℂ) := by
              rw [hiab, hfi20, ClassFunction.cfInner_smul_right, hdconj] at hc2
              have hX : ⟪(a : ClassFunction G) - (b : ClassFunction G),
                  (k0 : ClassFunction G) - (k2 : ClassFunction G)⟫_[G] = d := by
                have hmul : d * (d * ⟪(a : ClassFunction G) - (b : ClassFunction G),
                    (k0 : ClassFunction G) - (k2 : ClassFunction G)⟫_[G]) = d * 1 := by rw [hc2]
                rwa [← mul_assoc, hd2, one_mul, mul_one] at hmul
              have hsum0 : ⟪(a : ClassFunction G) - (b : ClassFunction G),
                  (k2 : ClassFunction G) - (k0 : ClassFunction G)⟫_[G]
                  + ⟪(a : ClassFunction G) - (b : ClassFunction G),
                    (k0 : ClassFunction G) - (k2 : ClassFunction G)⟫_[G] = 0 := by
                rw [← ClassFunction.cfInner_add_right,
                  show ((k2 : ClassFunction G) - (k0 : ClassFunction G))
                      + ((k0 : ClassFunction G) - (k2 : ClassFunction G)) = 0 from by abel,
                  ClassFunction.cfInner_zero_right]
              rw [hX] at hsum0
              rw [hnegd]
              exact eq_neg_of_add_eq_zero_left hsum0
            rcases vchar_isometry_base4 hk1k2 h1 h2 with ⟨hε, hbk0⟩ | ⟨hε, hak0⟩
            · have hd_eq : d = -1 := by
                rw [hddef, (neg_eq_iff_eq_neg.mp hε : ε0 = -1)]; exact hmone
              refine ⟨a, fun h => absurd h hi0, ?_⟩
              rw [hiab, hbk0, hd_eq, neg_one_smul, neg_sub]
            · have hε0 : ε0 = 1 := by
                have h := neg_eq_iff_eq_neg.mp hε; rwa [neg_neg] at h
              have hd_eq : d = 1 := by rw [hddef, hε0]; exact hone
              refine ⟨b, fun h => absurd h hi0, ?_⟩
              rw [hiab, hak0, hd_eq, one_smul]
    choose μ hμk0 hμτ using muP
    refine ⟨μ, ?_, -ε0, ?_⟩
    · intro i i' hii'
      by_contra hne
      have heq : τ ((Chi i : ClassFunction H) - (Chi 0 : ClassFunction H))
          = τ ((Chi i' : ClassFunction H) - (Chi 0 : ClassFunction H)) := by
        rw [hμτ i, hμτ i', hii']
      have hzero : τ ((Chi i : ClassFunction H) - (Chi i' : ClassFunction H)) = 0 := by
        rw [show (Chi i : ClassFunction H) - (Chi i' : ClassFunction H)
            = ((Chi i : ClassFunction H) - (Chi 0 : ClassFunction H))
              - ((Chi i' : ClassFunction H) - (Chi 0 : ClassFunction H)) from by abel,
          map_sub, heq, sub_self]
      have hnorm := htau2 i i' hne
      rw [hzero, ClassFunction.cfInner_zero_left] at hnorm
      norm_num at hnorm
    · intro i
      have hμ0 : μ 0 = k0 := hμk0 0 rfl
      rw [hμτ i, hμ0, hnegd, neg_smul, ← smul_neg, neg_sub]

end Main

end

section

variable {G : Type u} [Group G]

/-! ### Kernel elements act trivially -/

/-- If `k` lies in the kernel of `χ` (i.e. acts as the identity on a witnessing simple module),
then `χ (x * k) = χ x` for every `x`. MathComp: the multiplicativity of `cfker` membership
underlying `cfkerEchar`. -/
theorem Irr.apply_mul_mem_ker [Fintype G] (χ : Irr G) {x k : G} (hk : k ∈ χ.ker) :
    χ (x * k) = χ x := by
  set N := χ.exists_simple'.choose with hNdef
  have hval : χ.toClassFunction = MonoidAlgebra.moduleCharacter G N :=
    χ.exists_simple'.choose_spec.2
  have happ : ∀ y : G, χ y = trace ℂ N (MonoidAlgebra.actionEnd N y) := by
    intro y
    have := congrArg (fun φ : ClassFunction G => φ y) hval
    simpa [MonoidAlgebra.moduleCharacter_apply] using this
  have hkeriff : k ∈ χ.ker ↔ Representation.ofModule' (k := ℂ) (G := G) N k = 1 := Iff.rfl
  have hker := hkeriff.mp hk
  rw [MonoidAlgebra.ofModule'_eq_actionEnd] at hker
  rw [happ (x * k), happ x, MonoidAlgebra.actionEnd_mul, hker, ← Module.End.mul_eq_comp, mul_one]

/-! ### A nonzero class function has an irreducible constituent -/

variable [Fintype G]

/-- A nonzero class function has an irreducible constituent: some inner product
`⟪φ, ξ⟫` is nonzero, else the basis expansion would make `φ = 0`. MathComp: `neq0_has_constt`. -/
theorem exists_constt_of_ne_zero {φ : ClassFunction G} (h : φ ≠ 0) :
    ∃ ξ : Irr G, ⟪φ, (ξ : ClassFunction G)⟫_[G] ≠ 0 := by
  classical
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  apply h
  rw [ClassFunction.eq_sum_cfInner_smul φ]
  exact Finset.sum_eq_zero fun ξ _ => by rw [hcon ξ, zero_smul]

/-! ### The degree of a constituent is bounded by the degree of the character -/

/-- If `χ` is an irreducible constituent of a character `Ψ` (`⟪Ψ, χ⟫ ≠ 0`), then
`χ 1 ≤ Ψ 1`: expand `Ψ = ∑ ξ, cₓ ξ • ξ` with natural coefficients, so `Ψ 1 = ∑ ξ, cₓ ξ · ξ 1`
is a sum of nonnegative integers dominating the single term `c_χ · χ 1 ≥ χ 1`.
MathComp: `char1_ge_constt`. -/
theorem char1_ge_constt {Ψ : ClassFunction G} (hΨ : Ψ.IsChar) {χ : Irr G}
    (h : ⟪Ψ, (χ : ClassFunction G)⟫_[G] ≠ 0) : (χ 1).re ≤ (Ψ 1).re := by
  classical
  obtain ⟨c, hc⟩ := hΨ
  choose d _hd0 hd using fun ξ : Irr G => ξ.exists_degree
  have hcoef : ⟪Ψ, (χ : ClassFunction G)⟫_[G] = (c χ : ℂ) := by
    rw [hc, ClassFunction.cfInner_sum_left,
      Finset.sum_congr rfl (fun ξ _ => by
        rw [ClassFunction.cfInner_smul_left, Irr.cfInner_eq, mul_ite, mul_one, mul_zero]),
      Finset.sum_ite_eq' Finset.univ χ (fun ξ => (c ξ : ℂ)), if_pos (Finset.mem_univ χ)]
  have hcχ : 1 ≤ c χ := by
    rw [hcoef] at h
    exact Nat.one_le_iff_ne_zero.mpr fun h0 => h (by rw [h0]; simp)
  have hΨ1 : Ψ 1 = ((∑ ξ : Irr G, c ξ * d ξ : ℕ) : ℂ) := by
    conv_lhs => rw [hc]
    rw [ClassFunction.sum_apply]
    push_cast
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [ClassFunction.smul_apply, smul_eq_mul, Irr.coe_apply, hd ξ]
  have hnat : d χ ≤ ∑ ξ : Irr G, c ξ * d ξ :=
    calc d χ ≤ c χ * d χ := le_mul_of_one_le_left (Nat.zero_le _) hcχ
      _ ≤ ∑ ξ : Irr G, c ξ * d ξ :=
          Finset.single_le_sum (f := fun ξ => c ξ * d ξ) (fun ξ _ => Nat.zero_le _)
            (Finset.mem_univ χ)
  rw [hd χ, Complex.natCast_re, hΨ1, Complex.natCast_re]
  exact_mod_cast hnat

/-! ### An irreducible constituent of an inflated class function is inflated -/

/-- A class function on `K` invariant under right multiplication by a normal subgroup `B`
descends to a class function on `K ⧸ B`. This is the (reducible) descent underlying
MathComp's `cfQuo`. -/
def descend {K : Type u} [Group K] {B : Subgroup K} [B.Normal] (ψ : ClassFunction K)
    (hψ : ∀ b ∈ B, ∀ x : K, ψ (x * b) = ψ x) : ClassFunction (K ⧸ B) where
  toFun q := Quotient.liftOn' q ψ fun a c hac => by
    have hmem : a⁻¹ * c ∈ B := QuotientGroup.leftRel_apply.mp hac
    have h2 := hψ (a⁻¹ * c) hmem a
    rw [mul_inv_cancel_left] at h2
    exact h2.symm
  conj_invariant' g h := by
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective h
    change ψ (a * c * a⁻¹) = ψ c
    exact ψ.conj_apply c a

theorem cfMod_descend {K : Type u} [Group K] {B : Subgroup K} [B.Normal] (ψ : ClassFunction K)
    (hψ : ∀ b ∈ B, ∀ x : K, ψ (x * b) = ψ x) :
    ClassFunction.cfMod B (descend ψ hψ) = ψ := by
  ext x
  rw [ClassFunction.cfMod_apply]
  rfl

/-- **Constituent of an inflated character is inflated.** If an irreducible character `ζ` of `K`
is a constituent of a class function inflated from `K ⧸ B`, then `B ≤ ker ζ`. Proof: expand the
quotient class function in the irreducible basis of `K ⧸ B` and inflate; every summand is a
`mod ξ` (with `B ≤ ker`), so orthonormality forces `ζ` to be one of them. This is the
character-theoretic route to MathComp's `cfker_constt` for the inflated situation, avoiding
character-value norm bounds. -/
theorem le_ker_of_cfMod_constt {K : Type u} [Group K] [Fintype K] {B : Subgroup K} [B.Normal]
    (φ : ClassFunction (K ⧸ B)) {ζ : Irr K}
    (h : ⟪ClassFunction.cfMod B φ, (ζ : ClassFunction K)⟫_[K] ≠ 0) : B ≤ ζ.ker := by
  classical
  haveI : Fintype (K ⧸ B) := Fintype.ofFinite _
  have hexp : ClassFunction.cfMod B φ
      = ∑ ξ : Irr (K ⧸ B), ⟪φ, (ξ : ClassFunction (K ⧸ B))⟫_[K ⧸ B]
          • ((ξ.mod B : Irr K) : ClassFunction K) := by
    conv_lhs => rw [ClassFunction.eq_sum_cfInner_smul φ]
    rw [map_sum]
    exact Finset.sum_congr rfl fun ξ _ => by rw [map_smul, ← Irr.coe_mod]
  rw [hexp, ClassFunction.cfInner_sum_left] at h
  have hex : ∃ ξ : Irr (K ⧸ B), ξ.mod B = ζ := by
    by_contra hcon
    simp only [not_exists] at hcon
    exact h (Finset.sum_eq_zero fun ξ _ => by
      rw [ClassFunction.cfInner_smul_left, Irr.cfInner_eq, if_neg (hcon ξ), mul_zero])
  obtain ⟨ξ, hξ⟩ := hex
  rw [← hξ]
  exact Irr.le_ker_mod B ξ

/-! ### The character-center Schur bound (the one budgeted gap) -/

/-- **Character-center Schur bound, quotient form** (Peterfalvi (1.8) inner step `I1B`).
For an irreducible character `χ` of `K` with `B ≤ ker χ` and `D / B ≤ Z(K / B)`,
```
    χ(1)² ≤ |K : D|.
```
NOT YET PROVED. Its MathComp proof (`irr1_bound i2` composed with `index_quotient_eq`) rests on
the character center `cfcenter` (`χ(1)² ≤ |K : Z(χ)|`), which is not yet ported. This carries the
project's single budgeted gap for (1.8). -/
theorem irr1_bound_charCenter {K : Type u} [Group K] [Fintype K] (B D : Subgroup K) [B.Normal]
    (χ : Irr K) (hBker : B ≤ χ.ker) (hBD : B ≤ D)
    (hZ : D.map (QuotientGroup.mk' B) ≤ Subgroup.center (K ⧸ B)) :
    (χ 1).re ^ 2 ≤ (D.index : ℝ) := by
  -- TODO(m6-task2): irr1_bound (character-center Schur bound) not yet in project
  sorry

/-! ### Peterfalvi (1.8) -/

/-- **Peterfalvi (1.8)** (`irr1_bound_quo`). With `B ◁ C`, `B ≤ ker χ`, `B ≤ D ≤ C` and
`D / B ≤ Z(C / B)`,
```
    χ 1 ≤ |G : C| · √|C : D|.
```
See the module docstring for the `√`/cast discipline and the location of the single budgeted
gap. -/
theorem irr1_bound_quo (B C D : Subgroup G) [B.Normal] (χ : Irr G)
    (_hBC : B ≤ C) (hBker : B ≤ χ.ker) (hBD : B ≤ D)
    (_hDC : D ≤ C)
    (hZ : (D.subgroupOf C).map (QuotientGroup.mk' (B.subgroupOf C))
        ≤ Subgroup.center (↥C ⧸ B.subgroupOf C)) :
    (χ 1).re ≤ (C.index : ℝ) * Real.sqrt (D.relIndex C : ℝ) := by
  classical
  haveI : Fintype ↥C := Fintype.ofFinite _
  obtain ⟨dχ, hdχ0, hdχ⟩ := χ.exists_degree
  -- `Res_C χ` is nonzero (it takes the value `χ 1 ≠ 0` at the identity).
  have hRes1 : ClassFunction.res C (χ : ClassFunction G) 1 = χ 1 := by
    rw [ClassFunction.res_apply, OneMemClass.coe_one, Irr.coe_apply]
  have hResne : ClassFunction.res C (χ : ClassFunction G) ≠ 0 := by
    intro h0
    rw [h0, ClassFunction.zero_apply, hdχ] at hRes1
    exact (Nat.cast_ne_zero.mpr hdχ0.ne') hRes1.symm
  -- pick an irreducible constituent `χ1` of `Res_C χ`.
  obtain ⟨χ1, hχ1⟩ := exists_constt_of_ne_zero hResne
  -- `Res_C χ` is invariant under right multiplication by `B` (kernel elements act trivially).
  have hψinv : ∀ b ∈ B.subgroupOf C, ∀ x : ↥C,
      ClassFunction.res C (χ : ClassFunction G) (x * b)
        = ClassFunction.res C (χ : ClassFunction G) x := by
    intro b hb x
    rw [ClassFunction.res_apply, ClassFunction.res_apply, Subgroup.coe_mul, Irr.coe_apply,
      Irr.coe_apply]
    exact Irr.apply_mul_mem_ker χ (hBker (Subgroup.mem_subgroupOf.mp hb))
  -- hence `B ≤ ker χ1` (constituent of an inflated character).
  have hkerχ1 : B.subgroupOf C ≤ χ1.ker := by
    apply le_ker_of_cfMod_constt (descend (ClassFunction.res C (χ : ClassFunction G)) hψinv)
    rw [cfMod_descend]
    exact hχ1
  -- Frobenius reciprocity: `χ` is a constituent of `Ind_C^G χ1`.
  have hFrob : ⟪ClassFunction.ind C (χ1 : ClassFunction ↥C), (χ : ClassFunction G)⟫_[G] ≠ 0 := by
    rw [ClassFunction.cfInner_ind_eq_cfInner_res, ClassFunction.cfInner_conj_symm,
      starRingEnd_apply, ne_eq, star_eq_zero]
    exact hχ1
  -- degree bound `χ 1 ≤ (Ind_C^G χ1) 1`.
  have hstep := char1_ge_constt (Irr.isChar χ1).ind hFrob
  -- `cfInd1`: `(Ind_C^G χ1) 1 = |G : C| · χ1 1`.
  obtain ⟨dχ1, _hdχ10, hdχ1⟩ := χ1.exists_degree
  have hindre : (ClassFunction.ind C (χ1 : ClassFunction ↥C) 1).re = (C.index : ℝ) * (χ1 1).re := by
    have hcast : ClassFunction.ind C (χ1 : ClassFunction ↥C) 1 = ((C.index * dχ1 : ℕ) : ℂ) := by
      rw [ClassFunction.ind_apply_one, Irr.coe_apply, hdχ1, ← Nat.cast_mul]
    rw [hcast, Complex.natCast_re, hdχ1, Complex.natCast_re, Nat.cast_mul]
  rw [hindre] at hstep
  -- the isolated Schur bound gives `(χ1 1).re² ≤ |C : D|`, so `(χ1 1).re ≤ √|C : D|`.
  have haux : (χ1 1).re ^ 2 ≤ (D.relIndex C : ℝ) :=
    irr1_bound_charCenter (B.subgroupOf C) (D.subgroupOf C) χ1 hkerχ1
      (Subgroup.subgroupOf_mono C hBD) hZ
  have hsqrt : (χ1 1).re ≤ Real.sqrt (D.relIndex C : ℝ) := Real.le_sqrt_of_sq_le haux
  -- assemble.
  calc (χ 1).re ≤ (C.index : ℝ) * (χ1 1).re := hstep
    _ ≤ (C.index : ℝ) * Real.sqrt (D.relIndex C : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg _)

end

section

/-! ### General helper lemmas (norms of characters, a finite non-negativity argument) -/

section Helpers

variable {G₀ : Type*} [Group G₀] [Fintype G₀]

/-- A character of norm `1` whose value at `1` is a positive real is an irreducible character
(the `vchar_norm1` sign is `+`, ruled out by positivity of the degree). -/
theorem exists_irr_coe_eq_of_norm_one {φ : ClassFunction G₀} (hφ : φ.IsChar)
    (h1 : ⟪φ, φ⟫_[G₀] = 1) {d : ℕ} (hd : 0 < d) (hφ1 : φ 1 = (d : ℂ)) :
    ∃ χ : Irr G₀, (χ : ClassFunction G₀) = φ := by
  rcases hφ.isVirtualChar.exists_eq_or_eq_neg_of_cfInner_self_eq_one h1 with
    ⟨χ, hχ⟩ | ⟨χ, hχ⟩
  · exact ⟨χ, hχ.symm⟩
  · exfalso
    obtain ⟨d', hd'0, hd'⟩ := χ.exists_degree
    have h2 : φ 1 = -(χ 1) := by rw [hχ]; simp
    rw [hφ1, hd'] at h2
    have hr : (d : ℝ) = -(d' : ℝ) := by exact_mod_cast h2
    have hdp : (0 : ℝ) < d := by exact_mod_cast hd
    have hd'p : (0 : ℝ) < d' := by exact_mod_cast hd'0
    linarith

/-- A character whose value at `1` is a positive real has self-inner-product at least `1`. -/
theorem one_le_cfInner_nat {φ : ClassFunction G₀} (hφ : φ.IsChar) {n : ℕ}
    (hn : ⟪φ, φ⟫_[G₀] = (n : ℂ)) {d : ℕ} (hd : 0 < d) (hφ1 : φ 1 = (d : ℂ)) : 1 ≤ n := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exfalso
    obtain ⟨c, hc⟩ := hφ.isVirtualChar
    have hsq := ClassFunction.sum_sq_coeff_eq_cfInner_self hc
    rw [hn] at hsq
    have hsqZ : (∑ χ : Irr G₀, (c χ) ^ 2 : ℤ) = 0 := by exact_mod_cast hsq
    have hallc : ∀ χ : Irr G₀, c χ = 0 := by
      intro χ
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun χ _ => sq_nonneg (c χ))).mp hsqZ χ (Finset.mem_univ χ)
      simpa using hz
    have hφ0 : φ = 0 := by
      rw [hc]
      refine Finset.sum_eq_zero fun χ _ => ?_
      rw [hallc χ]; simp
    have : φ 1 = 0 := by rw [hφ0]; simp
    rw [hφ1] at this
    exact absurd (by exact_mod_cast this : d = 0) hd.ne'
  · exact hpos

open scoped Classical in
/-- **The finite non-negativity ("norm-counting") argument.**  Given non-negative
"multiplicities" `emul` and a "Gram matrix" `M` of non-negative integers with `M t t ≥ 1`,
if `∑_{t,s} emul t · emul s · M t s = ∑_t (emul t)²` then `M t t = 1` for every `t` with
`emul t ≠ 0` (diagonal), and `M t s = 0` for distinct `t, s` both with nonzero `emul`
(off-diagonal).  This is the combinatorial core that replaces MathComp's Mackey-based
`constt_Inertia_bijection`. -/
theorem counting_argument {ι : Type*} [Fintype ι]
    (emul : ι → ℕ) (M : ι → ι → ℕ) (hMdiag : ∀ t, 1 ≤ M t t)
    (key : ∑ t : ι, ∑ s : ι, emul t * emul s * M t s = ∑ t : ι, emul t ^ 2) :
    (∀ t, emul t ≠ 0 → M t t = 1) ∧
      (∀ t s, t ≠ s → emul t ≠ 0 → emul s ≠ 0 → M t s = 0) := by
  classical
  have hdiag_le_total : ∀ t : ι,
      emul t ^ 2 * M t t ≤ ∑ s : ι, emul t * emul s * M t s := by
    intro t
    have h := Finset.single_le_sum (f := fun s => emul t * emul s * M t s)
      (fun s _ => Nat.zero_le _) (Finset.mem_univ t)
    calc emul t ^ 2 * M t t = emul t * emul t * M t t := by ring
      _ ≤ ∑ s : ι, emul t * emul s * M t s := h
  have hsq_le_diag : ∀ t : ι, emul t ^ 2 ≤ emul t ^ 2 * M t t := fun t =>
    le_mul_of_one_le_right (Nat.zero_le _) (hMdiag t)
  have hD_le_total : (∑ t : ι, emul t ^ 2 * M t t)
      ≤ ∑ t : ι, ∑ s : ι, emul t * emul s * M t s :=
    Finset.sum_le_sum fun t _ => hdiag_le_total t
  have hsq_le_D : (∑ t : ι, emul t ^ 2) ≤ ∑ t : ι, emul t ^ 2 * M t t :=
    Finset.sum_le_sum fun t _ => hsq_le_diag t
  have hD_eq_sq : (∑ t : ι, emul t ^ 2 * M t t) = ∑ t : ι, emul t ^ 2 :=
    le_antisymm (le_trans hD_le_total (le_of_eq key)) hsq_le_D
  have htot_eq_D : (∑ t : ι, ∑ s : ι, emul t * emul s * M t s)
      = ∑ t : ι, emul t ^ 2 * M t t := by rw [key, ← hD_eq_sq]
  refine ⟨?_, ?_⟩
  · intro t ht
    have hpt := (Finset.sum_eq_sum_iff_of_le (fun t _ => hsq_le_diag t)).mp hD_eq_sq.symm t
      (Finset.mem_univ t)
    have hpos2 : 0 < emul t ^ 2 := pow_pos (Nat.pos_of_ne_zero ht) 2
    have heqm : emul t ^ 2 * 1 = emul t ^ 2 * M t t := by rw [mul_one]; exact hpt
    have hone : 1 = M t t := Nat.eq_of_mul_eq_mul_left hpos2 heqm
    omega
  · intro t s hts ht hs
    have hpt := (Finset.sum_eq_sum_iff_of_le (fun t _ => hdiag_le_total t)).mp htot_eq_D.symm t
      (Finset.mem_univ t)
    have hsplit : (∑ s : ι, emul t * emul s * M t s)
        = emul t * emul t * M t t + ∑ s ∈ Finset.univ.erase t, emul t * emul s * M t s :=
      (Finset.add_sum_erase Finset.univ (fun s => emul t * emul s * M t s)
        (Finset.mem_univ t)).symm
    have hdiag_eq : emul t ^ 2 * M t t = emul t * emul t * M t t := by ring
    rw [hsplit, ← hdiag_eq] at hpt
    have herase0 : (∑ s ∈ Finset.univ.erase t, emul t * emul s * M t s) = 0 := by omega
    have hs_mem : s ∈ Finset.univ.erase t := Finset.mem_erase.mpr ⟨Ne.symm hts, Finset.mem_univ s⟩
    have hterm0 : emul t * emul s * M t s = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp herase0 s hs_mem
    rcases Nat.mul_eq_zero.mp hterm0 with h | h
    · rcases Nat.mul_eq_zero.mp h with h' | h'
      · exact absurd h' ht
      · exact absurd h' hs
    · exact h

end Helpers

variable {G : Type u} [Group G] [Fintype G] {H : Subgroup G} [hHN : H.Normal] [Fintype H]
variable (θ : Irr H) [Fintype ↥θ.inertia]

/-! ### The constituent sets `calA`, `calB` and the multiplicities `e_` -/

open scoped Classical in
/-- `calA`: the irreducible constituents of `Ind_H^T θ`, indexed by those `t : Irr T` for
which `θ` is a constituent of `Res_H^T t`.  MathComp: `irr_constt ('Ind[T] theta)`. -/
def calA : Finset (Irr ↥θ.inertia) :=
  Finset.univ.filter fun t =>
    ⟪ClassFunction.resNested (Irr.le_inertia θ) (t : ClassFunction ↥θ.inertia),
        (θ : ClassFunction ↥H)⟫_[↥H] ≠ 0

open scoped Classical in
/-- `calB`: the irreducible constituents of `Ind_H^G θ`, indexed by those `χ : Irr G` for
which `θ` is a constituent of `Res_H χ`.  MathComp: `irr_constt ('Ind[G] theta)`. -/
def calB : Finset (Irr G) :=
  Finset.univ.filter fun χ =>
    ⟪ClassFunction.res H (χ : ClassFunction G), (θ : ClassFunction ↥H)⟫_[↥H] ≠ 0

/-- The multiplicity `e_ t = ⟪Ind_H^T θ, t⟫_T` of `t` in `Ind_H^T θ`.
MathComp: `e_ t := '['Ind theta, 'chi[T]_t]`. -/
def mult (t : Irr ↥θ.inertia) : ℂ :=
  ⟪ClassFunction.indNested (Irr.le_inertia θ) (θ : ClassFunction ↥H),
      (t : ClassFunction ↥θ.inertia)⟫_[↥θ.inertia]

omit [Fintype G] in
theorem mem_calA_iff (t : Irr ↥θ.inertia) :
    t ∈ calA θ ↔
      ⟪ClassFunction.resNested (Irr.le_inertia θ) (t : ClassFunction ↥θ.inertia),
          (θ : ClassFunction ↥H)⟫_[↥H] ≠ 0 := by
  classical
  simp [calA]

omit [Fintype ↥θ.inertia] hHN in
theorem mem_calB_iff (χ : Irr G) :
    χ ∈ calB θ ↔
      ⟪ClassFunction.res H (χ : ClassFunction G), (θ : ClassFunction ↥H)⟫_[↥H] ≠ 0 := by
  classical
  simp [calB]

/-! ### `Ind_H^T θ` is a character and `mult` is its (natural) multiplicity function -/

omit [Fintype G] in
/-- `Ind_H^T θ` is a character of `T`. -/
theorem indNested_theta_isChar :
    (ClassFunction.indNested (Irr.le_inertia θ) (θ : ClassFunction ↥H)).IsChar := by
  -- `indNested` is `ind` on a transported class function; the transported `θ` is a character.
  haveI : Fintype ↥(H.subgroupOf θ.inertia) := Fintype.ofFinite _
  rw [ClassFunction.indNested_def]
  refine ClassFunction.IsChar.ind ?_
  -- the transported class function is the coercion of an irreducible character
  have hcoe : (ClassFunction.congr (Subgroup.subgroupOfEquivOfLe (Irr.le_inertia θ))).symm
      (θ : ClassFunction ↥H)
      = ((Irr.congr (Subgroup.subgroupOfEquivOfLe (Irr.le_inertia θ)).symm θ :
          Irr ↥(H.subgroupOf θ.inertia)) : ClassFunction ↥(H.subgroupOf θ.inertia)) := rfl
  rw [hcoe]
  exact Irr.isChar _

omit [Fintype G] in
/-- `Frobenius reciprocity` links `mult t` to the `calA` membership condition:
`mult t = conj ⟪Res_H^T t, θ⟫_H`.  In particular `mult t ≠ 0 ↔ t ∈ calA`. -/
theorem mult_eq_conj (t : Irr ↥θ.inertia) :
    mult θ t = starRingEnd ℂ
      ⟪ClassFunction.resNested (Irr.le_inertia θ) (t : ClassFunction ↥θ.inertia),
          (θ : ClassFunction ↥H)⟫_[↥H] := by
  rw [mult, ClassFunction.cfInner_indNested_eq_cfInner_resNested,
    ClassFunction.cfInner_conj_symm]

omit [Fintype G] in
theorem mult_ne_zero_iff (t : Irr ↥θ.inertia) : mult θ t ≠ 0 ↔ t ∈ calA θ := by
  rw [mem_calA_iff, mult_eq_conj, ne_eq, ne_eq, starRingEnd_apply, star_eq_zero]

/-! ### Transitivity of induction and the sum formula (Peterfalvi (1.7)(a), last clause) -/

/-- Transitivity: `Ind_H^G θ = Ind_T^G (Ind_H^T θ)`.  MathComp: `cfIndInd`. -/
theorem cfInd_theta_eq_indNested :
    ClassFunction.ind H (θ : ClassFunction ↥H)
      = ClassFunction.ind θ.inertia
          (ClassFunction.indNested (Irr.le_inertia θ) (θ : ClassFunction ↥H)) :=
  (ClassFunction.ind_indNested (Irr.le_inertia θ) (θ : ClassFunction ↥H)).symm

omit [Fintype G] in
/-- Basis expansion of `Ind_H^T θ` in the irreducible characters of `T`, with `mult` as the
coefficients.  MathComp: `cfun_sum_constt`. -/
theorem indNested_eq_sum :
    ClassFunction.indNested (Irr.le_inertia θ) (θ : ClassFunction ↥H)
      = ∑ t : Irr ↥θ.inertia, mult θ t • (t : ClassFunction ↥θ.inertia) :=
  ClassFunction.eq_sum_cfInner_smul _

/-- **Peterfalvi (1.7)(a), sum-formula clause** (no isometry needed):
`Ind_H^G θ = ∑_{t ∈ calA} e_t · Ind_T^G t`.  MathComp: the final conjunct of
`cfInd_sum_Inertia`. -/
theorem cfInd_eq_sum_calA :
    ClassFunction.ind H (θ : ClassFunction ↥H)
      = ∑ t ∈ calA θ, mult θ t • ClassFunction.ind θ.inertia (t : ClassFunction ↥θ.inertia) := by
  rw [cfInd_theta_eq_indNested, indNested_eq_sum, map_sum]
  simp_rw [map_smul]
  refine (Finset.sum_subset (Finset.subset_univ (calA θ)) ?_).symm
  intro t _ ht
  have hmt : mult θ t = 0 := by
    by_contra h; exact ht ((mult_ne_zero_iff θ t).mp h)
  rw [hmt, zero_smul]

/-! ### The norm of `Ind_H^G θ` (Clifford at `(H, G)`) -/

omit [Fintype ↥θ.inertia] in
/-- `⟪Ind_H^G θ, Ind_H^G θ⟫_G = |T : H|` (Clifford at the `(H, G)` level).
MathComp: `cfnorm_Ind_irr`-shaped consequence of `cfResInd_sum_cfclass`. -/
theorem cfInner_cfInd_self :
    ⟪ClassFunction.ind H (θ : ClassFunction ↥H),
        ClassFunction.ind H (θ : ClassFunction ↥H)⟫_[G]
      = (H.relIndex θ.inertia : ℂ) := by
  have h1 : ⟪ClassFunction.res H (ClassFunction.ind H (θ : ClassFunction ↥H)),
      (θ : ClassFunction ↥H)⟫_[↥H] = (H.relIndex θ.inertia : ℂ) := θ.cfInner_res_ind_self
  rw [ClassFunction.cfInner_ind_eq_cfInner_res, ClassFunction.cfInner_conj_symm, h1, map_natCast]

/-! ### The norm of `Ind_H^T θ` (Clifford at `(H, T)`)

The Clifford machinery of `Inertia.lean` is stated for a subgroup of an ambient *type*.  To
apply it at the `(H, T)` level we transport `θ` to `thetaT : Irr (H.subgroupOf T)` (viewing
`H` inside `T = θ.inertia`) and show that its inertia group computed inside `T` is all of `T`
(the defining property of the inertia group). -/

section HTLevel

variable [Fintype ↥(H.subgroupOf θ.inertia)]

/-- `θ` transported to an irreducible character of `H` viewed as a subgroup of `T = θ.inertia`.
MathComp: the implicit identification `'chi_s` on `H ≤ T`. -/
def thetaT : Irr ↥(H.subgroupOf θ.inertia) :=
  Irr.congr (Subgroup.subgroupOfEquivOfLe (Irr.le_inertia θ)).symm θ

omit [Fintype G] [Fintype ↥θ.inertia] in
theorem thetaT_apply (m : ↥(H.subgroupOf θ.inertia)) :
    thetaT θ m = θ (Subgroup.subgroupOfEquivOfLe (Irr.le_inertia θ) m) := by
  rw [thetaT, Irr.congr_apply, MulEquiv.symm_symm]

omit [Fintype G] in
/-- `Ind_H^T θ` (as `indNested`) equals `ind` of the transported character `thetaT`. -/
theorem indNested_eq_ind :
    ClassFunction.indNested (Irr.le_inertia θ) (θ : ClassFunction ↥H)
      = ClassFunction.ind (H.subgroupOf θ.inertia)
          (thetaT θ : ClassFunction ↥(H.subgroupOf θ.inertia)) := by
  rw [ClassFunction.indNested_def]
  congr 1

omit [Fintype G] [Fintype ↥θ.inertia] in
/-- **The inertia group of `θ` computed inside `T = θ.inertia` is all of `T`.**  This is the
defining property of the inertia group, transported through the `H ≤ T` identification.
MathComp: `T ⊆ 'I[theta]` with `T = 'I_G[theta]` (`sub_inertia_Res`/`subsetIr`). -/
theorem thetaT_inertia_eq_top :
    (thetaT θ).inertia = (⊤ : Subgroup ↥θ.inertia) := by
  haveI : (H.subgroupOf θ.inertia).Normal := hHN.subgroupOf θ.inertia
  rw [Subgroup.eq_top_iff']
  intro t
  rw [Irr.mem_inertia]
  have hθt : θ.conjg (↑t : G) = θ := Irr.mem_inertia.mp t.2
  refine Irr.ext fun m => ?_
  rw [Irr.conjg_apply, thetaT_apply, thetaT_apply]
  -- reduce to the ambient-`G` inertia identity for `θ`
  have key : (Subgroup.subgroupOfEquivOfLe (Irr.le_inertia θ)) ((MulAut.conjNormal t).symm m)
      = (MulAut.conjNormal (↑t : G)).symm
          ((Subgroup.subgroupOfEquivOfLe (Irr.le_inertia θ)) m) := by
    apply Subtype.ext
    rw [MulAut.conjNormal_symm_apply]
    have hL : ((Subgroup.subgroupOfEquivOfLe (Irr.le_inertia θ))
        ((MulAut.conjNormal t).symm m) : G)
        = (((MulAut.conjNormal t).symm m : ↥θ.inertia) : G) := rfl
    have hR : ((Subgroup.subgroupOfEquivOfLe (Irr.le_inertia θ)) m : G)
        = ((m : ↥θ.inertia) : G) := rfl
    rw [hL, hR, MulAut.conjNormal_symm_apply]
    push_cast
    group
  rw [key]
  rw [← Irr.conjg_apply, hθt]

end HTLevel

omit [Fintype G] in
/-- `⟪Ind_H^T θ, Ind_H^T θ⟫_T = |T : H|` (Clifford at the `(H, T)` level). -/
theorem cfInner_indNested_self :
    ⟪ClassFunction.indNested (Irr.le_inertia θ) (θ : ClassFunction ↥H),
        ClassFunction.indNested (Irr.le_inertia θ) (θ : ClassFunction ↥H)⟫_[↥θ.inertia]
      = (H.relIndex θ.inertia : ℂ) := by
  haveI : Fintype ↥(H.subgroupOf θ.inertia) := Fintype.ofFinite _
  haveI : (H.subgroupOf θ.inertia).Normal := hHN.subgroupOf θ.inertia
  have h1 : ⟪ClassFunction.res (H.subgroupOf θ.inertia)
        (ClassFunction.ind (H.subgroupOf θ.inertia)
          (thetaT θ : ClassFunction ↥(H.subgroupOf θ.inertia))),
      (thetaT θ : ClassFunction ↥(H.subgroupOf θ.inertia))⟫_[↥(H.subgroupOf θ.inertia)]
      = ((H.subgroupOf θ.inertia).relIndex (thetaT θ).inertia : ℂ) :=
    (thetaT θ).cfInner_res_ind_self
  rw [indNested_eq_ind, ClassFunction.cfInner_ind_eq_cfInner_res,
    ClassFunction.cfInner_conj_symm, h1, thetaT_inertia_eq_top,
    Subgroup.relIndex_top_right, map_natCast]
  rfl

/-! ### Peterfalvi (1.7)(a): the Clifford correspondence -/

/-- `Ind_H^G θ = ∑_{t : Irr T} e_t · Ind_T^G t` (over all of `Irr T`). -/
theorem cfInd_eq_sum_univ :
    ClassFunction.ind H (θ : ClassFunction ↥H)
      = ∑ t : Irr ↥θ.inertia,
          mult θ t • ClassFunction.ind θ.inertia (t : ClassFunction ↥θ.inertia) := by
  rw [cfInd_theta_eq_indNested, indNested_eq_sum, map_sum]
  simp_rw [map_smul]

/-- **Peterfalvi (1.7)(a): the Clifford correspondence.**  Induction `Ind_T^G` restricts to a
bijection from the constituents of `Ind_H^T θ` (`calA`) to those of `Ind_H^G θ` (`calB`),
with `Ind_H^G θ = ∑_{t ∈ calA} e_t · Ind_T^G t`.  The four conjuncts are, in order:
irreducibility of `Ind_T^G t` on `calA`, injectivity on `calA`, the image is exactly `calB`,
and the sum decomposition.  MathComp: `cfInd_sum_Inertia` (`PFsection1.v`); its Coq proof
invokes the Mackey-based `constt_Inertia_bijection`, which we replace with a norm-counting
argument (see `counting_argument`). -/
theorem cfInd_sum_Inertia :
    (∀ t : Irr ↥θ.inertia,
        ⟪ClassFunction.resNested (Irr.le_inertia θ) (t : ClassFunction ↥θ.inertia),
            (θ : ClassFunction ↥H)⟫_[↥H] ≠ 0 →
          ∃ χ : Irr G, (χ : ClassFunction G)
            = ClassFunction.ind θ.inertia (t : ClassFunction ↥θ.inertia)) ∧
      (∀ t t' : Irr ↥θ.inertia,
        ⟪ClassFunction.resNested (Irr.le_inertia θ) (t : ClassFunction ↥θ.inertia),
            (θ : ClassFunction ↥H)⟫_[↥H] ≠ 0 →
        ⟪ClassFunction.resNested (Irr.le_inertia θ) (t' : ClassFunction ↥θ.inertia),
            (θ : ClassFunction ↥H)⟫_[↥H] ≠ 0 →
          ClassFunction.ind θ.inertia (t : ClassFunction ↥θ.inertia)
            = ClassFunction.ind θ.inertia (t' : ClassFunction ↥θ.inertia) → t = t') ∧
      (∀ χ : Irr G,
        ⟪ClassFunction.res H (χ : ClassFunction G), (θ : ClassFunction ↥H)⟫_[↥H] ≠ 0 ↔
          ∃ t : Irr ↥θ.inertia,
            ⟪ClassFunction.resNested (Irr.le_inertia θ) (t : ClassFunction ↥θ.inertia),
                (θ : ClassFunction ↥H)⟫_[↥H] ≠ 0 ∧
              (χ : ClassFunction G)
                = ClassFunction.ind θ.inertia (t : ClassFunction ↥θ.inertia)) ∧
      ClassFunction.ind H (θ : ClassFunction ↥H)
        = ∑ t ∈ calA θ,
            mult θ t • ClassFunction.ind θ.inertia (t : ClassFunction ↥θ.inertia) := by
  classical
  -- natural-number multiplicities of `Ind_H^T θ`
  choose emul hemul using fun t => (indNested_theta_isChar θ).cfInner_mem_nat t
  have hmult : ∀ t : Irr ↥θ.inertia, mult θ t = (emul t : ℂ) := fun t => hemul t
  -- the (natural-number) Gram matrix `M t s = ⟪Ind_T^G t, Ind_T^G s⟫`
  choose Mmat hM using fun (p : Irr ↥θ.inertia × Irr ↥θ.inertia) =>
    ((Irr.isChar p.1).ind).cfInner_mem_nat' ((Irr.isChar p.2).ind)
  -- degrees of `Ind_T^G t`
  have hdeg : ∀ t : Irr ↥θ.inertia,
      ∃ d : ℕ, 0 < d ∧ ClassFunction.ind θ.inertia (t : ClassFunction ↥θ.inertia) 1 = (d : ℂ) := by
    intro t
    obtain ⟨dt, hdt0, hdt⟩ := t.exists_degree
    have hidx : 0 < θ.inertia.index := by rw [Subgroup.index_eq_card]; exact Nat.card_pos
    refine ⟨θ.inertia.index * dt, Nat.mul_pos hidx hdt0, ?_⟩
    rw [ClassFunction.ind_apply_one, Irr.coe_apply, hdt]
    push_cast; ring
  -- diagonal Gram entries are at least `1`
  have hMdiag : ∀ t : Irr ↥θ.inertia, 1 ≤ Mmat (t, t) := by
    intro t
    obtain ⟨d, hd0, hd⟩ := hdeg t
    exact one_le_cfInner_nat (Irr.isChar t).ind (hM (t, t)) hd0 hd
  -- the norm identity, expanded on the `G` side …
  have hNormG_expand : ⟪ClassFunction.ind H (θ : ClassFunction ↥H),
        ClassFunction.ind H (θ : ClassFunction ↥H)⟫_[G]
      = ∑ t : Irr ↥θ.inertia, ∑ s : Irr ↥θ.inertia,
          (emul t : ℂ) * (emul s : ℂ) * (Mmat (t, s) : ℂ) := by
    rw [cfInd_eq_sum_univ, ClassFunction.cfInner_sum_left]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ClassFunction.cfInner_smul_left, ClassFunction.cfInner_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ClassFunction.cfInner_smul_right, hM (t, s), hmult t, hmult s, map_natCast]
    ring
  -- … and on the `T` side
  have hcT : ClassFunction.indNested (Irr.le_inertia θ) (θ : ClassFunction ↥H)
      = ∑ t : Irr ↥θ.inertia, ((emul t : ℤ) : ℂ) • (t : ClassFunction ↥θ.inertia) := by
    rw [indNested_eq_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hmult t]; norm_cast
  have hNormT_expand : ⟪ClassFunction.indNested (Irr.le_inertia θ) (θ : ClassFunction ↥H),
        ClassFunction.indNested (Irr.le_inertia θ) (θ : ClassFunction ↥H)⟫_[↥θ.inertia]
      = ∑ t : Irr ↥θ.inertia, (emul t : ℂ) ^ 2 := by
    rw [← ClassFunction.sum_sq_coeff_eq_cfInner_self hcT]
    push_cast; rfl
  -- both norms are `|T : H|`, so the two expansions are equal, hence equal over `ℕ`
  have hCeq : (∑ t : Irr ↥θ.inertia, ∑ s : Irr ↥θ.inertia,
        (emul t : ℂ) * (emul s : ℂ) * (Mmat (t, s) : ℂ))
      = ∑ t : Irr ↥θ.inertia, (emul t : ℂ) ^ 2 := by
    rw [← hNormG_expand, ← hNormT_expand, cfInner_cfInd_self, cfInner_indNested_self]
  have hkey : ∑ t : Irr ↥θ.inertia, ∑ s : Irr ↥θ.inertia, emul t * emul s * Mmat (t, s)
      = ∑ t : Irr ↥θ.inertia, emul t ^ 2 := by exact_mod_cast hCeq
  -- apply the counting argument
  obtain ⟨hdiag1, hoff0⟩ := counting_argument emul (fun t s => Mmat (t, s)) hMdiag hkey
  -- bridge: `calA` membership ↔ nonzero `emul`
  have hemul_ne : ∀ t : Irr ↥θ.inertia, t ∈ calA θ → emul t ≠ 0 := by
    intro t ht h0
    have hm : mult θ t = 0 := by rw [hmult t, h0, Nat.cast_zero]
    exact (mult_ne_zero_iff θ t).mpr ht hm
  -- irreducibility of `Ind_T^G t` on `calA`
  have hAtoB : ∀ t : Irr ↥θ.inertia, t ∈ calA θ →
      ∃ χ : Irr G, (χ : ClassFunction G)
        = ClassFunction.ind θ.inertia (t : ClassFunction ↥θ.inertia) := by
    intro t ht
    obtain ⟨d, hd0, hd⟩ := hdeg t
    have hnorm1 : ⟪ClassFunction.ind θ.inertia (t : ClassFunction ↥θ.inertia),
        ClassFunction.ind θ.inertia (t : ClassFunction ↥θ.inertia)⟫_[G] = 1 := by
      rw [hM (t, t), hdiag1 t (hemul_ne t ht), Nat.cast_one]
    exact exists_irr_coe_eq_of_norm_one (Irr.isChar t).ind hnorm1 hd0 hd
  -- injectivity of `Ind_T^G` on `calA`
  have hInj : ∀ t t' : Irr ↥θ.inertia, t ∈ calA θ → t' ∈ calA θ →
      ClassFunction.ind θ.inertia (t : ClassFunction ↥θ.inertia)
        = ClassFunction.ind θ.inertia (t' : ClassFunction ↥θ.inertia) → t = t' := by
    intro t t' ht ht' heq
    by_contra hne
    have hcontra : ((Mmat (t, t') : ℕ) : ℂ) = ((Mmat (t, t) : ℕ) : ℂ) := by
      rw [← hM (t, t'), ← hM (t, t), ← heq]
    rw [hoff0 t t' hne (hemul_ne t ht) (hemul_ne t' ht'), hdiag1 t (hemul_ne t ht)] at hcontra
    norm_num at hcontra
  refine ⟨fun t hcond => hAtoB t ((mem_calA_iff θ t).mpr hcond),
    fun t t' hc hc' => hInj t t' ((mem_calA_iff θ t).mpr hc) ((mem_calA_iff θ t').mpr hc'),
    ?_, cfInd_eq_sum_calA θ⟩
  -- the image of `AtoB` is exactly `calB`
  intro χ
  -- choose the irreducible image of each `t ∈ calA`
  have htotal : ∀ t : Irr ↥θ.inertia, ∃ ψ : Irr G,
      t ∈ calA θ → (ψ : ClassFunction G)
        = ClassFunction.ind θ.inertia (t : ClassFunction ↥θ.inertia) := by
    intro t
    by_cases ht : t ∈ calA θ
    · obtain ⟨ψ, hψ⟩ := hAtoB t ht; exact ⟨ψ, fun _ => hψ⟩
    · exact ⟨Irr.one, fun h => absurd h ht⟩
  choose chi hchi using htotal
  have hindH : ClassFunction.ind H (θ : ClassFunction ↥H)
      = ∑ t ∈ calA θ, mult θ t • (chi t : ClassFunction G) := by
    rw [cfInd_eq_sum_calA]
    exact Finset.sum_congr rfl fun t ht => by rw [hchi t ht]
  have hchi_inj : ∀ t t' : Irr ↥θ.inertia, t ∈ calA θ → t' ∈ calA θ → chi t = chi t' → t = t' := by
    intro t t' ht ht' he
    refine hInj t t' ht ht' ?_
    rw [← hchi t ht, ← hchi t' ht', he]
  have hbridge : ⟪ClassFunction.ind H (θ : ClassFunction ↥H), (χ : ClassFunction G)⟫_[G]
      = starRingEnd ℂ ⟪ClassFunction.res H (χ : ClassFunction G), (θ : ClassFunction ↥H)⟫_[↥H] := by
    rw [ClassFunction.cfInner_ind_eq_cfInner_res, ClassFunction.cfInner_conj_symm]
  have hBmem : ⟪ClassFunction.res H (χ : ClassFunction G), (θ : ClassFunction ↥H)⟫_[↥H] ≠ 0
      ↔ ⟪ClassFunction.ind H (θ : ClassFunction ↥H), (χ : ClassFunction G)⟫_[G] ≠ 0 := by
    rw [hbridge, ne_eq, ne_eq, starRingEnd_apply, star_eq_zero]
  have hval : ⟪ClassFunction.ind H (θ : ClassFunction ↥H), (χ : ClassFunction G)⟫_[G]
      = ∑ t ∈ calA θ, mult θ t * (if chi t = χ then (1 : ℂ) else 0) := by
    rw [hindH, ClassFunction.cfInner_sum_left]
    exact Finset.sum_congr rfl fun t _ => by
      rw [ClassFunction.cfInner_smul_left, Irr.cfInner_eq]
  rw [hBmem, hval]
  constructor
  · intro hne
    obtain ⟨t, ht, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hchiχ : chi t = χ := by
      by_contra h; rw [if_neg h, mul_zero] at hterm; exact hterm rfl
    exact ⟨t, (mem_calA_iff θ t).mp ht, by rw [← hchiχ]; exact hchi t ht⟩
  · rintro ⟨t₀, hcond, hχeq⟩
    have ht₀ : t₀ ∈ calA θ := (mem_calA_iff θ t₀).mpr hcond
    have hchit₀ : chi t₀ = χ :=
      Irr.toClassFunction_injective ((hchi t₀ ht₀).trans hχeq.symm)
    have h0 : ∀ t ∈ calA θ, t ≠ t₀ →
        mult θ t * (if chi t = χ then (1 : ℂ) else 0) = 0 := by
      intro t ht htne
      by_cases hc : chi t = χ
      · exact absurd (hchi_inj t t₀ ht ht₀ (by rw [hc, hchit₀])) htne
      · rw [if_neg hc, mul_zero]
    rw [Finset.sum_eq_single_of_mem t₀ ht₀ h0, hchit₀, if_pos rfl, mul_one, hmult t₀]
    exact_mod_cast hemul_ne t₀ ht₀

end

end PF1

end
