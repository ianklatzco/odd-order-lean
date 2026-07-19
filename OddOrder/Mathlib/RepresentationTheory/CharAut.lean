/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import OddOrder.Mathlib.RepresentationTheory.CharacterArith
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# The Galois action on characters: conjugation and coprime power twists (`cfAut`)

This file is Task 7 of the M2 character-theory plan: the minimal honest slice of MathComp's
`cfAut` action (ring automorphisms of the coefficient field acting valuewise on class
functions, `classfun.v`) that the Peterfalvi sections consume.  Per the plan's task-start
resolution, it delivers exactly two actions and no general bundled `cfAut σ` framework:

1. **complex conjugation** `ClassFunction.conjC` (MathComp `cfConjC`, `phi^*%CF`), which
   permutes the irreducible characters (`Irr.conj`, `Irr.conjEquiv`; MathComp `conjC_Iirr`,
   `conjC_IirrK`), with the fixed-point lemma `Irr.conj_eq_self_iff` (`χ.conj = χ` iff `χ` is
   real-valued) in the shape PF (1.1) (`odd_eq_conj_irr1`: in an odd-order group only the
   principal character is real) needs to be *stated*;
2. **the coprime power twist** `ClassFunction.powTwist u` (`φ^(u) g := φ (g ^ u)`), for `u`
   coprime to `Monoid.exponent G`, which also permutes the irreducible characters
   (`Irr.powTwist`, `Irr.powTwist_bijective`; MathComp `aut_Iirr` composed with the power
   automorphism) — the form consumed by the PF (1.9)-style congruence arguments.

## Main definitions

* `ClassFunction.conjC φ`: pointwise complex conjugation of a class function.  MathComp:
  `cfConjC` (`classfun.v`).  (Named `conjC`, not `conj`, because
  `ClassFunction.conj_apply` is already the conjugation-*invariance* lemma
  `φ (h * g * h⁻¹) = φ g` of the Task 9 foundation file.)
* `ClassFunction.powTwist u φ`: the power twist `g ↦ φ (g ^ u)`, defined for every `u : ℕ`
  (conjugation-invariance needs no hypothesis on `u`).  MathComp: the `cfAut` image of a
  character under a `ζ ↦ ζ^u` automorphism (`classfun.v`; see `Irr.apply_pow` for the
  equivalence of the two descriptions).
* `Irr.conj χ` and `Irr.conjEquiv : Equiv.Perm (Irr G)`: conjugation as a map/permutation of
  `Irr G`.  MathComp: `conjC_Iirr`, `conjC_IirrK` (`character.v`).
* `Irr.powTwist χ hu` (for `hu : u.Coprime (Monoid.exponent G)`) and
  `Irr.powTwist_bijective`: the power twist as a map/permutation of `Irr G`.  MathComp:
  `aut_Iirr` (`character.v`).

## Main results

* `MonoidAlgebra.exists_isSimpleModule_moduleCharacter_comp`: **the engine** — for any ring
  automorphism `σ : ℂ ≃+* ℂ`, the valuewise image `σ ∘ χ` of an irreducible character is
  again the character of a simple module.  This is MathComp's `cfAut_irr`/`map_repr` argument
  (`mx_representation.v`, `character.v`): apply `σ` to the coefficients of the regular module
  (`MonoidAlgebra.mapRingEquiv`); the image of a simple submodule is a simple submodule whose
  character is `σ ∘ χ`.
* `Irr.conj_eq_self_iff`: `χ.conj = χ ↔ ∀ g, ∃ r : ℝ, χ g = r` — the real-valuedness
  fixed-point lemma for PF (1.1).
* `Complex.exists_ringEquiv_pow_of_coprime`: for `u` coprime to `n` there is a ring
  automorphism of `ℂ` raising every `n`-th root of unity to its `u`-th power — the cyclotomic
  Galois automorphism `ζ ↦ ζ^u` (`IsCyclotomicExtension.autEquivPow`) extended to `ℂ` along a
  transcendence basis (`IsAlgClosure.equivOfEquiv`).  MathComp works over `algC` (the
  algebraic numbers), where `Qn_aut_exists`-style lemmas produce the automorphism directly;
  over Mathlib's `ℂ` the transcendence-basis extension supplies the missing step.
* `Irr.apply_pow`: `χ (g ^ u) = τ (χ g)` for any ring homomorphism `τ : ℂ →+* ℂ` raising
  `Monoid.exponent G`-th roots of unity to their `u`-th powers — the bridge between the
  elementary description `g ↦ χ (g ^ u)` of the twist and the Galois description
  `σ ∘ χ`.  (Direct from the eigenvalue decomposition
  `Module.End.trace_eq_sum_zeta_pow_mul_natCast`: `χ (g ^ k) = ∑ j, (ζ^j)^k · m j` with
  multiplicities `m j` independent of `k`.)

## Design notes

* **Route: module twist, not inner products.**  The M2 plan sketches an inner-product route
  for "the twist permutes `Irr`" (integrality of the coefficients `⟪χ^(u), ψ⟫` plus the
  norm-1 classification of virtual characters).  That route has a gap that appears
  unfixable without module theory: `⟪χ^(u), ψ⟫ = |G|⁻¹ ∑ g, χ(g^u) conj(ψ g)` is `|G|⁻¹`
  times an algebraic integer, which is *not* an algebraic integer on the nose — exactly as in
  the first orthogonality relation itself, whose integrality comes from `dim Hom`, i.e. from
  modules.  So this file follows MathComp's own route (`map_repr`): the coefficientwise
  automorphism `σ` of the group algebra maps simple submodules to simple submodules and
  `σ`-twists their characters.  Conjugation uses `σ = starRingEnd ℂ` directly; the power
  twist uses `Complex.exists_ringEquiv_pow_of_coprime` and `Irr.apply_pow` to *identify*
  `g ↦ χ (g ^ u)` with a valuewise `σ`-image before applying the engine.
* **Coprime to the exponent, not the order.**  The twist hypothesis is
  `u.Coprime (Monoid.exponent G)`, which is weaker than `u.Coprime (Nat.card G)` (the
  exponent divides the order; `Nat.Coprime.of_natCard_group` converts).  PF1 call sites
  hold coprimality to `Nat.card G` (e.g. `u` coprime to the group order in (1.9)), so they
  can discharge either; the weaker hypothesis is kept because the underlying mathematics
  (roots of unity of exponent order) needs nothing more.
* **No bundled `cfAut σ`.**  MathComp's `cfAut` is a semilinear algebra morphism for an
  arbitrary `{rmorphism algC -> algC}`, with a large lemma kit.  PF1 consumes only
  conjugation and coprime power twists, so only those are exported (M2 plan scope
  discipline); the general-`σ` content lives in the single engine lemma
  `MonoidAlgebra.exists_isSimpleModule_moduleCharacter_comp`, which a future `cfAut`
  bundling could reuse unchanged.
-/

noncomputable section

open Finset LinearMap Module

universe u

/-! ### Modular inverses of exponents coprime to `Monoid.exponent G` -/

section PowInverse

variable {G : Type u} [Group G]

/-- Coprimality to the group order implies coprimality to the exponent (the exponent divides
the order).  Converts the hypothesis PF1 typically has (`u` coprime to `#G`) into the one
`Irr.powTwist` takes. -/
theorem Nat.Coprime.of_natCard_group {u : ℕ} (h : u.Coprime (Nat.card G)) :
    u.Coprime (Monoid.exponent G) :=
  Nat.Coprime.coprime_dvd_right Group.exponent_dvd_nat_card h

/-- For `u` coprime to the exponent of a finite group, the power maps `(·^u)` and `(·^u')`
are mutually inverse for a suitable `u'` (a modular inverse of `u` mod `Monoid.exponent G`,
produced by the Fermat–Euler theorem), which is again coprime to the exponent. -/
theorem Group.exists_pow_pow_eq_of_coprime_exponent [Finite G] {u : ℕ}
    (hu : u.Coprime (Monoid.exponent G)) :
    ∃ u' : ℕ, u'.Coprime (Monoid.exponent G) ∧
      (∀ g : G, (g ^ u) ^ u' = g) ∧ ∀ g : G, (g ^ u') ^ u = g := by
  set n := Monoid.exponent G with hn
  have hn0 : n ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have htot : 0 < n.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0)
  refine ⟨u ^ (n.totient - 1), Nat.Coprime.pow_left _ hu, ?_, ?_⟩ <;> intro g
  · have hmod : u * u ^ (n.totient - 1) ≡ 1 [MOD n] := by
      have hpow : u * u ^ (n.totient - 1) = u ^ n.totient := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hpow]
      exact Nat.ModEq.pow_totient hu
    rw [← pow_mul, ← pow_one g]
    conv_lhs => rw [pow_one g]
    exact pow_eq_pow_iff_modEq.mpr
      (Nat.ModEq.of_dvd (Monoid.order_dvd_exponent g) hmod)
  · have hmod : u ^ (n.totient - 1) * u ≡ 1 [MOD n] := by
      have hpow : u ^ (n.totient - 1) * u = u ^ n.totient := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpow]
      exact Nat.ModEq.pow_totient hu
    rw [← pow_mul, ← pow_one g]
    conv_lhs => rw [pow_one g]
    exact pow_eq_pow_iff_modEq.mpr
      (Nat.ModEq.of_dvd (Monoid.order_dvd_exponent g) hmod)

end PowInverse

/-! ### Conjugation and the power twist on class functions -/

namespace ClassFunction

variable {G : Type u} [Group G]

/-- Pointwise complex conjugation of a class function.  MathComp: `cfConjC`, `phi^*%CF`
(`classfun.v`).  Named `conjC` rather than `conj` because `ClassFunction.conj_apply` is
already the conjugation-invariance lemma of the foundation file. -/
def conjC (φ : ClassFunction G) : ClassFunction G :=
  ⟨fun g => starRingEnd ℂ (φ g), fun g h => by rw [conj_apply]⟩

@[simp]
theorem conjC_apply (φ : ClassFunction G) (g : G) : φ.conjC g = starRingEnd ℂ (φ g) :=
  rfl

/-- Conjugation of class functions is an involution.  MathComp: `cfConjCK` (`classfun.v`). -/
@[simp]
theorem conjC_conjC (φ : ClassFunction G) : φ.conjC.conjC = φ :=
  ext fun g => Complex.conj_conj (φ g)

/-- The power twist of a class function: `powTwist u φ = fun g => φ (g ^ u)`.  A class
function for *every* `u : ℕ` (powers commute with conjugation); only the `Irr`-permutation
statements need `u` coprime to the exponent.  MathComp: the `cfAut` image of a character
under a `ζ ↦ ζ^u` field automorphism (`classfun.v`); see `Irr.apply_pow` for the bridge. -/
def powTwist (u : ℕ) (φ : ClassFunction G) : ClassFunction G :=
  ⟨fun g => φ (g ^ u), fun g h => by
    have hconj : (h * g * h⁻¹) ^ u = h * g ^ u * h⁻¹ := by
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
    rw [hconj, conj_apply]⟩

@[simp]
theorem powTwist_apply (u : ℕ) (φ : ClassFunction G) (g : G) : φ.powTwist u g = φ (g ^ u) :=
  rfl

end ClassFunction

/-! ### The engine: coefficientwise ring automorphisms of the group algebra

For `σ : ℂ ≃+* ℂ`, applying `σ` to the coefficients of the regular module
(`MonoidAlgebra.mapRingEquiv`) fixes each basis vector `single g 1`, is `σ`-semilinear over
`ℂ`, and is multiplicative — so it maps `ℂ[G]`-submodules to `ℂ[G]`-submodules
(`twistSubmodule`), preserves simplicity (the submodule lattices are isomorphic), and
`σ`-twists traces of the `G`-action.  This is MathComp's `map_repr` argument
(`mx_representation.v`) transported from matrices to submodules of the regular module. -/

namespace MonoidAlgebra

variable {G : Type u} [Group G]
variable (σ : ℂ ≃+* ℂ)

/- Keep the unifier from normalizing `mapRingEquiv` applications coefficientwise (a defeq
blowup through `Finsupp.mapRange`); everything below manipulates it through its `_apply` and
`_single` lemmas only. -/
attribute [local irreducible] MonoidAlgebra.mapRingEquiv

private theorem mapRingEquiv_symm_apply_mapRingEquiv (x : MonoidAlgebra ℂ G) :
    mapRingEquiv G σ.symm (mapRingEquiv G σ x) = x :=
  MonoidAlgebra.ext fun m => by
    rw [mapRingEquiv_apply, mapRingEquiv_apply, RingEquiv.symm_apply_apply]

private theorem mapRingEquiv_apply_mapRingEquiv_symm (x : MonoidAlgebra ℂ G) :
    mapRingEquiv G σ (mapRingEquiv G σ.symm x) = x := by
  have h := mapRingEquiv_symm_apply_mapRingEquiv σ.symm x
  rwa [RingEquiv.symm_symm] at h

private theorem mapRingEquiv_smul (c : ℂ) (x : MonoidAlgebra ℂ G) :
    mapRingEquiv G σ (c • x) = σ c • mapRingEquiv G σ x :=
  MonoidAlgebra.ext fun m => by
    rw [mapRingEquiv_apply, MonoidAlgebra.smul_apply, MonoidAlgebra.smul_apply, smul_eq_mul,
      smul_eq_mul, map_mul, mapRingEquiv_apply]

variable (N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))

/-- The image of a submodule of the regular module under the coefficientwise ring
automorphism `mapRingEquiv G σ`: again a `ℂ[G]`-submodule, since the automorphism is
multiplicative and surjective.  The simple-module witness behind `Irr.conj` and
`Irr.powTwist`. -/
def twistSubmodule : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) where
  carrier := mapRingEquiv G σ '' (N : Set (MonoidAlgebra ℂ G))
  add_mem' := by
    rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, N.add_mem ha hb, map_add _ a b⟩
  zero_mem' := ⟨0, N.zero_mem, map_zero _⟩
  smul_mem' := by
    rintro r x ⟨a, ha, rfl⟩
    refine ⟨mapRingEquiv G σ.symm r * a, N.smul_mem _ ha, ?_⟩
    rw [map_mul, mapRingEquiv_apply_mapRingEquiv_symm, smul_eq_mul]

theorem mem_twistSubmodule {x : MonoidAlgebra ℂ G} :
    x ∈ twistSubmodule σ N ↔ mapRingEquiv G σ.symm x ∈ N := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [mapRingEquiv_symm_apply_mapRingEquiv]
  · intro h
    exact ⟨mapRingEquiv G σ.symm x, h, mapRingEquiv_apply_mapRingEquiv_symm σ x⟩

theorem twistSubmodule_mono {N P : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)}
    (h : N ≤ P) : twistSubmodule σ N ≤ twistSubmodule σ P := by
  intro x hx
  rw [mem_twistSubmodule] at hx ⊢
  exact h hx

theorem twistSubmodule_symm_twistSubmodule :
    twistSubmodule σ.symm (twistSubmodule σ N) = N := by
  ext x
  rw [mem_twistSubmodule, mem_twistSubmodule, RingEquiv.symm_symm,
    mapRingEquiv_symm_apply_mapRingEquiv]

theorem twistSubmodule_twistSubmodule_symm :
    twistSubmodule σ (twistSubmodule σ.symm N) = N := by
  have h := twistSubmodule_symm_twistSubmodule σ.symm N
  rwa [RingEquiv.symm_symm] at h

/-- The twisted submodule of a simple submodule is simple: the coefficientwise automorphism
induces an isomorphism of submodule lattices. -/
theorem isSimpleModule_twistSubmodule (hN : IsSimpleModule (MonoidAlgebra ℂ G) N) :
    IsSimpleModule (MonoidAlgebra ℂ G) (twistSubmodule σ N) := by
  haveI := hN
  let e₂ : {p : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) // p ≤ twistSubmodule σ N} ≃o
      {q : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) // q ≤ N} :=
    { toFun := fun p => ⟨twistSubmodule σ.symm p.1, by
        have h := twistSubmodule_mono σ.symm p.2
        rwa [twistSubmodule_symm_twistSubmodule] at h⟩
      invFun := fun q => ⟨twistSubmodule σ q.1, by
        have h := twistSubmodule_mono σ q.2
        exact h⟩
      left_inv := fun p => Subtype.ext (twistSubmodule_twistSubmodule_symm σ p.1)
      right_inv := fun q => Subtype.ext (twistSubmodule_symm_twistSubmodule σ q.1)
      map_rel_iff' := by
        intro p q
        simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk]
        constructor
        · intro h
          have h2 := twistSubmodule_mono σ h
          rwa [twistSubmodule_twistSubmodule_symm, twistSubmodule_twistSubmodule_symm] at h2
        · exact fun h => twistSubmodule_mono σ.symm h }
  haveI : IsSimpleOrder (Submodule (MonoidAlgebra ℂ G) ↥(twistSubmodule σ N)) :=
    ((Submodule.MapSubtype.orderIso (twistSubmodule σ N)).trans
      (e₂.trans (Submodule.MapSubtype.orderIso N).symm)).isSimpleOrder
  constructor

/-! The trace of the `G`-action on the twisted submodule.  The restriction of
`mapRingEquiv G σ` to `N` is an additive isomorphism onto `twistSubmodule σ N` that is
`σ`-semilinear over `ℂ` and commutes with the action of every `g : G` (the basis vectors
`single g 1` have coefficients `0, 1`, which `σ` fixes); transporting a basis through it
`σ`-twists all matrix entries, hence the trace.  Stated with explicit maps rather than
Mathlib's `≃ₛₗ` bundling to avoid the `RingHomInvPair` instance plumbing. -/

private def twistAddEquiv : N ≃+ twistSubmodule σ N where
  toFun x := ⟨mapRingEquiv G σ x, (mem_twistSubmodule σ N).mpr (by
    rw [mapRingEquiv_symm_apply_mapRingEquiv]
    exact x.2)⟩
  invFun y := ⟨mapRingEquiv G σ.symm y, (mem_twistSubmodule σ N).mp y.2⟩
  left_inv x := by
    apply Subtype.ext
    change mapRingEquiv G σ.symm (mapRingEquiv G σ (x : MonoidAlgebra ℂ G))
      = (x : MonoidAlgebra ℂ G)
    exact mapRingEquiv_symm_apply_mapRingEquiv σ (x : MonoidAlgebra ℂ G)
  right_inv y := by
    apply Subtype.ext
    change mapRingEquiv G σ (mapRingEquiv G σ.symm (y : MonoidAlgebra ℂ G))
      = (y : MonoidAlgebra ℂ G)
    exact mapRingEquiv_apply_mapRingEquiv_symm σ (y : MonoidAlgebra ℂ G)
  map_add' x y := by
    apply Subtype.ext
    change mapRingEquiv G σ ((x : MonoidAlgebra ℂ G) + (y : MonoidAlgebra ℂ G))
      = mapRingEquiv G σ (x : MonoidAlgebra ℂ G) + mapRingEquiv G σ (y : MonoidAlgebra ℂ G)
    exact map_add _ _ _

private theorem coe_twistAddEquiv (x : N) :
    (twistAddEquiv σ N x : MonoidAlgebra ℂ G) = mapRingEquiv G σ x :=
  rfl

private theorem coe_twistAddEquiv_symm (y : twistSubmodule σ N) :
    ((twistAddEquiv σ N).symm y : MonoidAlgebra ℂ G) = mapRingEquiv G σ.symm y :=
  rfl

private theorem twistAddEquiv_symm_smul (c : ℂ) (y : twistSubmodule σ N) :
    (twistAddEquiv σ N).symm (c • y) = σ.symm c • (twistAddEquiv σ N).symm y := by
  refine Subtype.ext ?_
  rw [coe_twistAddEquiv_symm, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower,
    coe_twistAddEquiv_symm, mapRingEquiv_smul]

private theorem twistAddEquiv_actionEnd (g : G) (x : N) :
    twistAddEquiv σ N (actionEnd (↥N) g x)
      = actionEnd (↥(twistSubmodule σ N)) g (twistAddEquiv σ N x) := by
  refine Subtype.ext ?_
  rw [coe_twistAddEquiv, actionEnd_apply, actionEnd_apply, Submodule.coe_smul,
    Submodule.coe_smul, smul_eq_mul, smul_eq_mul, map_mul, mapRingEquiv_single, map_one,
    coe_twistAddEquiv]

variable {ι : Type*}

/-- Coordinates on the twisted submodule: pull back along `twistAddEquiv`, take coordinates
in a basis `b` of `N`, and apply `σ` coordinatewise.  The `σ`-twists cancel to make this
honestly `ℂ`-linear. -/
private def twistCoords (b : Basis ι ℂ N) : twistSubmodule σ N ≃ₗ[ℂ] (ι →₀ ℂ) where
  toFun y := (b.repr ((twistAddEquiv σ N).symm y)).mapRange σ (map_zero σ)
  invFun v := twistAddEquiv σ N (b.repr.symm (v.mapRange σ.symm (map_zero σ.symm)))
  left_inv y := by
    dsimp only
    have h : (((b.repr ((twistAddEquiv σ N).symm y)).mapRange σ (map_zero σ)).mapRange σ.symm
        (map_zero σ.symm)) = b.repr ((twistAddEquiv σ N).symm y) :=
      Finsupp.ext fun i => by
        rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply, RingEquiv.symm_apply_apply]
    rw [h, LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
  right_inv v := by
    dsimp only
    rw [AddEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
    exact Finsupp.ext fun i => by
      rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply, RingEquiv.apply_symm_apply]
  map_add' y z := by
    rw [map_add, map_add]
    exact Finsupp.ext fun i => by
      simp only [Finsupp.mapRange_apply, Finsupp.add_apply, map_add]
  map_smul' c y := by
    rw [RingHom.id_apply, twistAddEquiv_symm_smul, map_smul]
    exact Finsupp.ext fun i => by
      rw [Finsupp.mapRange_apply, Finsupp.smul_apply, Finsupp.smul_apply,
        Finsupp.mapRange_apply, smul_eq_mul, smul_eq_mul, map_mul,
        RingEquiv.apply_symm_apply]

private theorem twistCoords_apply (b : Basis ι ℂ N) (y : twistSubmodule σ N) :
    twistCoords σ N b y = (b.repr ((twistAddEquiv σ N).symm y)).mapRange σ (map_zero σ) :=
  rfl

variable [Finite G]

private theorem trace_actionEnd_twistSubmodule (g : G) :
    trace ℂ (twistSubmodule σ N) (actionEnd (↥(twistSubmodule σ N)) g)
      = σ (trace ℂ N (actionEnd (↥N) g)) := by
  classical
  let b : Basis (Fin (Module.finrank ℂ N)) ℂ N := Module.finBasis ℂ N
  let b' : Basis (Fin (Module.finrank ℂ N)) ℂ (twistSubmodule σ N) :=
    Basis.ofRepr (twistCoords σ N b)
  have hb'repr : ∀ y, b'.repr y = twistCoords σ N b y := fun _ => rfl
  have hb'j : ∀ j, b' j = twistAddEquiv σ N (b j) := by
    intro j
    apply b'.repr.injective
    rw [Basis.repr_self, hb'repr, twistCoords_apply, AddEquiv.symm_apply_apply,
      Basis.repr_self, Finsupp.mapRange_single, map_one]
  have hmat : ∀ i j, LinearMap.toMatrix b' b' (actionEnd (↥(twistSubmodule σ N)) g) i j
      = σ (LinearMap.toMatrix b b (actionEnd (↥N) g) i j) := by
    intro i j
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb'j j, ← twistAddEquiv_actionEnd,
      hb'repr, twistCoords_apply, AddEquiv.symm_apply_apply, Finsupp.mapRange_apply]
  rw [LinearMap.trace_eq_matrix_trace ℂ b' (actionEnd (↥(twistSubmodule σ N)) g),
    LinearMap.trace_eq_matrix_trace ℂ b (actionEnd (↥N) g), Matrix.trace, Matrix.trace,
    map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Matrix.diag_apply, Matrix.diag_apply, hmat i i]

/-- The character of the twisted submodule is the `σ`-twist of the character:
`moduleCharacter G (twistSubmodule σ N) = σ ∘ moduleCharacter G N`. -/
theorem moduleCharacter_twistSubmodule (g : G) :
    moduleCharacter G (twistSubmodule σ N) g = σ (moduleCharacter G N g) := by
  rw [moduleCharacter_apply, moduleCharacter_apply]
  exact trace_actionEnd_twistSubmodule σ N g

/-- **The `cfAut` engine**: for a ring automorphism `σ : ℂ ≃+* ℂ` and a simple submodule
`N` of the regular module, there is a simple submodule whose character is the valuewise
`σ`-image of the character of `N`.  Both `Irr.conj` (with `σ` = complex conjugation) and
`Irr.powTwist` (with `σ` a cyclotomic automorphism, via `Irr.apply_pow`) instantiate this.
MathComp: `cfAut_irr` via `map_repr` (`character.v`, `mx_representation.v`). -/
theorem exists_isSimpleModule_moduleCharacter_comp {N : Submodule (MonoidAlgebra ℂ G)
    (MonoidAlgebra ℂ G)} (hN : IsSimpleModule (MonoidAlgebra ℂ G) N) :
    ∃ N' : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G),
      IsSimpleModule (MonoidAlgebra ℂ G) N' ∧
        ∀ g : G, moduleCharacter G N' g = σ (moduleCharacter G N g) :=
  ⟨twistSubmodule σ N, isSimpleModule_twistSubmodule σ N hN,
    moduleCharacter_twistSubmodule σ N⟩

end MonoidAlgebra

/-! ### Conjugation permutes the irreducible characters -/

section IrrConj

variable {G : Type u} [Group G] [Fintype G]

namespace Irr

/-- The complex conjugate of an irreducible character is an irreducible character: `Irr.conj`
is conjugation as a self-map of `Irr G` (the engine applied to `σ = starRingEnd ℂ`).
MathComp: `conjC_Iirr` (`character.v`). -/
def conj (χ : Irr G) : Irr G where
  toClassFunction := (χ : ClassFunction G).conjC
  exists_simple' := by
    obtain ⟨N, hN, hχ⟩ := χ.exists_simple'
    obtain ⟨N', hN', hchar⟩ :=
      MonoidAlgebra.exists_isSimpleModule_moduleCharacter_comp (starRingAut (R := ℂ)) hN
    refine ⟨N', hN', ClassFunction.ext fun g => ?_⟩
    have hval : MonoidAlgebra.moduleCharacter G N g = χ g := by
      have h := congrArg (fun φ : ClassFunction G => φ g) hχ
      simpa using h.symm
    rw [ClassFunction.conjC_apply, hchar g, hval]
    rfl

@[simp]
theorem conj_apply (χ : Irr G) (g : G) : χ.conj g = starRingEnd ℂ (χ g) :=
  rfl

@[simp]
theorem coe_conj (χ : Irr G) : (χ.conj : ClassFunction G) = (χ : ClassFunction G).conjC :=
  rfl

/-- Conjugation of irreducible characters is an involution.  MathComp: `conjC_IirrK`
(`character.v`). -/
@[simp]
theorem conj_conj (χ : Irr G) : χ.conj.conj = χ :=
  ext fun g => Complex.conj_conj (χ g)

theorem conj_involutive : Function.Involutive (conj : Irr G → Irr G) :=
  conj_conj

theorem conj_injective : Function.Injective (conj : Irr G → Irr G) :=
  conj_involutive.injective

variable (G) in
/-- Conjugation as a permutation of `Irr G` ("conjugation permutes the irreducible
characters").  MathComp: `conjC_Iirr` with `conjC_IirrK` (`character.v`). -/
def conjEquiv : Equiv.Perm (Irr G) :=
  conj_involutive.toPerm

@[simp]
theorem conjEquiv_apply (χ : Irr G) : conjEquiv G χ = χ.conj :=
  rfl

/-- **Fixed points of conjugation are the real-valued irreducible characters**: the form in
which PF (1.1) (`odd_eq_conj_irr1`: in a group of odd order the principal character is the
only real irreducible character) is stated.  MathComp: the `cfConjC_eq`-style rewriting
underlying `odd_eq_conj_irr1` (`PFsection1.v`). -/
theorem conj_eq_self_iff {χ : Irr G} : χ.conj = χ ↔ ∀ g : G, ∃ r : ℝ, χ g = r := by
  constructor
  · intro h g
    have hg := congrArg (fun ψ : Irr G => ψ g) h
    simp only [conj_apply] at hg
    exact Complex.conj_eq_iff_real.mp hg
  · intro h
    refine ext fun g => ?_
    obtain ⟨r, hr⟩ := h g
    rw [conj_apply, hr, Complex.conj_ofReal]

/-- The trivial character is conjugation-fixed (sanity check; the nontrivial half of
PF (1.1) is that in odd-order groups it is the *only* fixed point). -/
@[simp]
theorem conj_one : (Irr.one : Irr G).conj = Irr.one :=
  conj_eq_self_iff.mpr fun g => ⟨1, by rw [one_apply, Complex.ofReal_one]⟩

end Irr

end IrrConj

/-! ### A ring automorphism of `ℂ` raising `n`-th roots of unity to a coprime power -/

section RingEquivPow

/-- For `u` coprime to `n ≠ 0`, there is a ring automorphism of `ℂ` sending every `n`-th
root of unity `z` to `z ^ u`: the Galois automorphism of the cyclotomic subfield `ℚ(ζₙ) ⊆ ℂ`
determined by `u` (`IsCyclotomicExtension.autEquivPow`), extended to all of `ℂ` along a
transcendence basis (`IsAlgClosure.equivOfEquiv`).  MathComp: over `algC` this is the
`Qn_aut_exists`-style automorphism used by `cfAut` in Peterfalvi (1.9); over `ℂ` the
transcendence-basis extension supplies the last step. -/
theorem Complex.exists_ringEquiv_pow_of_coprime {n u : ℕ} (hn : n ≠ 0) (hu : u.Coprime n) :
    ∃ σ : ℂ ≃+* ℂ, ∀ z : ℂ, z ^ n = 1 → σ z = z ^ u := by
  haveI : NeZero n := ⟨hn⟩
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζdef
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn
  -- the cyclotomic subfield `ℚ(ζ) = ℚ[ζ] ⊆ ℂ`
  set L : Subalgebra ℚ ℂ := Algebra.adjoin ℚ ({ζ} : Set ℂ) with hLdef
  haveI : IsCyclotomicExtension {n} ℚ L := hζ.adjoin_isCyclotomicExtension ℚ
  set ζL : L := ⟨ζ, Algebra.subset_adjoin (Set.mem_singleton ζ)⟩ with hζLdef
  have hζL : IsPrimitiveRoot ζL n := by
    apply IsPrimitiveRoot.of_map_of_injective (f := L.val)
    · exact hζ
    · exact Subtype.val_injective
  -- the Galois automorphism `ζ ↦ ζ ^ u` of `ℚ(ζ)`
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hn)
  set t : (ZMod n)ˣ := ZMod.unitOfCoprime u hu with htdef
  set σ₀ : L ≃ₐ[ℚ] L := (IsCyclotomicExtension.autEquivPow L hirr).symm t with hσ₀def
  have hσ₀ζ : σ₀ ζL = ζL ^ u := by
    set z₀ : L := IsCyclotomicExtension.zeta n ℚ L with hz₀def
    have hz₀ : IsPrimitiveRoot z₀ n := IsCyclotomicExtension.zeta_spec n ℚ L
    have hpow : hz₀.autToPow ℚ σ₀ = t := by
      have happ : IsCyclotomicExtension.autEquivPow L hirr σ₀ = hz₀.autToPow ℚ σ₀ := rfl
      rw [← happ, hσ₀def, MulEquiv.apply_symm_apply]
    have hspec : z₀ ^ ((t : ZMod n)).val = σ₀ z₀ := by
      rw [← hpow]
      exact IsPrimitiveRoot.autToPow_spec ℚ hz₀ σ₀
    have hzmod : ∀ {i j : ℕ}, i ≡ j [MOD n] → z₀ ^ i = z₀ ^ j := by
      have hz1 : z₀ ^ n = 1 := hz₀.pow_eq_one
      have hmod : ∀ i : ℕ, z₀ ^ i = z₀ ^ (i % n) := by
        intro i
        conv_lhs => rw [← Nat.div_add_mod i n]
        rw [pow_add, pow_mul, hz1, one_pow, one_mul]
      intro i j hij
      have hij' : i % n = j % n := hij
      rw [hmod i, hmod j, hij']
    obtain ⟨a, -, ha⟩ := hz₀.eq_pow_of_pow_eq_one hζL.pow_eq_one
    rw [← ha, map_pow, ← hspec, ← pow_mul, ← pow_mul]
    apply hzmod
    have hval : ((t : ZMod n)).val = u % n := by
      rw [htdef, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    rw [hval, mul_comm a u]
    exact (Nat.mod_modEq u n).mul_right a
  -- extend `σ₀` to `ℂ` along a transcendence basis
  haveI : FaithfulSMul L ℂ :=
    (faithfulSMul_iff_algebraMap_injective L ℂ).mpr fun x y hxy =>
      Subtype.val_injective hxy
  obtain ⟨T, hT⟩ := exists_isTranscendenceBasis (↥L) (A := ℂ)
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hT
  set A : Subalgebra (↥L) ℂ := Algebra.adjoin (↥L) (Set.range ((↑) : T → ℂ)) with hAdef
  set e : A ≃+* A :=
    (hT.1.aevalEquiv.symm.toRingEquiv.trans
      ((MvPolynomial.mapEquiv _ σ₀.toRingEquiv).trans hT.1.aevalEquiv.toRingEquiv)) with hedef
  have he : ∀ x : L, e (algebraMap (↥L) A x) = algebraMap (↥L) A (σ₀ x) := by
    intro x
    have h1 : hT.1.aevalEquiv.symm (algebraMap (↥L) A x) = MvPolynomial.C x := by
      rw [AlgEquiv.symm_apply_eq, ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    have h2 : MvPolynomial.mapEquiv T σ₀.toRingEquiv
        (MvPolynomial.C x : MvPolynomial T (↥L)) = MvPolynomial.C (σ₀ x) := by
      rw [MvPolynomial.mapEquiv_apply, MvPolynomial.map_C]
      rfl
    have h3 : hT.1.aevalEquiv (MvPolynomial.C (σ₀ x)) = algebraMap (↥L) A (σ₀ x) := by
      rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rw [hedef]
    simp only [RingEquiv.coe_trans, Function.comp_apply, AlgEquiv.coe_ringEquiv]
    rw [h1, h2, h3]
  set σ : ℂ ≃+* ℂ := IsAlgClosure.equivOfEquiv ℂ ℂ e with hσdef
  have hσζ : σ ζ = ζ ^ u := by
    have hζcoe : algebraMap (↥L) ℂ ζL = ζ := rfl
    have htower : algebraMap (↥L) ℂ ζL = algebraMap A ℂ (algebraMap (↥L) A ζL) :=
      IsScalarTower.algebraMap_apply (↥L) A ℂ ζL
    calc σ ζ = σ (algebraMap A ℂ (algebraMap (↥L) A ζL)) := by rw [← htower, hζcoe]
      _ = algebraMap A ℂ (e (algebraMap (↥L) A ζL)) :=
          IsAlgClosure.equivOfEquiv_algebraMap ℂ ℂ e _
      _ = algebraMap A ℂ (algebraMap (↥L) A (σ₀ ζL)) := by rw [he]
      _ = algebraMap (↥L) ℂ (σ₀ ζL) := (IsScalarTower.algebraMap_apply (↥L) A ℂ _).symm
      _ = ζ ^ u := by rw [hσ₀ζ, map_pow, hζcoe]
  refine ⟨σ, fun z hz => ?_⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
  rw [map_pow, hσζ, ← pow_mul, ← pow_mul, mul_comm u i]

end RingEquivPow

/-! ### The power twist permutes the irreducible characters -/

section IrrPowTwist

variable {G : Type u} [Group G]

/-- The action of a power of `g` is the corresponding power of the action of `g`. -/
theorem MonoidAlgebra.actionEnd_pow (M : Type*) [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] (g : G) (k : ℕ) :
    actionEnd M (g ^ k) = actionEnd M g ^ k := by
  induction k with
  | zero =>
    refine LinearMap.ext fun x => ?_
    rw [pow_zero, pow_zero, actionEnd_apply, ← MonoidAlgebra.one_def, one_smul,
      Module.End.one_apply]
  | succ k ih =>
    rw [pow_succ, pow_succ, actionEnd_mul, ih]
    rfl

variable [Fintype G]

/-- **The power twist is a valuewise Galois twist**: if `τ : ℂ →+* ℂ` raises every
`Monoid.exponent G`-th root of unity to its `u`-th power, then `χ (g ^ u) = τ (χ g)` for
every irreducible character `χ`.  Direct from the eigenvalue decomposition
`Module.End.trace_eq_sum_zeta_pow_mul_natCast`: `χ (g ^ k) = ∑ j, (ζ^j)^k * m j` with the
*same* natural-number multiplicities `m j` for every `k`.  This is the bridge between the
two descriptions of MathComp's `cfAut` twist of a character (Peterfalvi (1.9) shape). -/
theorem Irr.apply_pow (χ : Irr G) {u : ℕ} (τ : ℂ →+* ℂ)
    (hτ : ∀ z : ℂ, z ^ Monoid.exponent G = 1 → τ z = z ^ u) (g : G) :
    χ (g ^ u) = τ (χ g) := by
  obtain ⟨N, hN, hχ⟩ := χ.exists_simple'
  have happ : ∀ x : G, χ x = trace ℂ N (MonoidAlgebra.actionEnd (↥N) x) := by
    intro x
    have h := congrArg (fun φ : ClassFunction G => φ x) hχ
    simpa [MonoidAlgebra.moduleCharacter_apply] using h
  have hord : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hone : MonoidAlgebra.actionEnd (↥N) (1 : G) = 1 := by
    rw [show (1 : G) = g ^ 0 from (pow_zero g).symm, MonoidAlgebra.actionEnd_pow, pow_zero]
  have hfpow : MonoidAlgebra.actionEnd (↥N) g ^ orderOf g = 1 := by
    rw [← MonoidAlgebra.actionEnd_pow, pow_orderOf_eq_one, hone]
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / orderOf g) with hζdef
  have hζ : IsPrimitiveRoot ζ (orderOf g) := Complex.isPrimitiveRoot_exp (orderOf g) hord
  obtain ⟨m, hm⟩ := Module.End.trace_eq_sum_zeta_pow_mul_natCast hord hfpow hζ
  have h1 : χ g = ∑ j ∈ range (orderOf g), ζ ^ j * (m j : ℂ) := by
    rw [happ g]
    have h := hm 1
    simpa [pow_one] using h
  have hu : χ (g ^ u) = ∑ j ∈ range (orderOf g), (ζ ^ j) ^ u * (m j : ℂ) := by
    rw [happ (g ^ u), MonoidAlgebra.actionEnd_pow]
    exact hm u
  have hroot : ∀ j, (ζ ^ j) ^ Monoid.exponent G = 1 := by
    intro j
    obtain ⟨k, hk⟩ := Monoid.order_dvd_exponent g
    have h2 : (ζ ^ j) ^ (orderOf g * k) = (ζ ^ orderOf g) ^ (j * k) := by
      rw [← pow_mul, ← pow_mul, mul_left_comm j (orderOf g) k]
    rw [hk, h2, hζ.pow_eq_one, one_pow]
  rw [hu, h1, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_natCast, hτ _ (hroot j)]

namespace Irr

/-- The power twist of an irreducible character by an exponent coprime to
`Monoid.exponent G` is an irreducible character: `Irr.powTwist` is the twist as a self-map
of `Irr G`.  The witness combines `Complex.exists_ringEquiv_pow_of_coprime` (a global
automorphism `σ` of `ℂ` raising exponent-order roots of unity to the `u`-th power),
`Irr.apply_pow` (identifying `g ↦ χ (g ^ u)` with `σ ∘ χ`), and the engine
`MonoidAlgebra.exists_isSimpleModule_moduleCharacter_comp`.  MathComp: `aut_Iirr`
(`character.v`).  The coprimality hypothesis is to the *exponent*, which is weaker than
coprimality to `Nat.card G` (convert with `Nat.Coprime.of_natCard_group`). -/
def powTwist (χ : Irr G) {u : ℕ} (hu : u.Coprime (Monoid.exponent G)) : Irr G where
  toClassFunction := (χ : ClassFunction G).powTwist u
  exists_simple' := by
    have hn : Monoid.exponent G ≠ 0 := Monoid.exponent_ne_zero_of_finite
    obtain ⟨σ, hσ⟩ := Complex.exists_ringEquiv_pow_of_coprime hn hu
    obtain ⟨N, hN, hχ⟩ := χ.exists_simple'
    obtain ⟨N', hN', hchar⟩ := MonoidAlgebra.exists_isSimpleModule_moduleCharacter_comp σ hN
    refine ⟨N', hN', ClassFunction.ext fun g => ?_⟩
    have hval : MonoidAlgebra.moduleCharacter G N g = χ g := by
      have h := congrArg (fun φ : ClassFunction G => φ g) hχ
      simpa using h.symm
    rw [ClassFunction.powTwist_apply, hchar g, hval, Irr.coe_apply]
    exact χ.apply_pow (σ : ℂ →+* ℂ) hσ g

@[simp]
theorem powTwist_apply (χ : Irr G) {u : ℕ} (hu : u.Coprime (Monoid.exponent G)) (g : G) :
    χ.powTwist hu g = χ (g ^ u) :=
  rfl

@[simp]
theorem coe_powTwist (χ : Irr G) {u : ℕ} (hu : u.Coprime (Monoid.exponent G)) :
    (χ.powTwist hu : ClassFunction G) = (χ : ClassFunction G).powTwist u :=
  rfl

/-- Twists by mutually inverse exponents cancel. -/
theorem powTwist_powTwist {u u' : ℕ} (hu : u.Coprime (Monoid.exponent G))
    (hu' : u'.Coprime (Monoid.exponent G)) (h : ∀ g : G, (g ^ u') ^ u = g) (χ : Irr G) :
    (χ.powTwist hu).powTwist hu' = χ :=
  ext fun g => by rw [powTwist_apply, powTwist_apply, h g]

/-- **The power twist permutes the irreducible characters**: for `u` coprime to the
exponent, `χ ↦ χ.powTwist hu` is a bijection of `Irr G` (the inverse is the twist by a
modular inverse of `u`).  MathComp: `aut_Iirr` is a permutation of `Iirr` (`character.v`). -/
theorem powTwist_bijective {u : ℕ} (hu : u.Coprime (Monoid.exponent G)) :
    Function.Bijective fun χ : Irr G => χ.powTwist hu := by
  obtain ⟨u', hu', h1, h2⟩ := Group.exists_pow_pow_eq_of_coprime_exponent (G := G) hu
  exact Function.bijective_iff_has_inverse.mpr
    ⟨fun χ => χ.powTwist hu', fun χ => powTwist_powTwist hu hu' h2 χ,
      fun χ => powTwist_powTwist hu' hu h1 χ⟩

end Irr

end IrrPowTwist
