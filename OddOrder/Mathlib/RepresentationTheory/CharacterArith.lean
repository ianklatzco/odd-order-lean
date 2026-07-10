/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import OddOrder.Mathlib.RepresentationTheory.ClassFunction

/-!
# Arithmetic character theory: the ring of class functions, the character predicate, degrees

This file is Task 1 of the M2 character-theory plan: it builds the commutative ring
structure on `ClassFunction G` (MathComp `cfun_ring`), the trivial character `Irr.one`
(MathComp `cfun1` / `irr1`), the predicate `ClassFunction.IsChar` singling out class functions
that are ℕ-combinations of irreducible characters (MathComp `character`, `is_char`), and basic
facts about degrees `χ 1` (MathComp `irr1_deg`, `irr1_gt0`) culminating in the sum-of-squares
identity `∑ χ, (χ 1)^2 = #G` (MathComp `sum_irr1_sq`-shaped; the exact MathComp name for this
corollary of the second orthogonality relation was not confirmed against a Coq checkout).

## Main definitions

* `ClassFunction.instCommRing`, `ClassFunction.instAlgebra`: the pointwise ring structure
  (`mul_apply`, `one_apply`, `pow_apply`) and the induced `ℂ`-algebra structure.
* `Irr.one`: the trivial irreducible character, the constant function `1`
  (`Irr.one_apply`).
* `ClassFunction.IsChar`: `φ` is an ℕ-combination of irreducible characters.
* `MonoidAlgebra.moduleCharacter_one`: `moduleCharacter G M 1 = finrank ℂ M` (any
  finite-dimensional `ℂ[G]`-module `M`).

## Main results

* `ClassFunction.isChar_moduleCharacter`: every finite-dimensional `ℂ[G]`-module's character
  is a character in the `IsChar` sense — the semisimple-decomposition direction of the
  MathComp equivalence between `character` and "trace of a representation". This is the
  direction downstream tasks (restriction/induction, Task 2) consume.
* `ClassFunction.IsChar.add`, `ClassFunction.IsChar.cfInner_mem_nat`.
* `Irr.exists_degree`: `∃ d : ℕ, 0 < d ∧ χ 1 = d`.
* `Irr.sum_sq_degree`: `∑ χ : Irr G, (χ 1)^2 = Nat.card G`.

## Design notes

* **Ring instances placed here, not in `ClassFunction.lean`.** `ClassFunction.lean` (Task 9)
  is an already-reviewed foundation file; the pointwise `Mul`/`One`/`CommRing`/`Algebra ℂ`
  instances on `ClassFunction G` are added in *this* file instead, since Lean's instance
  resolution does not care which file declares an instance, only that it is imported. Any
  file needing the ring structure already needs `IsChar` or `Irr.one` from this file (per the
  M2 plan's task dependency graph: Task 2 ← Task 1), so nothing downstream loses access.
* **`IsChar` ↔ module-character equivalence: forward direction only.** The M2 plan allows
  scoping down to `IsChar (moduleCharacter G M)` (semisimple decomposition: every
  finite-dimensional `ℂ[G]`-module's character is an ℕ-combination of `Irr G`) if the full
  iff fights universes/effort past budget. That forward direction is what is proved here
  (`ClassFunction.isChar_moduleCharacter`), via `IsSemisimpleModule (MonoidAlgebra ℂ G) M`
  (Maschke, no finiteness side conditions beyond `[Finite G]` and `NeZero (Nat.card G : ℂ)`)
  and strong induction on `finrank ℂ M`: extract a simple submodule (`exists_simple_submodule`),
  take a complement (`ComplementedLattice.exists_isCompl`), and add characters across the
  complementary decomposition (`MonoidAlgebra.moduleCharacter_add_of_isCompl`, proved via
  `Submodule.prodEquivOfIsCompl` and `LinearMap.trace_prodMap'`). The converse
  (`IsChar φ → ∃ module`, and `IsChar.mul` via tensor products) is a **documented omission**;
  see the task report for the reason and the (comparatively easy) sketch of what it would
  take.
-/

noncomputable section

open Finset LinearMap Module
open scoped ClassFunction

universe u v

variable {G : Type u} [Group G]

/-! ### The commutative ring of class functions

`cfun_ring` in MathComp: class functions form a commutative ring under pointwise
multiplication, with multiplicative unit the constant function `1`. -/

namespace ClassFunction

instance : Mul (ClassFunction G) :=
  ⟨fun φ ψ => ⟨fun g => φ g * ψ g, fun g h => by simp⟩⟩

instance : One (ClassFunction G) :=
  ⟨⟨fun _ => 1, fun _ _ => rfl⟩⟩

instance : Pow (ClassFunction G) ℕ :=
  ⟨fun φ n => ⟨fun g => φ g ^ n, fun g h => by simp⟩⟩

instance : NatCast (ClassFunction G) :=
  ⟨fun n => ⟨fun _ => (n : ℂ), fun _ _ => rfl⟩⟩

instance : IntCast (ClassFunction G) :=
  ⟨fun n => ⟨fun _ => (n : ℂ), fun _ _ => rfl⟩⟩

@[simp] theorem coe_mul (φ ψ : ClassFunction G) : ⇑(φ * ψ) = fun g => φ g * ψ g := rfl
@[simp] theorem coe_one : ⇑(1 : ClassFunction G) = fun _ : G => (1 : ℂ) := rfl
@[simp] theorem coe_pow (φ : ClassFunction G) (n : ℕ) : ⇑(φ ^ n) = fun g => φ g ^ n := rfl
@[simp] theorem coe_natCast (n : ℕ) : ⇑(n : ClassFunction G) = fun _ : G => (n : ℂ) := rfl
@[simp] theorem coe_intCast (n : ℤ) : ⇑(n : ClassFunction G) = fun _ : G => (n : ℂ) := rfl

/-- Pointwise product of class functions.  MathComp: `cfunM`/`cfun_ring`. -/
@[simp]
theorem mul_apply (φ ψ : ClassFunction G) (g : G) : (φ * ψ) g = φ g * ψ g := rfl

/-- The multiplicative unit of `ClassFunction G` is the constant function `1`.
MathComp: `cfun_ring`. -/
@[simp]
theorem one_apply (g : G) : (1 : ClassFunction G) g = 1 := rfl

@[simp]
theorem pow_apply (φ : ClassFunction G) (n : ℕ) (g : G) : (φ ^ n) g = φ g ^ n := rfl

instance instCommRing : CommRing (ClassFunction G) :=
  DFunLike.coe_injective.commRing (⇑) coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_smul
    coe_smul coe_pow coe_natCast coe_intCast

instance instAlgebra : Algebra ℂ (ClassFunction G) :=
  Algebra.ofModule
    (fun r φ ψ => by ext g; simp [mul_apply, smul_apply, smul_eq_mul, mul_assoc])
    (fun r φ ψ => by ext g; simp [mul_apply, smul_apply, smul_eq_mul, mul_left_comm])

end ClassFunction

/-! ### The trivial character

The trivial representation of `G` on `ℂ` is irreducible (a 1-dimensional vector space has no
proper nonzero subspaces), so it contributes a distinguished element of `Irr G`: the constant
function `1`.  MathComp: `cfun1`/`irr1`. -/

section IrrOne

variable {G : Type u} [Group G]

/-- The trivial representation of any group on `ℂ` is irreducible: its subrepresentations
are in particular `ℂ`-subspaces of the one-dimensional space `ℂ`, hence `⊥` or `⊤`. -/
instance Representation.instIsIrreducibleTrivial :
    (Representation.trivial ℂ G ℂ).IsIrreducible where
  exists_pair_ne := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    have h2 : (⊥ : Submodule ℂ ℂ) = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h2
  eq_bot_or_eq_top σ := by
    rcases eq_bot_or_eq_top σ.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

/-- The character of the trivial representation is the constant function `1`. -/
theorem Representation.trivial_character (g : G) :
    (Representation.trivial ℂ G ℂ).character g = 1 := by
  have h1 : (Representation.trivial ℂ G ℂ) g = LinearMap.id :=
    LinearMap.ext (Representation.trivial_apply ℂ g)
  rw [Representation.character, h1, trace_id, CommSemiring.finrank_self ℂ, Nat.cast_one]

/-- The trivial irreducible character of `G`: the constant function `1`.
MathComp: `cfun1`/`irr1`. -/
noncomputable def Irr.one [Fintype G] : Irr G :=
  (Representation.exists_irr_classFunction_eq (Representation.trivial ℂ G ℂ)).choose

/-- The defining property of `Irr.one`: its class function is the character of the trivial
representation. -/
theorem Irr.one_spec [Fintype G] :
    (Irr.one : Irr G).toClassFunction = (Representation.trivial ℂ G ℂ).classFunction :=
  (Representation.exists_irr_classFunction_eq (Representation.trivial ℂ G ℂ)).choose_spec

@[simp]
theorem Irr.one_apply [Fintype G] (g : G) : (Irr.one : Irr G) g = 1 := by
  have h := congrArg (fun φ : ClassFunction G => φ g) Irr.one_spec
  simpa [Representation.classFunction_apply, Representation.trivial_character] using h

end IrrOne

/-! ### Characters of modules, and the sum of characters of a complementary pair

`moduleCharacter_one` computes the character at the identity as the module's dimension
(MathComp: `cfRepr1`/`irr1_deg` restated at the module level).  `moduleCharacter_add_of_isCompl`
is the additivity of the character across a complementary pair of `ℂ[G]`-submodules; it is the
engine of the semisimple-decomposition argument for `IsChar`. -/

section ModuleCharacterArith

open MonoidAlgebra

variable {G : Type u} [Group G]

theorem MonoidAlgebra.moduleCharacter_one {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M]
    [FiniteDimensional ℂ M] : moduleCharacter G M 1 = Module.finrank ℂ M := by
  rw [moduleCharacter_eq_ofModule'_character]
  exact Representation.char_one _

/-- Any `MonoidAlgebra ℂ G`-submodule of a finite-dimensional `ℂ`-vector space is itself
finite-dimensional over `ℂ`: it is, in particular, a `ℂ`-submodule (via `IsScalarTower`), and
submodules of finite-dimensional spaces are finite-dimensional. Generalizes the
`ClassFunction.lean` instance for submodules of the regular module to an arbitrary
finite-dimensional module. -/
instance MonoidAlgebra.instFiniteDimensionalSubmodule {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M]
    [FiniteDimensional ℂ M] (N : Submodule (MonoidAlgebra ℂ G) M) : FiniteDimensional ℂ N :=
  FiniteDimensional.of_injective ((Submodule.subtype N).restrictScalars ℂ) N.injective_subtype

variable {M : Type v} [AddCommGroup M] [Module ℂ M] [Module (MonoidAlgebra ℂ G) M]
  [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] [FiniteDimensional ℂ M]

/-- The character of a finite-dimensional `ℂ[G]`-module is additive across a complementary
pair of submodules: `moduleCharacter G M = moduleCharacter G p + moduleCharacter G q` when
`p, q` are complementary. Proved by transporting the trace of `g`'s action along
`Submodule.prodEquivOfIsCompl` and applying `LinearMap.trace_prodMap'`. -/
theorem MonoidAlgebra.moduleCharacter_add_of_isCompl
    {p q : Submodule (MonoidAlgebra ℂ G) M} (h : IsCompl p q) (g : G) :
    moduleCharacter G M g = moduleCharacter G p g + moduleCharacter G q g := by
  set Φ := Submodule.prodEquivOfIsCompl p q h with hΦ
  have hconj : (Φ.restrictScalars ℂ).conj
      (LinearMap.prodMap (actionEnd (↥p) g) (actionEnd (↥q) g)) = actionEnd M g := by
    refine LinearMap.ext fun x => ?_
    rw [LinearEquiv.conj_apply_apply]
    have hbridge : (Φ.restrictScalars ℂ)
        (LinearMap.prodMap (actionEnd (↥p) g) (actionEnd (↥q) g) ((Φ.restrictScalars ℂ).symm x))
        = Φ (LinearMap.prodMap (actionEnd (↥p) g) (actionEnd (↥q) g) (Φ.symm x)) := rfl
    rw [hbridge, actionEnd_apply]
    conv_rhs => rw [(Φ.apply_symm_apply x).symm]
    obtain ⟨a, b⟩ := Φ.symm x
    rw [LinearMap.prodMap_apply, actionEnd_apply, actionEnd_apply, ← Prod.smul_mk, map_smul]
  have htrace := LinearMap.trace_conj' (R := ℂ)
    (LinearMap.prodMap (actionEnd (↥p) g) (actionEnd (↥q) g)) (Φ.restrictScalars ℂ)
  rw [hconj] at htrace
  rw [MonoidAlgebra.moduleCharacter_apply, htrace,
    LinearMap.trace_prodMap' (actionEnd (↥p) g) (actionEnd (↥q) g)]
  rfl

end ModuleCharacterArith

/-! ### The character predicate `IsChar` -/

section IsChar

variable {G : Type u} [Group G] [Fintype G]

/-- A class function is a **character** if it is an ℕ-combination of the irreducible
characters.  MathComp: `character`, `is_char`. -/
def ClassFunction.IsChar (φ : ClassFunction G) : Prop :=
  ∃ c : Irr G → ℕ, φ = ∑ χ : Irr G, (c χ : ℂ) • (χ : ClassFunction G)

/-- Every finite-dimensional `ℂ[G]`-module's character is a character in the `IsChar` sense.
This is the semisimple-decomposition direction of the `IsChar`/module equivalence (the
direction later tasks consume); see the module docstring for what is deliberately omitted. -/
theorem ClassFunction.isChar_moduleCharacter :
    ∀ (n : ℕ) (M : Type v) [AddCommGroup M] [Module ℂ M] [Module (MonoidAlgebra ℂ G) M]
      [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] [FiniteDimensional ℂ M],
      Module.finrank ℂ M = n → (MonoidAlgebra.moduleCharacter G M).IsChar := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M _ _ _ _ _ hn
    classical
    haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
    rcases eq_or_ne n 0 with rfl | hn0
    · refine ⟨fun _ => 0, ?_⟩
      haveI : Subsingleton M := Module.finrank_zero_iff.mp hn
      ext g
      have hz : MonoidAlgebra.actionEnd M g = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
      simp [MonoidAlgebra.moduleCharacter_apply, hz]
    · haveI : Nontrivial M := Module.nontrivial_of_finrank_pos (R := ℂ)
        (hn ▸ Nat.pos_of_ne_zero hn0)
      obtain ⟨N, hN⟩ := IsSemisimpleModule.exists_simple_submodule (MonoidAlgebra ℂ G) M
      haveI := hN
      haveI : Nontrivial (↥N) := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) (↥N)
      obtain ⟨Q, hQ⟩ := ComplementedLattice.exists_isCompl N
      have hNQ : Module.finrank ℂ (↥N) + Module.finrank ℂ (↥Q) = Module.finrank ℂ M := by
        rw [← Module.finrank_prod (R := ℂ) (M := ↥N) (M' := ↥Q),
          ((Submodule.prodEquivOfIsCompl N Q hQ).restrictScalars ℂ).finrank_eq]
      have hNpos : 0 < Module.finrank ℂ (↥N) := Module.finrank_pos
      have hQlt : Module.finrank ℂ (↥Q) < n := by omega
      obtain ⟨cQ, hcQ⟩ := ih (Module.finrank ℂ (↥Q)) hQlt (↥Q) rfl
      haveI hirrN : (Representation.ofModule' (k := ℂ) (G := G) (↥N)).IsIrreducible :=
        MonoidAlgebra.isIrreducible_ofModule' (↥N) hN
      obtain ⟨χN, hχN⟩ := Representation.exists_irr_classFunction_eq
        (Representation.ofModule' (k := ℂ) (G := G) (↥N))
      have hχN' : (χN : ClassFunction G) = MonoidAlgebra.moduleCharacter G (↥N) := by
        ext g
        have := congrArg (fun φ : ClassFunction G => φ g) hχN
        simpa [Representation.classFunction_apply,
          MonoidAlgebra.moduleCharacter_eq_ofModule'_character] using this
      have hsum : MonoidAlgebra.moduleCharacter G M
          = MonoidAlgebra.moduleCharacter G (↥N) + MonoidAlgebra.moduleCharacter G (↥Q) :=
        ClassFunction.ext fun g => MonoidAlgebra.moduleCharacter_add_of_isCompl hQ g
      have hone : (χN : ClassFunction G)
          = ∑ χ : Irr G, if χ = χN then (1 : ℂ) • (χ : ClassFunction G) else (0 : ClassFunction G)
          := by
        rw [Finset.sum_ite_eq' Finset.univ χN fun χ => (1 : ℂ) • (χ : ClassFunction G)]
        simp
      refine ⟨fun χ => cQ χ + (if χ = χN then 1 else 0), ?_⟩
      calc MonoidAlgebra.moduleCharacter G M
          = MonoidAlgebra.moduleCharacter G (↥N) + MonoidAlgebra.moduleCharacter G (↥Q) := hsum
        _ = (χN : ClassFunction G) + ∑ χ : Irr G, (cQ χ : ℂ) • (χ : ClassFunction G) := by
            rw [hχN', hcQ]
        _ = (∑ χ : Irr G,
                if χ = χN then (1 : ℂ) • (χ : ClassFunction G) else (0 : ClassFunction G))
              + ∑ χ : Irr G, (cQ χ : ℂ) • (χ : ClassFunction G) := by rw [hone]
        _ = ∑ χ : Irr G, ((cQ χ : ℂ) • (χ : ClassFunction G)
              + if χ = χN then (1 : ℂ) • (χ : ClassFunction G) else (0 : ClassFunction G)) := by
            rw [add_comm, ← Finset.sum_add_distrib]
        _ = ∑ χ : Irr G, ((cQ χ + if χ = χN then 1 else 0 : ℕ) : ℂ) • (χ : ClassFunction G) := by
            refine Finset.sum_congr rfl fun χ _ => ?_
            by_cases hχ : χ = χN
            · subst hχ; simp [add_smul]
            · simp [hχ]

/-- Applied with `n := finrank ℂ M`, without threading the induction variable explicitly. -/
theorem ClassFunction.isChar_moduleCharacter' {M : Type v} [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M]
    [FiniteDimensional ℂ M] : (MonoidAlgebra.moduleCharacter G M).IsChar :=
  ClassFunction.isChar_moduleCharacter (Module.finrank ℂ M) M rfl

theorem ClassFunction.IsChar.add {φ ψ : ClassFunction G} (hφ : φ.IsChar) (hψ : ψ.IsChar) :
    (φ + ψ).IsChar := by
  obtain ⟨cφ, hcφ⟩ := hφ
  obtain ⟨cψ, hcψ⟩ := hψ
  refine ⟨fun χ => cφ χ + cψ χ, ?_⟩
  rw [hcφ, hcψ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Nat.cast_add, add_smul]

/-- The multiplicity of an irreducible character `ψ` in a character `φ` is a natural number
(realized as the inner product `⟪φ, ψ⟫`). MathComp: (character multiplicities are natural
numbers, underlying `cfdot_char_irr`-style lemmas). -/
theorem ClassFunction.IsChar.cfInner_mem_nat {φ : ClassFunction G} (hφ : φ.IsChar) (ψ : Irr G) :
    ∃ n : ℕ, ⟪φ, (ψ : ClassFunction G)⟫_[G] = n := by
  classical
  obtain ⟨c, hc⟩ := hφ
  refine ⟨c ψ, ?_⟩
  rw [hc, ClassFunction.cfInner_sum_left]
  have hterm : ∀ χ : Irr G, ⟪(c χ : ℂ) • (χ : ClassFunction G), (ψ : ClassFunction G)⟫_[G]
      = if χ = ψ then (c χ : ℂ) else 0 := by
    intro χ
    rw [ClassFunction.cfInner_smul_left, Irr.cfInner_eq, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl fun χ _ => hterm χ,
    Finset.sum_ite_eq' Finset.univ ψ fun χ => (c χ : ℂ)]
  simp

end IsChar

/-! ### Degrees -/

section Degree

variable {G : Type u} [Group G] [Fintype G]

/-- The degree `χ 1` of an irreducible character is a positive natural number: the dimension
of a witnessing simple module. MathComp: `irr1_deg`, `irr1_gt0`. -/
theorem Irr.exists_degree (χ : Irr G) : ∃ d : ℕ, 0 < d ∧ χ 1 = d := by
  obtain ⟨N, hN, hχ⟩ := χ.exists_simple'
  haveI := hN
  haveI : Nontrivial (↥N) := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) (↥N)
  refine ⟨Module.finrank ℂ (↥N), Module.finrank_pos, ?_⟩
  have h1 := congrArg (fun φ : ClassFunction G => φ 1) hχ
  simpa [MonoidAlgebra.moduleCharacter_one] using h1

/-- **Sum of squares of degrees**: `∑ χ : Irr G, (χ 1)^2 = |G|`, evaluating the second
orthogonality relation at `g = h = 1`. -/
theorem Irr.sum_sq_degree : ∑ χ : Irr G, (χ 1 : ℂ) ^ 2 = (Nat.card G : ℂ) := by
  classical
  have h := Irr.second_orthogonality (G := G) 1 1
  rw [if_pos (IsConj.refl 1)] at h
  have hcent : Subgroup.centralizer ({1} : Set G) = ⊤ := by
    ext x
    simp [Subgroup.mem_centralizer_iff]
  rw [hcent, Subgroup.card_top] at h
  rw [← h]
  refine Finset.sum_congr rfl fun χ _ => ?_
  obtain ⟨d, _, hd⟩ := χ.exists_degree
  rw [hd, sq, map_natCast]

end Degree
