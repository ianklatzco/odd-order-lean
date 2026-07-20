/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import OddOrder.Mathlib.RepresentationTheory.ClassFunction
import OddOrder.Mathlib.RepresentationTheory.ClassSum
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.FractionRing

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
* `ClassFunction.IsChar.add`, `ClassFunction.IsChar.natCast_smul`,
  `ClassFunction.IsChar.cfInner_mem_nat`.
* `Irr.exists_degree`: `∃ d : ℕ, 0 < d ∧ χ 1 = d`.
* `Irr.sum_sq_degree`: `∑ χ : Irr G, (χ 1)^2 = Nat.card G`.
* `Irr.ker` (with `Irr.mem_ker_iff`, `Irr.eq_one_of_ker_eq_top`): character kernels, promoted
  from `Burnside.lean` (M3 Task 4, per the M2 deferred-consolidation list) together with the
  eigen-projection kit and the scalar-action lemma
  (`Module.End.eq_smul_one_of_trace_eq_mul_finrank`) they rest on. MathComp: `cfker`.
* `Irr.exists_ne_one_apply_ne`: a nonidentity element is separated from `1` by some
  nonprincipal irreducible character (the column argument at `(g, 1)`).

## Design notes

* **Ring instances placed here, not in `ClassFunction.lean`.** `ClassFunction.lean` (Task 9)
  is an already-reviewed foundation file; the pointwise `Mul`/`One`/`CommRing`/`Algebra ℂ`
  instances on `ClassFunction G` are added in *this* file instead, since Lean's instance
  resolution does not care which file declares an instance, only that it is imported. Any
  file needing the ring structure already needs `IsChar` or `Irr.one` from this file (per the
  M2 plan's task dependency graph: Task 2 ← Task 1), so nothing downstream loses access.
* **`IsChar` ↔ module-character equivalence: forward direction only.** What is proved here
  is the forward direction `IsChar (moduleCharacter G M)` (semisimple decomposition: every
  finite-dimensional `ℂ[G]`-module's character is an ℕ-combination of `Irr G`); the converse
  is a recorded deferral — see the M2 results table in `docs/superpowers/plans/STATUS.md`
  (Task 1 row: "deferred per plan clauses: `IsChar.mul`, module-equivalence converse") and
  the deferral annotation on Task 1 in the M2 plan itself. The forward direction is proved
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

/-- The class function of the trivial irreducible character is the ring unit of
`ClassFunction G` (the constant function `1`). -/
@[simp]
theorem Irr.coe_one [Fintype G] : ((Irr.one : Irr G) : ClassFunction G) = 1 :=
  ClassFunction.ext fun g => by rw [Irr.coe_apply, Irr.one_apply, ClassFunction.one_apply]

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

/-- A `ℕ`-multiple of a character is a character (with the scalar spelled as the `ℂ`-cast,
matching the `IsChar` convention). -/
theorem ClassFunction.IsChar.natCast_smul {φ : ClassFunction G} (hφ : φ.IsChar) (n : ℕ) :
    ((n : ℂ) • φ).IsChar := by
  obtain ⟨c, hc⟩ := hφ
  refine ⟨fun χ => n * c χ, ?_⟩
  rw [hc, Finset.smul_sum]
  exact Finset.sum_congr rfl fun χ _ => by rw [smul_smul, ← Nat.cast_mul]

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

/-! ### Algebraic integrality of character values (Task 4, item 1)

`χ(g)` is an algebraic integer over `ℤ`: it is, via
`Module.End.trace_eq_sum_zeta_pow_mul_natCast` (refactored out of
`Module.End.trace_pow_pred_eq_star_trace` in `ClassFunction.lean` for exactly this reuse), a
`ℕ`-weighted sum of `orderOf g`-th roots of unity, and each of those is integral (root of
`X ^ n - 1`) while sums/products of integral elements are integral.  MathComp: `χ(g)` is an
algebraic integer (`Aint_char`-shaped, exact name unconfirmed). -/

section IsIntegralApply

variable {G : Type u} [Group G] [Fintype G]

/-- The value of an irreducible character at any group element is an algebraic integer. -/
theorem Irr.isIntegral_apply (χ : Irr G) (g : G) : IsIntegral ℤ (χ g) := by
  obtain ⟨N, hN, hχ⟩ := χ.exists_simple'
  haveI := hN
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hpow1 : (MonoidAlgebra.actionEnd (↥N) g) ^ orderOf g = 1 := by
    rw [← MonoidAlgebra.ofModule'_eq_actionEnd, ← map_pow, pow_orderOf_eq_one, map_one]
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / orderOf g) with hζdef
  have hζ : IsPrimitiveRoot ζ (orderOf g) := Complex.isPrimitiveRoot_exp (orderOf g) hn
  obtain ⟨m, hm⟩ := Module.End.trace_eq_sum_zeta_pow_mul_natCast hn hpow1 hζ
  have hχg : χ g = trace ℂ (↥N) (MonoidAlgebra.actionEnd (↥N) g) := by
    have := congrArg (fun φ : ClassFunction G => φ g) hχ
    simpa [MonoidAlgebra.moduleCharacter_apply] using this
  have h1 := hm 1
  simp only [pow_one] at h1
  rw [hχg, h1]
  have hζI : IsIntegral ℤ ζ := by
    refine ⟨Polynomial.X ^ orderOf g - Polynomial.C (1 : ℤ),
      Polynomial.monic_X_pow_sub_C 1 hn, ?_⟩
    simp [hζ.pow_eq_one]
  exact IsIntegral.sum _ fun j _ => IsIntegral.mul (hζI.pow j) (isIntegral_natCast _)

end IsIntegralApply

/-! ### The central character `ω_χ` (Task 4, item 2)

For `χ : Irr G` and a conjugacy class `c`, Schur's lemma shows that the class sum
`classSum c` (central in `ℂ[G]`, hence `ℂ[G]`-linear as a left-multiplication map) acts on
any simple module witnessing `χ` by a single scalar `ω_χ(c)`, the **central character**. The
scalar-extraction map, for a fixed simple submodule `N`, is packaged as an algebra
homomorphism `MonoidAlgebra.centralScalarHom N : center →ₐ[ℂ] ℂ`; the two facts consumed
downstream (the closed formula `Irr.omega_eq` and the structure-constant identity
`Irr.omega_mul`) both come from generic `AlgHom`/`AlgEquiv` API (`map_mul`, `map_sum`, and a
trace computation) rather than bespoke uniqueness arguments. MathComp: the central character
`ω_χ` (`gring`-mode material, exact name unconfirmed). -/

section CentralAction

variable {G : Type u} [Group G]

/-- Left multiplication by a central element of the group algebra, restricted to a submodule
`N` of the regular module: `ℂ[G]`-linear precisely because `z` is central. -/
def MonoidAlgebra.centralAction {z : MonoidAlgebra ℂ G}
    (hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G))
    (N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    N →ₗ[MonoidAlgebra ℂ G] N where
  toFun x := ⟨z * (x : MonoidAlgebra ℂ G), by
    have h := N.smul_mem z x.2
    rwa [smul_eq_mul] at h⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' a x := Subtype.ext (by
    change z * (a * (x : MonoidAlgebra ℂ G)) = a * (z * (x : MonoidAlgebra ℂ G))
    rw [← mul_assoc, ← Subalgebra.mem_center_iff.mp hz a, mul_assoc])

@[simp]
theorem MonoidAlgebra.centralAction_coe {z : MonoidAlgebra ℂ G}
    (hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G))
    (N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) (x : N) :
    (MonoidAlgebra.centralAction hz N x : MonoidAlgebra ℂ G) = z * (x : MonoidAlgebra ℂ G) :=
  rfl

/-- The `ℂ`-algebra homomorphism sending a central element of the group algebra to (left
multiplication by it, restricted to a submodule `N`): `map_one`/`map_mul`/`map_add` are
associativity/distributivity of ring multiplication. -/
noncomputable def MonoidAlgebra.centralActionAlgHom
    (N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G)) →ₐ[ℂ] Module.End (MonoidAlgebra ℂ G) N :=
  AlgHom.ofLinearMap
    { toFun := fun z => MonoidAlgebra.centralAction z.2 N
      map_add' := fun z₁ z₂ => LinearMap.ext fun x => Subtype.ext (by
        change ((z₁ : MonoidAlgebra ℂ G) + z₂) * (x : MonoidAlgebra ℂ G)
            = (z₁ : MonoidAlgebra ℂ G) * x + (z₂ : MonoidAlgebra ℂ G) * x
        rw [add_mul])
      map_smul' := fun a z => LinearMap.ext fun x => Subtype.ext (by
        change (a • (z : MonoidAlgebra ℂ G)) * (x : MonoidAlgebra ℂ G)
            = a • ((z : MonoidAlgebra ℂ G) * x)
        rw [smul_mul_assoc]) }
    (LinearMap.ext fun x => Subtype.ext (one_mul _))
    (fun z₁ z₂ => LinearMap.ext fun x => Subtype.ext (by
      change ((z₁ : MonoidAlgebra ℂ G) * z₂) * (x : MonoidAlgebra ℂ G)
          = (z₁ : MonoidAlgebra ℂ G) * ((z₂ : MonoidAlgebra ℂ G) * (x : MonoidAlgebra ℂ G))
      rw [mul_assoc]))

@[simp]
theorem MonoidAlgebra.centralActionAlgHom_apply
    (N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G))) :
    MonoidAlgebra.centralActionAlgHom N z = MonoidAlgebra.centralAction z.2 N :=
  rfl

end CentralAction

section CentralScalar

variable {G : Type u} [Group G] [Finite G]
  (N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) [IsSimpleModule (MonoidAlgebra ℂ G) N]

/-- **Schur's lemma**, packaged as an algebra isomorphism: every `ℂ[G]`-linear endomorphism
of a simple module `N` is a scalar. -/
noncomputable def MonoidAlgebra.centralScalarAlgEquiv :
    ℂ ≃ₐ[ℂ] Module.End (MonoidAlgebra ℂ G) N :=
  AlgEquiv.ofBijective (Algebra.ofId ℂ (Module.End (MonoidAlgebra ℂ G) N))
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (k := ℂ) (A := MonoidAlgebra ℂ G) (V := N))

/-- The **central character** scalar-extraction map: a `ℂ`-algebra homomorphism from the
center of the group algebra to `ℂ`, sending a central element `z` to the scalar by which it
acts on the simple module `N` (via Schur's lemma). -/
noncomputable def MonoidAlgebra.centralScalarHom :
    ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G)) →ₐ[ℂ] ℂ :=
  (MonoidAlgebra.centralScalarAlgEquiv N).symm.toAlgHom.comp
    (MonoidAlgebra.centralActionAlgHom N)

/-- The defining property of `centralScalarHom`: the scalar it produces acts on `N` exactly
as `z` does (via left multiplication). -/
theorem MonoidAlgebra.centralActionAlgHom_eq_algebraMap_centralScalarHom
    (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G))) :
    MonoidAlgebra.centralActionAlgHom N z
      = algebraMap ℂ (Module.End (MonoidAlgebra ℂ G) N)
          (MonoidAlgebra.centralScalarHom N z) := by
  change MonoidAlgebra.centralActionAlgHom N z
    = (MonoidAlgebra.centralScalarAlgEquiv N)
        ((MonoidAlgebra.centralScalarAlgEquiv N).symm (MonoidAlgebra.centralActionAlgHom N z))
  rw [AlgEquiv.apply_symm_apply]

/-- The Schur scalar for a central element `z`, viewed over `ℂ`: multiplication by `z` on `N`
is exactly scalar multiplication by `centralScalarHom N ⟨z, hz⟩`. -/
theorem MonoidAlgebra.restrictScalars_centralAction {z : MonoidAlgebra ℂ G}
    (hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) :
    LinearMap.restrictScalars ℂ (MonoidAlgebra.centralAction hz N)
      = (MonoidAlgebra.centralScalarHom N ⟨z, hz⟩) • LinearMap.id := by
  have hs : algebraMap ℂ (Module.End (MonoidAlgebra ℂ G) N)
      (MonoidAlgebra.centralScalarHom N ⟨z, hz⟩) = MonoidAlgebra.centralAction hz N :=
    (MonoidAlgebra.centralActionAlgHom_eq_algebraMap_centralScalarHom N ⟨z, hz⟩).symm.trans
      (MonoidAlgebra.centralActionAlgHom_apply N ⟨z, hz⟩)
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.restrictScalars_apply, ← hs, Algebra.algebraMap_eq_smul_one,
    LinearMap.smul_apply, Module.End.one_apply, LinearMap.smul_apply, LinearMap.id_apply]

end CentralScalar

section TraceCentralAction

variable {G : Type u} [Group G] [Fintype G]

open scoped Classical in
/-- The trace of the class-sum action on a submodule `N` is the sum of `N`'s character over
the conjugacy class `c`: the class sum is a sum of group-algebra basis elements, and left
multiplication by a basis element `single x 1` acts as `MonoidAlgebra.actionEnd N x`. -/
theorem MonoidAlgebra.trace_centralAction_classSum (c : ConjClasses G)
    (N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) [FiniteDimensional ℂ N] :
    trace ℂ N (LinearMap.restrictScalars ℂ
        (MonoidAlgebra.centralAction (MonoidAlgebra.classSum_mem_center c) N))
      = ∑ x ∈ Finset.univ.filter (· ∈ c.carrier), MonoidAlgebra.moduleCharacter G N x := by
  have hrestrict : LinearMap.restrictScalars ℂ
      (MonoidAlgebra.centralAction (MonoidAlgebra.classSum_mem_center c) N)
      = ∑ x ∈ Finset.univ.filter (· ∈ c.carrier), MonoidAlgebra.actionEnd N x := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    rw [LinearMap.restrictScalars_apply, MonoidAlgebra.centralAction_coe,
      MonoidAlgebra.classSum_eq_sum_single, Finset.sum_mul, LinearMap.sum_apply,
      AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun x _ => by
      rw [MonoidAlgebra.actionEnd_apply, Submodule.coe_smul, smul_eq_mul]
  rw [hrestrict, map_sum]
  exact Finset.sum_congr rfl fun x _ => rfl

end TraceCentralAction

section CentralCharacter

variable {G : Type u} [Group G] [Fintype G]

/-- The **central character** `ω_χ(c)`: the scalar by which the class sum `classSum c` acts
(via Schur's lemma) on a witnessing simple module for `χ`. MathComp: the central character
(`gring`-mode material, exact name unconfirmed). -/
noncomputable def Irr.omega (χ : Irr G) (c : ConjClasses G) : ℂ :=
  letI := χ.exists_simple'.choose_spec.1
  MonoidAlgebra.centralScalarHom χ.exists_simple'.choose
    ⟨MonoidAlgebra.classSum G c, MonoidAlgebra.classSum_mem_center c⟩

open scoped Classical in
/-- **Closed formula for the central character**: `ω_χ(c) = |c| * χ(c.out) / χ(1)`.
MathComp: the central character formula (`gring`-mode material, exact name unconfirmed). -/
theorem Irr.omega_eq (χ : Irr G) (c : ConjClasses G) :
    Irr.omega χ c = (Nat.card c.carrier : ℂ) * χ c.out / χ 1 := by
  classical
  set N := χ.exists_simple'.choose with hNdef
  haveI hN : IsSimpleModule (MonoidAlgebra ℂ G) N := χ.exists_simple'.choose_spec.1
  have hχ : χ.toClassFunction = MonoidAlgebra.moduleCharacter G N :=
    χ.exists_simple'.choose_spec.2
  have homega : Irr.omega χ c = MonoidAlgebra.centralScalarHom N
      ⟨MonoidAlgebra.classSum G c, MonoidAlgebra.classSum_mem_center c⟩ := rfl
  have htrace1 : trace ℂ N (LinearMap.restrictScalars ℂ
      (MonoidAlgebra.centralAction (MonoidAlgebra.classSum_mem_center c) N))
      = (MonoidAlgebra.centralScalarHom N
          ⟨MonoidAlgebra.classSum G c, MonoidAlgebra.classSum_mem_center c⟩)
          * Module.finrank ℂ N := by
    rw [MonoidAlgebra.restrictScalars_centralAction, map_smul, LinearMap.trace_id, smul_eq_mul]
  have htrace2 : trace ℂ N (LinearMap.restrictScalars ℂ
      (MonoidAlgebra.centralAction (MonoidAlgebra.classSum_mem_center c) N))
      = ∑ x ∈ Finset.univ.filter (· ∈ c.carrier), χ x := by
    rw [MonoidAlgebra.trace_centralAction_classSum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hthis := congrArg (fun φ : ClassFunction G => φ x) hχ
    simpa using hthis.symm
  have hconst : ∀ x ∈ Finset.univ.filter (· ∈ c.carrier), χ x = χ c.out := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have hcout : c.out ∈ c.carrier := ConjClasses.mem_carrier_iff_mk_eq.mpr c.out_eq
    have hxc : IsConj x c.out := ConjClasses.mk_eq_mk_iff_isConj.mp
      ((ConjClasses.mem_carrier_iff_mk_eq.mp hx.2).trans
        (ConjClasses.mem_carrier_iff_mk_eq.mp hcout).symm)
    exact χ.toClassFunction.apply_eq_of_isConj hxc
  have hcard : (Finset.univ.filter (· ∈ c.carrier)).card = Nat.card c.carrier := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsum : ∑ x ∈ Finset.univ.filter (· ∈ c.carrier), χ x
      = (Nat.card c.carrier : ℂ) * χ c.out := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, nsmul_eq_mul]
  have hχ1 : χ 1 = (Module.finrank ℂ N : ℂ) := by
    have hthis := congrArg (fun φ : ClassFunction G => φ 1) hχ
    simpa [MonoidAlgebra.moduleCharacter_one] using hthis
  have hkey : (MonoidAlgebra.centralScalarHom N
      ⟨MonoidAlgebra.classSum G c, MonoidAlgebra.classSum_mem_center c⟩) * χ 1
      = (Nat.card c.carrier : ℂ) * χ c.out := by
    rw [hχ1, ← htrace1, htrace2]
    exact hsum
  rw [homega]
  have hdne : (χ 1 : ℂ) ≠ 0 := by
    obtain ⟨d, hd0, hd⟩ := χ.exists_degree
    rw [hd]
    exact Nat.cast_ne_zero.mpr hd0.ne'
  rw [eq_div_iff hdne]
  exact hkey

open scoped Classical in
/-- **Structure-constant identity for central characters**, transporting Task 3's
`classSum_mul` through the algebra homomorphism `centralScalarHom`:
`ω_χ(c) * ω_χ(d) = ∑ e, classMulCoeff c d e * ω_χ(e)`. This is the integrality workhorse for
`Irr.isIntegral_omega`. -/
theorem Irr.omega_mul (χ : Irr G) (c d : ConjClasses G) :
    Irr.omega χ c * Irr.omega χ d
      = ∑ e : ConjClasses G, (MonoidAlgebra.classMulCoeff G c d e : ℂ) * Irr.omega χ e := by
  classical
  set N := χ.exists_simple'.choose with hNdef
  haveI hN : IsSimpleModule (MonoidAlgebra ℂ G) N := χ.exists_simple'.choose_spec.1
  set ze : ConjClasses G → ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G)) :=
    fun e => ⟨MonoidAlgebra.classSum G e, MonoidAlgebra.classSum_mem_center e⟩ with hzedef
  have homega : ∀ e : ConjClasses G, Irr.omega χ e = MonoidAlgebra.centralScalarHom N (ze e) :=
    fun _ => rfl
  have hzz : ze c * ze d = ∑ e : ConjClasses G, MonoidAlgebra.classMulCoeff G c d e • ze e := by
    refine Subtype.ext ?_
    have hcoe : ((ze c * ze d :
        ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G))) : MonoidAlgebra ℂ G)
        = MonoidAlgebra.classSum G c * MonoidAlgebra.classSum G d := rfl
    have hcoe2 : ((∑ e : ConjClasses G, MonoidAlgebra.classMulCoeff G c d e • ze e :
        ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G))) : MonoidAlgebra ℂ G)
        = ∑ e : ConjClasses G,
            MonoidAlgebra.classMulCoeff G c d e • MonoidAlgebra.classSum G e := by
      rw [AddSubmonoidClass.coe_finsetSum]
      exact Finset.sum_congr rfl fun e _ => rfl
    rw [hcoe, hcoe2]
    exact MonoidAlgebra.classSum_mul c d
  calc Irr.omega χ c * Irr.omega χ d
      = MonoidAlgebra.centralScalarHom N (ze c) * MonoidAlgebra.centralScalarHom N (ze d) := by
        rw [homega c, homega d]
    _ = MonoidAlgebra.centralScalarHom N (ze c * ze d) := (map_mul _ (ze c) (ze d)).symm
    _ = MonoidAlgebra.centralScalarHom N
          (∑ e : ConjClasses G, MonoidAlgebra.classMulCoeff G c d e • ze e) := by rw [hzz]
    _ = ∑ e : ConjClasses G,
          MonoidAlgebra.classMulCoeff G c d e • MonoidAlgebra.centralScalarHom N (ze e) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun e _ => map_nsmul _ _ _
    _ = ∑ e : ConjClasses G, (MonoidAlgebra.classMulCoeff G c d e : ℂ) * Irr.omega χ e := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [homega e, nsmul_eq_mul]

/-- Sanity check: the central character of the trivial conjugacy class is `1` (the class sum
of `{1}` is the identity of the group algebra, which acts by the scalar `1`). Used to show
the `ℤ`-span of the `ω_χ` family contains `1`, for `Irr.isIntegral_omega`. -/
theorem Irr.omega_mk_one (χ : Irr G) : Irr.omega χ (ConjClasses.mk 1) = 1 := by
  classical
  set N := χ.exists_simple'.choose with hNdef
  haveI hN : IsSimpleModule (MonoidAlgebra ℂ G) N := χ.exists_simple'.choose_spec.1
  have homega : Irr.omega χ (ConjClasses.mk 1) = MonoidAlgebra.centralScalarHom N
      ⟨MonoidAlgebra.classSum G (ConjClasses.mk 1),
        MonoidAlgebra.classSum_mem_center (ConjClasses.mk 1)⟩ := rfl
  have h1 : (⟨MonoidAlgebra.classSum G (ConjClasses.mk 1),
      MonoidAlgebra.classSum_mem_center (ConjClasses.mk 1)⟩ :
      ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G))) = 1 :=
    Subtype.ext MonoidAlgebra.classSum_mk_one
  rw [homega, h1, map_one]

/-- **Algebraic integrality of the central character** (item 2c): `ω_χ(c)` is an algebraic
integer. Route: the `ℤ`-span `S` of the family `{ω_χ(e)}_{e : ConjClasses G}` is finitely
generated (the family is finite), contains `1` (hence is nonzero), and is stable under
multiplication by any `ω_χ(d)` (`Irr.omega_mul` expresses the product as a `ℕ`-combination of
the family, hence an element of the span); `isIntegral_of_smul_mem_submodule` then gives
integrality. MathComp: `ω_χ(c)` is an algebraic integer (`gring`-mode material, exact name
unconfirmed). -/
theorem Irr.isIntegral_omega (χ : Irr G) (c : ConjClasses G) : IsIntegral ℤ (Irr.omega χ c) := by
  classical
  set S : Submodule ℤ ℂ := Submodule.span ℤ (Set.range (Irr.omega χ)) with hSdef
  have hSfg : S.FG := Submodule.fg_span (Set.finite_range (Irr.omega χ))
  have h1S : (1 : ℂ) ∈ S := by
    rw [hSdef, ← Irr.omega_mk_one χ]
    exact Submodule.subset_span ⟨ConjClasses.mk 1, rfl⟩
  have hSne : S ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.mem_bot] at h1S
    exact one_ne_zero h1S
  have hSmem : ∀ d : ConjClasses G, ∀ n ∈ S, Irr.omega χ d * n ∈ S := by
    intro d
    set mulBy : ℂ →ₗ[ℤ] ℂ :=
      { toFun := fun n => Irr.omega χ d * n
        map_add' := fun x y => mul_add _ x y
        map_smul' := fun a x => by
          simp only [zsmul_eq_mul, RingHom.id_apply]
          ring } with hmulBydef
    have hsub : Set.range (Irr.omega χ) ⊆ (S.comap mulBy : Set ℂ) := by
      rintro n ⟨c', rfl⟩
      change Irr.omega χ d * Irr.omega χ c' ∈ S
      rw [Irr.omega_mul]
      refine Submodule.sum_mem S fun e _ => ?_
      have hcast : (MonoidAlgebra.classMulCoeff G d c' e : ℂ) * Irr.omega χ e
          = (MonoidAlgebra.classMulCoeff G d c' e : ℤ) • Irr.omega χ e := by
        rw [zsmul_eq_mul]
        push_cast
        ring
      rw [hcast]
      exact Submodule.smul_mem S _ (Submodule.subset_span ⟨e, rfl⟩)
    have hle : S ≤ S.comap mulBy := Submodule.span_le.mpr hsub
    exact fun n hn => hle hn
  exact isIntegral_of_smul_mem_submodule S hSne hSfg (Irr.omega χ c) (hSmem c)

end CentralCharacter

/-! ### `χ(1) ∣ |G|` (Task 4, item 3)

First orthogonality (`⟪χ,χ⟫ = 1`) expands, grouping the sum over `G` by conjugacy classes and
applying `Irr.omega_eq`, to `|G| = χ(1) * ∑_c ω_χ(c) * conj(χ(c.out))`. The sum on the right is
an algebraic integer (products of the integral `ω_χ(c)` and the integral `conj(χ(c.out))`);
since it equals the rational number `|G|/χ(1)`, that rational number is a rational algebraic
integer, hence (integral closure of `ℤ` in `ℚ`) an actual integer, giving `χ(1) ∣ |G|`.
MathComp: `dvd_irr1_cardG`. -/

section DegreeDvdCard

variable {G : Type u} [Group G] [Fintype G]

open scoped Classical in
/-- **The degree of an irreducible character divides the order of the group.**
MathComp: `dvd_irr1_cardG`. -/
theorem Irr.exists_degree_dvd_card (χ : Irr G) :
    ∃ d : ℕ, (χ 1 : ℂ) = d ∧ d ∣ Nat.card G := by
  classical
  obtain ⟨d, hd0, hd⟩ := χ.exists_degree
  refine ⟨d, hd, ?_⟩
  have hdne : (χ 1 : ℂ) ≠ 0 := by rw [hd]; exact Nat.cast_ne_zero.mpr hd0.ne'
  -- first orthogonality, expanded: `∑ g, χ g * conj (χ g) = |G|`
  have hsum1 : ∑ g : G, χ g * starRingEnd ℂ (χ g) = (Fintype.card G : ℂ) := by
    have h := Irr.cfInner_eq χ χ
    rw [if_pos rfl, ClassFunction.cfInner_def] at h
    have hGne : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have h2 := congrArg (fun x => (Fintype.card G : ℂ) * x) h
    simpa [mul_inv_cancel_left₀ hGne] using h2
  -- group the sum over `G` by conjugacy classes
  have hpartition : ∑ g : G, χ g * starRingEnd ℂ (χ g)
      = ∑ c : ConjClasses G, (Nat.card c.carrier : ℂ) * (χ c.out * starRingEnd ℂ (χ c.out)) := by
    have hstep : ∑ g : G, χ g * starRingEnd ℂ (χ g)
        = ∑ g : G, χ (ConjClasses.mk g).out * starRingEnd ℂ (χ (ConjClasses.mk g).out) := by
      refine Finset.sum_congr rfl fun g _ => ?_
      have hcout : IsConj (ConjClasses.mk g).out g :=
        ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.mk g).out_eq
      have heq : χ (ConjClasses.mk g).out = χ g := by
        have hthis := χ.toClassFunction.apply_eq_of_isConj hcout
        simpa using hthis
      rw [heq]
    rw [hstep, ← Finset.sum_fiberwise' (Finset.univ : Finset G) ConjClasses.mk
      (fun c => χ c.out * starRingEnd ℂ (χ c.out))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_const]
    have hcardc : (Finset.univ.filter (fun g : G => ConjClasses.mk g = c)).card
        = Nat.card c.carrier := by
      rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeEquivRight fun g =>
        (ConjClasses.mem_carrier_iff_mk_eq (a := g) (b := c)).symm), Nat.card_eq_fintype_card]
    rw [hcardc, nsmul_eq_mul]
  -- `|G| = χ(1) * ∑_c ω_χ(c) * conj (χ (c.out))`
  have hmain : (Nat.card G : ℂ)
      = χ 1 * ∑ c : ConjClasses G, Irr.omega χ c * starRingEnd ℂ (χ c.out) := by
    rw [Nat.card_eq_fintype_card, ← hsum1, hpartition, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have homegamul : Irr.omega χ c * χ 1 = (Nat.card c.carrier : ℂ) * χ c.out :=
      (eq_div_iff hdne).mp (Irr.omega_eq χ c)
    rw [← mul_assoc, ← homegamul]
    ring
  -- the sum is an algebraic integer
  set S : ℂ := ∑ c : ConjClasses G, Irr.omega χ c * starRingEnd ℂ (χ c.out) with hSdef
  have hSint : IsIntegral ℤ S :=
    IsIntegral.sum _ fun c _ => IsIntegral.mul (Irr.isIntegral_omega χ c)
      (IsIntegral.map (starRingEnd ℂ).toIntAlgHom (Irr.isIntegral_apply χ c.out))
  -- `S` equals the rational number `|G| / d`
  set q : ℚ := (Nat.card G : ℚ) / (d : ℚ) with hqdef
  have hdQne : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hdCne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hSeq : S = (q : ℂ) := by
    rw [hqdef]
    push_cast
    rw [eq_div_iff hdCne, mul_comm, ← hd]
    exact hmain.symm
  have hqCint : IsIntegral ℤ (q : ℂ) := hSeq ▸ hSint
  -- transport integrality from `ℂ` down to `ℚ`
  have hinj : Function.Injective ((Rat.castHom ℂ).toIntAlgHom : ℚ →ₐ[ℤ] ℂ) := by
    intro a b hab
    exact Rat.cast_injective (α := ℂ) hab
  have heqcast : ((Rat.castHom ℂ).toIntAlgHom : ℚ →ₐ[ℤ] ℂ) q = (q : ℂ) := rfl
  have hqint : IsIntegral ℤ q := by
    rw [← heqcast] at hqCint
    exact (isIntegral_algHom_iff ((Rat.castHom ℂ).toIntAlgHom : ℚ →ₐ[ℤ] ℂ) hinj).mp hqCint
  -- `ℤ` is integrally closed in `ℚ`, so `q` is an integer
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff ℚ).mp inferInstance hqint
  have hyQ : (y : ℚ) = q := by
    rw [← hy]; simp [algebraMap_int_eq]
  have hqnonneg : 0 ≤ q := by rw [hqdef]; positivity
  have hynonneg : 0 ≤ y := by
    have : (0 : ℚ) ≤ (y : ℚ) := hyQ ▸ hqnonneg
    exact_mod_cast this
  set k : ℕ := y.toNat with hkdef
  have hyk : (y : ℤ) = (k : ℤ) := (Int.toNat_of_nonneg hynonneg).symm
  have hkQ : (k : ℚ) = q := by
    have := hyQ
    rw [hyk] at this
    exact_mod_cast this
  have hkd : (k : ℚ) * (d : ℚ) = (Nat.card G : ℚ) := by
    rw [hkQ, hqdef, div_mul_cancel₀]
    exact hdQne
  have hkdN : k * d = Nat.card G := by exact_mod_cast hkd
  exact ⟨k, hkdN.symm.trans (mul_comm k d)⟩

end DegreeDvdCard

/-! ### Eigen-projections and the scalar-action lemma

The *operator* identity behind `Module.End.trace_eq_sum_zeta_pow_mul_natCast`
(`ClassFunction.lean`): a finite-order operator decomposes along the projections `Q j` onto
its `ζ ^ j`-eigenspaces, and equality in the resulting trace bound forces the operator to be
a scalar. Promoted here from `Burnside.lean` (where it was a deliberately local duplicate —
see the M2 Task 5 report) as part of the M3 Task 4 `Irr.ker` promotion: the kernel
characterization `Irr.mem_ker_iff` below is the `target = 1` instance of the scalar-action
lemma, and `Burnside.lean` keeps consuming the general-`target` form for its class-size
lemma. -/

section EigenKit

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- **Eigen-projections of a finite-order operator.** If `f ^ n = 1` and `ζ` is a primitive
`n`-th root of unity, there are idempotents `Q j` (`j < n`) summing to `1`, with
`f * Q j = ζ ^ j • Q j` and `Q j` a projection onto its range. -/
private theorem Module.End.exists_zeta_pow_eigenProjections {f : Module.End ℂ V} {n : ℕ}
    (hn : n ≠ 0) (hf : f ^ n = 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    ∃ Q : ℕ → Module.End ℂ V,
      (∑ j ∈ range n, Q j = 1) ∧
      (∀ j, f * Q j = ζ ^ j • Q j) ∧
      (∀ j, LinearMap.IsProj (LinearMap.range (Q j)) (Q j)) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hζn : ζ ^ n = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow hn] at hζn
    exact zero_ne_one hζn
  set Q : ℕ → Module.End ℂ V := fun j => (n : ℂ)⁻¹ • ∑ i ∈ range n, ζ⁻¹ ^ (i * j) • f ^ i
    with hQdef
  have hQsum : ∑ j ∈ range n, Q j = 1 := by
    have key : ∀ i ∈ range n, (∑ j ∈ range n, ζ⁻¹ ^ (i * j)) • f ^ i
        = if i = 0 then (n : ℂ) • 1 else 0 := by
      intro i hi
      rcases eq_or_ne i 0 with rfl | hi0
      · simp
      · have hne1 : ζ⁻¹ ^ i ≠ 1 :=
          hζ.inv.pow_ne_one_of_pos_of_lt hi0 (mem_range.mp hi)
        have hpow1 : (ζ⁻¹ ^ i) ^ n = 1 := by
          rw [← pow_mul, mul_comm i n, pow_mul, inv_pow, hζn, inv_one, one_pow]
        rw [if_neg hi0]
        have : ∑ j ∈ range n, ζ⁻¹ ^ (i * j) = 0 := by
          have := geom_sum_eq hne1 n
          simp only [hpow1, sub_self, zero_div] at this
          simpa only [pow_mul] using this
        rw [this, zero_smul]
    calc ∑ j ∈ range n, Q j
        = (n : ℂ)⁻¹ • ∑ j ∈ range n, ∑ i ∈ range n, ζ⁻¹ ^ (i * j) • f ^ i := by
          rw [Finset.smul_sum]
      _ = (n : ℂ)⁻¹ • ∑ i ∈ range n, (∑ j ∈ range n, ζ⁻¹ ^ (i * j)) • f ^ i := by
          rw [Finset.sum_comm]
          congr 1
          exact Finset.sum_congr rfl fun i _ => (Finset.sum_smul).symm
      _ = (n : ℂ)⁻¹ • ((n : ℂ) • 1) := by
          rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' (range n) 0,
            if_pos (mem_range.mpr (Nat.pos_of_ne_zero hn))]
      _ = 1 := by rw [smul_smul, inv_mul_cancel₀ hn0, one_smul]
  have hfQ : ∀ j, f * Q j = ζ ^ j • Q j := by
    intro j
    have expand : f * Q j = (n : ℂ)⁻¹ • ∑ i ∈ range n, ζ⁻¹ ^ (i * j) • f ^ (i + 1) := by
      rw [hQdef, mul_smul_comm, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [mul_smul_comm, ← pow_succ']
    set h : ℕ → Module.End ℂ V := fun i => (ζ ^ j * ζ⁻¹ ^ (i * j)) • f ^ i with hh
    have hstep : ∀ i, ζ⁻¹ ^ (i * j) • f ^ (i + 1) = h (i + 1) := by
      intro i
      rw [hh]
      congr 1
      rw [add_mul, one_mul, pow_add, ← mul_assoc, mul_comm (ζ ^ j), mul_assoc, ← mul_pow,
        mul_inv_cancel₀ hζ0, one_pow, mul_one]
    have hshift : ∑ i ∈ range n, h (i + 1) = ∑ i ∈ range n, h i := by
      have h1 : ∑ i ∈ range (n + 1), h i = ∑ i ∈ range n, h (i + 1) + h 0 :=
        Finset.sum_range_succ' h n
      have h2 : ∑ i ∈ range (n + 1), h i = ∑ i ∈ range n, h i + h n :=
        Finset.sum_range_succ h n
      have hn' : h n = h 0 := by
        rw [hh]
        simp only [Nat.zero_mul, pow_zero, mul_one]
        rw [pow_mul, inv_pow, hζn, inv_one, one_pow, mul_one, hf]
      have := h1.symm.trans h2
      rw [hn'] at this
      exact add_right_cancel this
    calc f * Q j
        = (n : ℂ)⁻¹ • ∑ i ∈ range n, h (i + 1) := by
          rw [expand]
          exact congrArg _ (Finset.sum_congr rfl fun i _ => hstep i)
      _ = (n : ℂ)⁻¹ • ∑ i ∈ range n, h i := by rw [hshift]
      _ = ζ ^ j • Q j := by
          rw [hQdef]
          simp only [hh, mul_smul, ← Finset.smul_sum]
          rw [smul_comm]
  have hfpowQ : ∀ j k, f ^ k * Q j = (ζ ^ j) ^ k • Q j := by
    intro j k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_assoc, hfQ j, mul_smul_comm, ih, smul_smul, pow_succ,
        mul_comm (ζ ^ j)]
  have hQQ : ∀ j, Q j * Q j = Q j := by
    intro j
    have expand : Q j * Q j = (n : ℂ)⁻¹ • ∑ i ∈ range n, ζ⁻¹ ^ (i * j) • (f ^ i * Q j) := by
      conv_lhs => rw [hQdef]
      rw [smul_mul_assoc, Finset.sum_mul]
      congr 1
    rw [expand]
    have : ∀ i ∈ range n, ζ⁻¹ ^ (i * j) • (f ^ i * Q j) = Q j := by
      intro i _
      rw [hfpowQ j i, smul_smul, ← pow_mul, mul_comm j i, ← mul_pow, inv_mul_cancel₀ hζ0,
        one_pow, one_smul]
    rw [Finset.sum_congr rfl this, Finset.sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ hn0, one_smul]
  have hproj : ∀ j, LinearMap.IsProj (LinearMap.range (Q j)) (Q j) := by
    intro j
    refine ⟨fun x => LinearMap.mem_range_self _ x, fun x hx => ?_⟩
    obtain ⟨y, rfl⟩ := hx
    have := congrArg (fun T : Module.End ℂ V => T y) (hQQ j)
    simpa [Module.End.mul_apply] using this
  exact ⟨Q, hQsum, hfQ, hproj⟩

end EigenKit

/-- Real part of a `ℕ`-weighted sum of complex numbers, term by term. Helper for the
equality case of the triangle inequality below. -/
private theorem Complex.re_natCast_mul_finset_sum {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (z : ι → ℂ) : (∑ i ∈ s, (m i : ℂ) * z i).re = ∑ i ∈ s, (m i : ℝ) * (z i).re := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Complex.add_re, ih, Complex.mul_re]
    simp

/-- Real part of a sum of `ℕ`-casts. Helper for the equality case of the triangle
inequality below; public because `Burnside.lean`'s nonvanishing dichotomy also consumes
it. -/
theorem Complex.re_natCast_finset_sum {ι : Type*} (s : Finset ι) (m : ι → ℕ) :
    (∑ i ∈ s, (m i : ℂ) : ℂ).re = ∑ i ∈ s, (m i : ℝ) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih => rw [Finset.sum_cons, Finset.sum_cons, Complex.add_re, ih]; simp

/-- If `z i` (for `i` in a finite set `s`) all have norm `1`, `m : ι → ℕ` are weights, and the
weighted sum `∑ m i • z i` equals the real total weight `∑ m i`, then every `z i` with nonzero
weight equals `1`. The "equality case of the triangle inequality," isolated as a standalone
complex-number fact (no operator theory): taking real parts turns the hypothesis into a sum of
nonpositive terms equal to zero, forcing each term to vanish. -/
private theorem Complex.eq_one_of_natCast_smul_sum_eq_natCast_sum {ι : Type*} (s : Finset ι)
    (m : ι → ℕ) (z : ι → ℂ) (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (heq : ∑ i ∈ s, (m i : ℂ) * z i = (∑ i ∈ s, (m i : ℂ))) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hm : m i₀ ≠ 0) : z i₀ = 1 := by
  have hre : ∑ i ∈ s, ((m i : ℝ) * (z i).re - (m i : ℝ)) = 0 := by
    have hre_eq : (∑ i ∈ s, (m i : ℂ) * z i).re = (∑ i ∈ s, (m i : ℂ) : ℂ).re :=
      congrArg Complex.re heq
    rw [Complex.re_natCast_mul_finset_sum, Complex.re_natCast_finset_sum] at hre_eq
    have hsplit : ∑ i ∈ s, ((m i : ℝ) * (z i).re - (m i : ℝ))
        = ∑ i ∈ s, (m i : ℝ) * (z i).re - ∑ i ∈ s, (m i : ℝ) := by
      rw [Finset.sum_sub_distrib]
    rw [hsplit, hre_eq, sub_self]
  have hnonpos : ∀ i ∈ s, (m i : ℝ) * (z i).re - (m i : ℝ) ≤ 0 := by
    intro i hi
    have hzre : (z i).re ≤ 1 := by
      have hb : (z i).re * (z i).re ≤ Complex.normSq (z i) := Complex.re_sq_le_normSq (z i)
      rw [Complex.normSq_eq_norm_sq, hz i hi, one_pow] at hb
      nlinarith [sq_nonneg ((z i).re - 1)]
    nlinarith [Nat.cast_nonneg (α := ℝ) (m i)]
  have hall0 := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hre i₀ hi₀
  have hmi0 : (m i₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hre1 : (z i₀).re = 1 := by
    have : (m i₀ : ℝ) * ((z i₀).re - 1) = 0 := by linarith [hall0]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hmi0
    · linarith
  have hnorm1 : ‖z i₀‖ = 1 := hz i₀ hi₀
  have hnormSq : Complex.normSq (z i₀) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm1, one_pow]
  rw [Complex.normSq_apply, hre1] at hnormSq
  have himsq : (z i₀).im * (z i₀).im = 0 := by linarith
  have him0 : (z i₀).im = 0 := by
    rcases mul_eq_zero.mp himsq with h | h <;> exact h
  exact Complex.ext hre1 him0

/-- **Scalar-action lemma.** If `f ^ n = 1` and `trace f = target * finrank V` for a unimodular
`target`, then `f` is literally the scalar map `target • 1`. Specializes (`target = 1`) to the
kernel characterization `Irr.mem_ker_iff` below, and (general `target`) to the scalar-action
fact behind `Burnside.lean`'s class-size lemma. -/
theorem Module.End.eq_smul_one_of_trace_eq_mul_finrank {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] {f : Module.End ℂ V} {n : ℕ} (hn : n ≠ 0)
    (hf : f ^ n = 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) {target : ℂ} (htarget : ‖target‖ = 1)
    (htrace : trace ℂ V f = target * (Module.finrank ℂ V : ℂ)) :
    f = target • (1 : Module.End ℂ V) := by
  obtain ⟨Q, hQsum, hfQ, hproj⟩ := Module.End.exists_zeta_pow_eigenProjections hn hf hζ
  set m : ℕ → ℕ := fun j => Module.finrank ℂ (LinearMap.range (Q j)) with hmdef
  have hfsum : f = ∑ j ∈ range n, ζ ^ j • Q j := by
    conv_lhs => rw [← mul_one f, ← hQsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hfQ j
  have htraceQ : ∀ j, trace ℂ V (Q j) = (m j : ℂ) := fun j => (hproj j).trace
  have htrace2 : trace ℂ V f = ∑ j ∈ range n, ζ ^ j * (m j : ℂ) := by
    rw [hfsum, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, htraceQ, smul_eq_mul]
  have htrace1 : (Module.finrank ℂ V : ℂ) = ∑ j ∈ range n, (m j : ℂ) := by
    have h1 : trace ℂ V (1 : Module.End ℂ V) = (Module.finrank ℂ V : ℂ) :=
      LinearMap.trace_one ℂ V
    rw [← h1, ← hQsum, map_sum]
    exact Finset.sum_congr rfl fun j _ => htraceQ j
  have hcombine : ∑ j ∈ range n, (m j : ℂ) * ζ ^ j = ∑ j ∈ range n, (m j : ℂ) * target := by
    have hstep : ∑ j ∈ range n, (m j : ℂ) * ζ ^ j = target * (Module.finrank ℂ V : ℂ) := by
      rw [← htrace, htrace2]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hstep, htrace1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have htarget0 : target ≠ 0 := fun h => by simp [h] at htarget
  have hkey : ∀ j ∈ range n, m j ≠ 0 → ζ ^ j = target := by
    intro j hj hmj
    have hz : ∀ i ∈ range n, ‖ζ ^ i * target⁻¹‖ = 1 := by
      intro i _
      rw [norm_mul, norm_inv]
      have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one hn
      rw [norm_pow, hζnorm, one_pow, htarget, inv_one, mul_one]
    have heq2 : ∑ i ∈ range n, (m i : ℂ) * (ζ ^ i * target⁻¹) = ∑ i ∈ range n, (m i : ℂ) := by
      have hstep : ∀ i ∈ range n, (m i : ℂ) * (ζ ^ i * target⁻¹) = ((m i : ℂ) * ζ ^ i) * target⁻¹ :=
        fun i _ => by ring
      rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, hcombine, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, mul_inv_cancel₀ htarget0, mul_one]
    have hthis := Complex.eq_one_of_natCast_smul_sum_eq_natCast_sum (range n) m
      (fun i => ζ ^ i * target⁻¹) hz heq2 hj hmj
    rw [← div_eq_mul_inv] at hthis
    exact (div_eq_one_iff_eq htarget0).mp hthis
  have hQ0 : ∀ j ∈ range n, m j = 0 → Q j = 0 := by
    intro j _ hmj
    have hrange0 : LinearMap.range (Q j) = ⊥ :=
      Submodule.finrank_eq_zero.mp hmj
    refine LinearMap.ext fun x => ?_
    have hx := (hproj j).map_mem x
    rw [hrange0] at hx
    simpa using hx
  by_cases hexists : ∃ j ∈ range n, m j ≠ 0
  · obtain ⟨j₀, hj₀mem, hj₀ne⟩ := hexists
    have hother0 : ∀ j ∈ range n, j ≠ j₀ → Q j = 0 := by
      intro j hj hjne
      apply hQ0 j hj
      by_contra hmj
      have h1 := hkey j hj hmj
      have h2 := hkey j₀ hj₀mem hj₀ne
      have hinjcast : ζ ^ j = ζ ^ j₀ := h1.trans h2.symm
      have := hζ.pow_inj (mem_range.mp hj) (mem_range.mp hj₀mem) hinjcast
      exact hjne this
    have hQj0 : Q j₀ = 1 := by
      have : ∑ j ∈ range n, Q j = Q j₀ := by
        rw [Finset.sum_eq_single j₀]
        · intro j hj hjne; exact hother0 j hj hjne
        · intro h; exact absurd hj₀mem h
      rw [← this, hQsum]
    rw [hfsum]
    rw [Finset.sum_eq_single j₀]
    · rw [hQj0, hkey j₀ hj₀mem hj₀ne]
    · intro j hj hjne
      rw [hother0 j hj hjne, smul_zero]
    · intro h; exact absurd hj₀mem h
  · exfalso
    push Not at hexists
    have : (∑ j ∈ range n, (m j : ℂ)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [hexists j hj]; simp
    rw [← htrace1] at this
    have hVpos : 0 < Module.finrank ℂ V := Module.finrank_pos
    exact absurd this (Nat.cast_ne_zero.mpr hVpos.ne')

/-! ### Character kernels

`Irr.ker` is the kernel of the associated representation (a genuine `MonoidHom.ker`, hence
automatically normal); `Irr.mem_ker_iff` identifies it with `{g | χ g = χ 1}` via the scalar-
action lemma at `target = 1`. Promoted here from `Burnside.lean` (M3 Task 4, per the M2
deferred-consolidation list), statements unchanged; the separation lemma
`Irr.exists_ne_one_apply_ne` (the intersection of all character kernels is trivial, in
element form) is new with M3 Task 4, feeding the Frobenius kernel theorem. -/

section Kernel

variable {G : Type u} [Group G] [Fintype G]

/-- The kernel of an irreducible character: the kernel of (a witnessing) associated
representation, as a genuine `MonoidHom.ker` — hence automatically a normal subgroup. -/
noncomputable def Irr.ker (χ : Irr G) : Subgroup G :=
  MonoidHom.ker (Representation.ofModule' (k := ℂ) (G := G) χ.exists_simple'.choose)

instance Irr.ker.normal (χ : Irr G) : χ.ker.Normal := MonoidHom.normal_ker _

/-- **Kernel characterization.** `g ∈ χ.ker ↔ χ g = χ 1`: the equality case of the trace bound,
via the scalar-action lemma at `target = 1`. -/
theorem Irr.mem_ker_iff (χ : Irr G) (g : G) : g ∈ χ.ker ↔ χ g = χ 1 := by
  set N := χ.exists_simple'.choose with hNdef
  haveI hN : IsSimpleModule (MonoidAlgebra ℂ G) N := χ.exists_simple'.choose_spec.1
  have hχ : χ.toClassFunction = MonoidAlgebra.moduleCharacter G N :=
    χ.exists_simple'.choose_spec.2
  have hχg : χ g = trace ℂ N (MonoidAlgebra.actionEnd N g) := by
    have := congrArg (fun φ : ClassFunction G => φ g) hχ
    simpa [MonoidAlgebra.moduleCharacter_apply] using this
  have hχ1 : χ 1 = (Module.finrank ℂ N : ℂ) := by
    have := congrArg (fun φ : ClassFunction G => φ 1) hχ
    simpa [MonoidAlgebra.moduleCharacter_one] using this
  have hkeriff : g ∈ χ.ker
      ↔ Representation.ofModule' (k := ℂ) (G := G) N g = 1 := Iff.rfl
  rw [hkeriff]
  constructor
  · intro hg
    rw [MonoidAlgebra.ofModule'_eq_actionEnd] at hg
    rw [hχg, hg, LinearMap.trace_one, hχ1]
  · intro heq
    haveI : Nontrivial N := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) N
    have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
    have hpow1 : (MonoidAlgebra.actionEnd N g) ^ orderOf g = 1 := by
      rw [← MonoidAlgebra.ofModule'_eq_actionEnd, ← map_pow, pow_orderOf_eq_one, map_one]
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / orderOf g) with hζdef
    have hζ : IsPrimitiveRoot ζ (orderOf g) := Complex.isPrimitiveRoot_exp (orderOf g) hn
    have htrace : trace ℂ N (MonoidAlgebra.actionEnd N g)
        = (1 : ℂ) * (Module.finrank ℂ N : ℂ) := by
      rw [one_mul, ← hχ1, ← hχg, heq]
    have hscalar := Module.End.eq_smul_one_of_trace_eq_mul_finrank hn hpow1 hζ
      (by norm_num) htrace
    rw [MonoidAlgebra.ofModule'_eq_actionEnd, hscalar, one_smul]

/-- A character whose kernel is everything is trivial: `g` acting as `1` for every `g` forces
`⟪χ, 1⟫ = χ 1 ≠ 0`, and distinct irreducible characters are orthogonal. -/
theorem Irr.eq_one_of_ker_eq_top (χ : Irr G) (htop : χ.ker = ⊤) : χ = Irr.one := by
  classical
  by_contra hne
  have hall : ∀ g : G, χ g = χ 1 := fun g =>
    (Irr.mem_ker_iff χ g).mp (htop ▸ Subgroup.mem_top g)
  have hval : ⟪χ.toClassFunction, (Irr.one : Irr G).toClassFunction⟫_[G] = χ 1 := by
    rw [ClassFunction.cfInner_def]
    have hterm : ∀ g : G, χ.toClassFunction g
        * starRingEnd ℂ ((Irr.one : Irr G).toClassFunction g) = χ 1 := fun g => by
      rw [Irr.coe_toClassFunction, Irr.coe_toClassFunction, Irr.one_apply, map_one, mul_one,
        hall g]
    rw [Finset.sum_congr rfl fun g _ => hterm g, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
      one_mul]
  have hzero := Irr.cfInner_eq χ Irr.one
  rw [if_neg hne, hval] at hzero
  obtain ⟨d, hd0, hd⟩ := χ.exists_degree
  rw [hd] at hzero
  exact (Nat.cast_ne_zero.mpr hd0.ne') hzero

/-- **Separation**: a nonidentity element is detected by some nonprincipal irreducible
character — equivalently, the intersection of the kernels of the nonprincipal irreducible
characters is trivial. Column argument: if `χ g = χ 1` for every `χ`, the second
orthogonality relation at `(g, 1)` reads `∑ χ, (χ 1)^2 = 0`, contradicting
`∑ χ, (χ 1)^2 = |G|`. Feeds the kernel extraction step of Frobenius' kernel theorem
(`FrobeniusKernel.lean`). -/
theorem Irr.exists_ne_one_apply_ne {g : G} (hg : g ≠ 1) :
    ∃ χ : Irr G, χ ≠ Irr.one ∧ χ g ≠ χ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hall : ∀ χ : Irr G, χ g = χ 1 := by
    intro χ
    rcases eq_or_ne χ Irr.one with rfl | hne
    · rw [Irr.one_apply, Irr.one_apply]
    · exact hcon χ hne
  have h2 := Irr.second_orthogonality g 1
  have hgconj : ¬ IsConj g 1 := fun hc => hg (isConj_one_left.mp hc)
  rw [if_neg hgconj] at h2
  have hterm : ∀ χ : Irr G, χ g * starRingEnd ℂ (χ 1) = (χ 1 : ℂ) ^ 2 := by
    intro χ
    obtain ⟨d, -, hd⟩ := χ.exists_degree
    rw [hall χ, hd, map_natCast, sq]
  rw [Finset.sum_congr rfl fun χ _ => hterm χ, Irr.sum_sq_degree] at h2
  exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne') h2

end Kernel
