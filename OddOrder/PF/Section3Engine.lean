/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import Mathlib.Data.Matrix.Mul
import OddOrder.Mathlib.RepresentationTheory.VirtualChar

/-!
# Peterfalvi, Section 3: the combinatorial engine for (3.5)

This file is the decision-D7 replacement for the `CyclicTIisoReflexion` module of
`PFsection3.v` (lines 80–853): the Coq development proves the combinatorial core of
Peterfalvi (3.5) — the existence of a *column pivot* in a rectangular array of norm-3
virtual characters — by a bespoke 770-line boolean-SAT reflection engine (reified clause
"theories", a `sat`/`unsat` semantics, and a mini tactic DSL: `consider`, `fill`, `uhave`,
`uwlog`, `counter to`, `symmetric to`).  **None of that machinery is ported.**  Instead the
facts it establishes are proved here as ordinary finite case analyses, the way Peterfalvi's
book handles them (over at most a 4 × 2 sub-array).

## Setting

Everything is stated at the level of `ℤ`-coefficient vectors: a virtual character of `G` is
determined by its coefficient function `Irr G → ℤ`, inner products of virtual characters
become integer dot products (`dotProduct`, `⬝ᵥ`) of coefficient functions, and a *signed
irreducible* (MathComp `dchi`) is a coordinate together with a sign `ε = ±1`.  The
rectangular array of Coq's `is_Lmodel`/`model` becomes `PF3Engine.IsBetaGrid`: a family
`b : ι₁ → ι₂ → Ω → ℤ` (in the application `Ω = Irr G`, `ι₁`/`ι₂` = nonprincipal
`Irr W₁`/`Irr W₂`, and `b i j` = the coefficients of `β_ij = Ind (α_ij) - 1`) with the Gram
pattern `⟪b i j, b i' j'⟫ = (i = i').+1 * (j = j').+1 - 1` (norm `3`; dot `1` on a common
row or column; dot `0` otherwise) and the size side conditions of `is_Lmodel` (both index
types of even cardinality `≥ 2`, of different cardinalities).  The Coq model's orthonormal
family `X` (the `x k`) needs no counterpart: coordinates of `Ω` *are* the orthonormal basis.

## Main results

* `PF3Engine.IsBetaGrid.exists_share_col` / `exists_share_row` / `share_col_eq` /
  `share_row_eq` — Peterfalvi (3.5.2): two entries on a common line share **exactly one**
  coordinate, and with the **same sign**.  This subsumes the Coq reflection lemmas
  `unsat_J`, `unsat_II` and the `L` test; the impossible overlap pattern `{+1, +1, −1}` is
  killed by a two-line parity argument against a "mate" entry (`⟪f, h⟫ − ⟪g, h⟫` is odd for
  a suitable third entry `h`, but would be even if `f` and `g` differed at one coordinate).
* `PF3Engine.IsBetaGrid.col_coherent` — the combinatorial core of Peterfalvi (3.5.4), Coq
  `unsat_Ii`: a coordinate shared by two entries of a column is present in *every* entry of
  that column.  The `K₄`-shaped escape configuration (four column entries pairwise sharing
  six distinct coordinates) is killed by another parity argument; the remaining cases funnel
  through the explicit 4 × 2 analysis (`col_coherent_core`/`col_coherent_final`), with the
  Coq's `symmetric to` symmetry reductions replaced by re-invocations with permuted
  arguments.
* `PF3Engine.IsBetaGrid.col_share_isolated` — Coq `unsat_C`: the shared coordinate of a
  column never occurs in an entry of a different column (statement transpose-symmetric; the
  proof transposes to put the ≥ 4 direction along the column, as the Coq's
  `unsat_consider`/`sub_match` machinery did implicitly).
* `PF3Engine.IsBetaGrid.exists_column_pivot` — Coq `column_pivot`, the essential part of
  (3.5.5): every column `j₀` has a *pivot*: a coordinate `a` and sign `ε` with
  `b i j a = if j = j₀ then ε else 0` for all `i, j`.  Row pivots follow by applying this to
  `IsBetaGrid.transpose`.
* `PF3Engine.exists_column_pivot_irr` — the class-function form consumed by Task 5's proof
  of (3.5) (Coq `cyclicTIiso_basis_exists`): for a family `β : ι₁ → ι₂ → ClassFunction G` of
  virtual characters with the (3.5.1) inner-product pattern, every column has a signed
  irreducible pivot `(χ, ε)` with `⟪β i j, χ⟫ = if j = j₀ then ε else 0`.  MathComp `dchi`
  outputs are returned as the pair `(χ, ε)`.

## Porting notes (D7)

* The Coq `O` test (dot-product evaluation of partially known entries) becomes the support
  expansion `PF3Engine.dotProduct_eq_of_support₃` plus `omega` on the resulting linear
  equations; the `L` test becomes `share_col_eq`/`share_row_eq`.
* The Coq statements index entries by `'I_m.1.+1`/`'I_m.2.+1` with `i ≠ 0` side conditions
  (grid = the nonzero indices); here the index types `ι₁`, `ι₂` carry only the grid, so the
  `≠ 0` conditions disappear.  Task 5 instantiates `ι₁`/`ι₂` with the nonprincipal
  irreducible characters of `W₁`/`W₂`.
* `unsat_J`/`unsat_II`/`unsat_Ii`/`unsat_C` are `Let`-bound (private) in the Coq file; only
  `column_pivot` feeds (3.5).  The corresponding statements here are exported anyway (they
  are true, self-contained, and cheap), but Task 5 should need only the pivot theorems.
-/

namespace PF3Engine

open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ### Norm-3 integer vectors

A vector `f : Ω → ℤ` with `f ⬝ᵥ f = 3` has values in `{-1, 0, 1}` and support of size
exactly `3`.  These replace the `norm_clP`/`sat_fill`/`norm_lit` layer of the Coq module
(there stated for norm-3 virtual characters; here `vchar_norm2`-style coefficient counting,
cf. `ClassFunction.card_filter_ne_zero_eq_of_sum_sq_eq` which caps at norm `2`). -/

private theorem sq_le_three {f : Ω → ℤ} (h3 : f ⬝ᵥ f = 3) (ω : Ω) : f ω * f ω ≤ 3 :=
  le_of_le_of_eq
    (Finset.single_le_sum (f := fun ω => f ω * f ω)
      (fun ω _ => mul_self_nonneg (f ω)) (mem_univ ω)) h3

/-- Every value of a norm-3 integer vector lies in `{-1, 0, 1}`.  Coq: `norm_lit`. -/
theorem val_of_norm3 {f : Ω → ℤ} (h3 : f ⬝ᵥ f = 3) (ω : Ω) :
    f ω = -1 ∨ f ω = 0 ∨ f ω = 1 := by
  have h := sq_le_three h3 ω
  have h1 : 4 * f ω ≤ 7 := by nlinarith [sq_nonneg (f ω - 2)]
  have h2 : -7 ≤ 4 * f ω := by nlinarith [sq_nonneg (f ω + 2)]
  omega

private theorem card_support_of_norm3 {f : Ω → ℤ} (h3 : f ⬝ᵥ f = 3) :
    ({ω : Ω | f ω ≠ 0} : Finset Ω).card = 3 := by
  have hval : ∀ ω : Ω, f ω * f ω = if f ω ≠ 0 then 1 else 0 := by
    intro ω
    rcases val_of_norm3 h3 ω with h | h | h <;> rw [h] <;> norm_num
  have hsum : ∑ ω : Ω, (if f ω ≠ 0 then (1 : ℤ) else 0) = 3 := by
    rw [← show ∑ ω : Ω, f ω * f ω = 3 from h3]
    exact Finset.sum_congr rfl fun ω _ => (hval ω).symm
  rw [Finset.sum_boole] at hsum
  exact_mod_cast hsum

/-- A norm-3 vector vanishes outside any three distinct coordinates where it is nonzero
(saturation: the support has size exactly `3`). -/
theorem eq_zero_of_norm3 {f : Ω → ℤ} (h3 : f ⬝ᵥ f = 3) {a b c : Ω} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : f a ≠ 0) (hb : f b ≠ 0) (hc : f c ≠ 0) {ω : Ω}
    (hωa : ω ≠ a) (hωb : ω ≠ b) (hωc : ω ≠ c) : f ω = 0 := by
  classical
  by_contra hω
  have hsub : ({ω, a, b, c} : Finset Ω) ⊆ ({x : Ω | f x ≠ 0} : Finset Ω) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp only [mem_filter_univ] <;> assumption
  have hcard : ({ω, a, b, c} : Finset Ω).card = 4 := by
    rw [card_insert_of_notMem (by simp [hωa, hωb, hωc]),
      card_insert_of_notMem (by simp [hab, hac]), card_insert_of_notMem (by simp [hbc]),
      card_singleton]
  have := Finset.card_le_card hsub
  rw [hcard, card_support_of_norm3 h3] at this
  omega

/-- A norm-3 vector is nonzero at three distinct coordinates.  Together with
`eq_zero_of_norm3` this is the Coq `fill` step (minus basis bookkeeping): the support is
exactly a triple. -/
theorem exists_triple_of_norm3 {f : Ω → ℤ} (h3 : f ⬝ᵥ f = 3) :
    ∃ a b c : Ω, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ f a ≠ 0 ∧ f b ≠ 0 ∧ f c ≠ 0 := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp (card_support_of_norm3 h3)
  have hmem : ∀ x ∈ ({a, b, c} : Finset Ω), f x ≠ 0 := by
    intro x hx
    rw [← hset, mem_filter_univ] at hx
    exact hx
  exact ⟨a, b, c, hab, hac, hbc, hmem a (by simp), hmem b (by simp), hmem c (by simp)⟩

/-- A norm-3 vector nonzero at `a` is nonzero at exactly two further coordinates. -/
theorem exists_pair_of_norm3 {f : Ω → ℤ} (h3 : f ⬝ᵥ f = 3) {a : Ω} (ha : f a ≠ 0) :
    ∃ b c : Ω, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ f b ≠ 0 ∧ f c ≠ 0 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩ := exists_triple_of_norm3 h3
  by_cases hax : a = x
  · exact ⟨y, z, by rw [hax]; exact hxy, by rw [hax]; exact hxz, hyz, hy, hz⟩
  by_cases hay : a = y
  · exact ⟨x, z, by rw [hay]; exact fun h => hxy h.symm, by rw [hay]; exact hyz, hxz, hx, hz⟩
  by_cases haz : a = z
  · exact ⟨x, y, by rw [haz]; exact fun h => hxz h.symm, by rw [haz]; exact fun h => hyz h.symm,
      hxy, hx, hy⟩
  · exact absurd (eq_zero_of_norm3 h3 hxy hxz hyz hx hy hz hax hay haz) ha

/-- A norm-3 vector nonzero at two distinct coordinates is nonzero at a third. -/
theorem exists_third_of_norm3 {f : Ω → ℤ} (h3 : f ⬝ᵥ f = 3) {a b : Ω} (hab : a ≠ b)
    (ha : f a ≠ 0) (hb : f b ≠ 0) : ∃ c : Ω, a ≠ c ∧ b ≠ c ∧ f c ≠ 0 := by
  obtain ⟨x, y, hax, hay, hxy, hx, hy⟩ := exists_pair_of_norm3 h3 ha
  by_cases hbx : b = x
  · exact ⟨y, hay, by rw [hbx]; exact hxy, hy⟩
  by_cases hby : b = y
  · exact ⟨x, hax, by rw [hby]; exact fun h => hxy h.symm, hx⟩
  · exact absurd (eq_zero_of_norm3 h3 hax hay hxy ha hx hy hab.symm hbx hby) hb

/-- Dot-product expansion over a three-element support: the engine form of the Coq `O` test
(`Otest`, (3.5.1) evaluation). -/
theorem dotProduct_eq_of_support₃ {f g : Ω → ℤ} {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hf : ∀ ω, ω ≠ a → ω ≠ b → ω ≠ c → f ω = 0) :
    f ⬝ᵥ g = f a * g a + f b * g b + f c * g c := by
  classical
  have hsum : f ⬝ᵥ g = ∑ ω ∈ ({a, b, c} : Finset Ω), f ω * g ω := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun ω _ hω => ?_).symm
    simp only [mem_insert, mem_singleton, not_or] at hω
    rw [hf ω hω.1 hω.2.1 hω.2.2, zero_mul]
  rw [hsum, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, add_assoc]

/-- If `f` and `g` agree off the single coordinate `a`, their dot products against any `h`
differ by `(f a - g a) * h a`.  The parity engine behind (3.5.2). -/
theorem dotProduct_sub_of_eq_off {f g h : Ω → ℤ} {a : Ω} (hfg : ∀ ω, ω ≠ a → f ω = g ω) :
    f ⬝ᵥ h - g ⬝ᵥ h = (f a - g a) * h a := by
  rw [← sub_dotProduct]
  have hexp : (f - g) ⬝ᵥ h = ∑ ω : Ω, (f ω - g ω) * h ω :=
    Finset.sum_congr rfl fun ω _ => by rw [Pi.sub_apply]
  rw [hexp, Finset.sum_eq_single a (fun ω _ hω => by rw [hfg ω hω, sub_self, zero_mul])
    (fun h => absurd (mem_univ a) h)]

/-! ### Sign and product arithmetic helpers -/

private theorem eq_of_mul_eq_one {x y : ℤ} (hx : x = -1 ∨ x = 0 ∨ x = 1) (h : x * y = 1) :
    y = x := by
  rcases hx with h' | h' | h' <;> rw [h'] at h ⊢ <;> omega

private theorem eq_neg_of_mul_eq_neg_one {x y : ℤ} (hx : x = -1 ∨ x = 0 ∨ x = 1)
    (h : x * y = -1) : y = -x := by
  rcases hx with h' | h' | h' <;> rw [h'] at h ⊢ <;> omega

private theorem eq_zero_of_mul_eq_zero {x y : ℤ} (hx : x ≠ 0) (h : x * y = 0) : y = 0 :=
  (mul_eq_zero.mp h).resolve_left hx

private theorem mul_val_cases {x y : ℤ} (hx : x = -1 ∨ x = 0 ∨ x = 1)
    (hy : y = -1 ∨ y = 0 ∨ y = 1) : x * y = -1 ∨ x * y = 0 ∨ x * y = 1 := by
  rcases hx with h | h | h <;> rcases hy with h' | h' | h' <;> rw [h, h'] <;> norm_num

/-- Three values in `{-1, 0, 1}` summing to `1`: either a single `1` or the pattern
`{1, 1, -1}` (the pattern (3.5.2) rules out).  Pure `omega`. -/
private theorem sum_three_eq_one_cases {t₁ t₂ t₃ : ℤ} (h1 : t₁ = -1 ∨ t₁ = 0 ∨ t₁ = 1)
    (h2 : t₂ = -1 ∨ t₂ = 0 ∨ t₂ = 1) (h3 : t₃ = -1 ∨ t₃ = 0 ∨ t₃ = 1)
    (hsum : t₁ + t₂ + t₃ = 1) :
    (t₁ = 1 ∧ t₂ = 0 ∧ t₃ = 0) ∨ (t₂ = 1 ∧ t₁ = 0 ∧ t₃ = 0) ∨ (t₃ = 1 ∧ t₁ = 0 ∧ t₂ = 0) ∨
    (t₁ = -1 ∧ t₂ = 1 ∧ t₃ = 1) ∨ (t₂ = -1 ∧ t₁ = 1 ∧ t₃ = 1) ∨
    (t₃ = -1 ∧ t₁ = 1 ∧ t₂ = 1) := by
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
    rcases h3 with rfl | rfl | rfl <;> omega

private theorem exists_notMem_of_card_lt {α : Type*} [Fintype α] (s : Finset α)
    (h : s.card < Fintype.card α) : ∃ x, x ∉ s := by
  by_contra hall
  have hsub : (Finset.univ : Finset α) ⊆ s := fun x _ =>
    not_not.mp (not_exists.mp hall x)
  have := Finset.card_le_card hsub
  rw [Finset.card_univ] at this
  omega

/-! ### The grid -/

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- The coefficient array of Peterfalvi (3.5): the `ℤ`-coefficient (over the coordinate/
irreducible-character type `Ω`) form of the Coq reflection module's `is_Lmodel`/`model`
(PFsection3.v:428–441).  `b i j` is the coefficient vector of the virtual character
`β_ij = Ind (α_ij) - 1`; `dot_eq` is the inner-product pattern (3.5.1) (`dot_ref`), and the
cardinality fields are `is_Lmodel`'s size conditions on the array (`(w₁-1) × (w₂-1)` with
`w₁ ≠ w₂` odd and `≥ 3`).  The Coq model's orthonormal component list `X`/`is_Rmodel` has no
counterpart: coordinates of `Ω` are the orthonormal basis. -/
structure IsBetaGrid (b : ι₁ → ι₂ → Ω → ℤ) : Prop where
  /-- `#|W₁| - 1` is even (`odd bb.1.+1` in `is_Lmodel`). -/
  even_card₁ : Even (Fintype.card ι₁)
  /-- `#|W₂| - 1` is even. -/
  even_card₂ : Even (Fintype.card ι₂)
  /-- The two dimensions differ (`bb.1 != bb.2`; from `coprime w₁ w₂`, `w₁, w₂ > 2`). -/
  card_ne : Fintype.card ι₁ ≠ Fintype.card ι₂
  /-- At least two rows (`bb.1 > 1`). -/
  one_lt_card₁ : 1 < Fintype.card ι₁
  /-- At least two columns (`bb.2 > 1`). -/
  one_lt_card₂ : 1 < Fintype.card ι₂
  /-- The (3.5.1) Gram pattern: norm `3`, dot `1` on a common line, dot `0` otherwise
  (Coq `dot_ref`). -/
  dot_eq : ∀ i₁ j₁ i₂ j₂, b i₁ j₁ ⬝ᵥ b i₂ j₂ =
    (if i₁ = i₂ then 2 else 1) * (if j₁ = j₂ then 2 else 1) - 1

namespace IsBetaGrid

variable {b : ι₁ → ι₂ → Ω → ℤ}

theorem norm3 (hb : IsBetaGrid b) (i : ι₁) (j : ι₂) : b i j ⬝ᵥ b i j = 3 := by
  have h := hb.dot_eq i j i j
  rwa [if_pos rfl, if_pos rfl] at h

theorem dot_row (hb : IsBetaGrid b) (i : ι₁) {j j' : ι₂} (h : j ≠ j') :
    b i j ⬝ᵥ b i j' = 1 := by
  have h' := hb.dot_eq i j i j'
  rwa [if_pos rfl, if_neg h] at h'

theorem dot_col (hb : IsBetaGrid b) {i i' : ι₁} (h : i ≠ i') (j : ι₂) :
    b i j ⬝ᵥ b i' j = 1 := by
  have h' := hb.dot_eq i j i' j
  rwa [if_neg h, if_pos rfl] at h'

theorem dot_zero (hb : IsBetaGrid b) {i i' : ι₁} {j j' : ι₂} (hi : i ≠ i') (hj : j ≠ j') :
    b i j ⬝ᵥ b i' j' = 0 := by
  have h' := hb.dot_eq i j i' j'
  rwa [if_neg hi, if_neg hj] at h'

/-- Value trichotomy for grid entries (Coq `norm_lit`). -/
theorem val (hb : IsBetaGrid b) (i : ι₁) (j : ι₂) (ω : Ω) :
    b i j ω = -1 ∨ b i j ω = 0 ∨ b i j ω = 1 :=
  val_of_norm3 (hb.norm3 i j) ω

/-- The transposed grid (the Coq `tr_model`, W₁/W₂ symmetry). -/
theorem transpose (hb : IsBetaGrid b) : IsBetaGrid (fun j i => b i j) where
  even_card₁ := hb.even_card₂
  even_card₂ := hb.even_card₁
  card_ne := hb.card_ne.symm
  one_lt_card₁ := hb.one_lt_card₂
  one_lt_card₂ := hb.one_lt_card₁
  dot_eq j₁ i₁ j₂ i₂ := by rw [hb.dot_eq i₁ j₁ i₂ j₂, mul_comm]

/-! ### Peterfalvi (3.5.2): entries on a line share exactly one coordinate, with equal sign

Coq: `unsat_J` (`|= & x1 in b11 & -x1 in b21` — an opposite-sign shared component is
impossible) and `unsat_II` (`|= & x1, x2 in b11 & x1, x2 in b21` — two shared components
are impossible), plus the `L` test built from them.  The proof: two norm-3 vectors with dot
product `1` overlap in pattern `{+1}` or `{+1, +1, −1}`; the latter would make them differ
at exactly one coordinate, forcing `⟪f, h⟫ ≡ ⟪g, h⟫ (mod 2)` against every entry `h`, but a
mate entry (same row as one, different column) gives dot products `1` and `0`. -/

/-- Two entries of a common column share **exactly one** coordinate, with the **same
sign**: there is `a` with `b i j a = b i' j a ≠ 0` and all other coordinatewise products
zero.  Peterfalvi (3.5.2); replaces Coq `unsat_J`/`unsat_II`/`L`. -/
theorem exists_share_col (hb : IsBetaGrid b) {i i' : ι₁} (hne : i ≠ i') (j : ι₂) :
    ∃ a : Ω, b i j a = b i' j a ∧ b i j a ≠ 0 ∧
      ∀ ω : Ω, ω ≠ a → b i j ω * b i' j ω = 0 := by
  obtain ⟨j', hj'⟩ := Fintype.exists_ne_of_one_lt_card hb.one_lt_card₂ j
  have h3f : b i j ⬝ᵥ b i j = 3 := hb.norm3 i j
  have h3g : b i' j ⬝ᵥ b i' j = 3 := hb.norm3 i' j
  have hfh : b i j ⬝ᵥ b i j' = 1 := hb.dot_row i hj'.symm
  have hgh : b i' j ⬝ᵥ b i j' = 0 := hb.dot_zero hne.symm hj'.symm
  have hvf := val_of_norm3 h3f
  have hvg := val_of_norm3 h3g
  obtain ⟨a₁, a₂, a₃, h12, h13, h23, hv1, hv2, hv3⟩ := exists_triple_of_norm3 h3f
  have hf0 : ∀ ω, ω ≠ a₁ → ω ≠ a₂ → ω ≠ a₃ → b i j ω = 0 :=
    fun ω => eq_zero_of_norm3 h3f h12 h13 h23 hv1 hv2 hv3
  have hexp : b i j a₁ * b i' j a₁ + b i j a₂ * b i' j a₂ + b i j a₃ * b i' j a₃ = 1 :=
    (dotProduct_eq_of_support₃ h12 h13 h23 hf0).symm.trans (hb.dot_col hne j)
  -- Case A: single shared coordinate `x`, products vanish at the other two.
  have caseA : ∀ x y z : Ω, x ≠ y → x ≠ z → y ≠ z →
      (∀ ω, ω ≠ x → ω ≠ y → ω ≠ z → b i j ω = 0) →
      b i j x * b i' j x = 1 → b i j y * b i' j y = 0 → b i j z * b i' j z = 0 →
      ∃ a : Ω, b i j a = b i' j a ∧ b i j a ≠ 0 ∧
        ∀ ω : Ω, ω ≠ a → b i j ω * b i' j ω = 0 := by
    intro x y z hxy hxz hyz hzero hx1 hy0 hz0
    have hx0 : b i j x ≠ 0 := fun h0 => by rw [h0, zero_mul] at hx1; omega
    refine ⟨x, (eq_of_mul_eq_one (hvf x) hx1).symm, hx0, fun ω hω => ?_⟩
    by_cases hωy : ω = y
    · rw [hωy]; exact hy0
    by_cases hωz : ω = z
    · rw [hωz]; exact hz0
    rw [hzero ω hω hωy hωz, zero_mul]
  -- Case B: the `{+1, +1, -1}` overlap is impossible (parity against the mate `b i j'`).
  have caseB : ∀ x y z : Ω, x ≠ y → x ≠ z → y ≠ z →
      (∀ ω, ω ≠ x → ω ≠ y → ω ≠ z → b i j ω = 0) →
      b i j x * b i' j x = -1 → b i j y * b i' j y = 1 → b i j z * b i' j z = 1 →
      False := by
    intro x y z hxy hxz hyz hzero hx hy hz
    have hgx : b i' j x ≠ 0 := fun h0 => by rw [h0, mul_zero] at hx; omega
    have hgy : b i' j y ≠ 0 := fun h0 => by rw [h0, mul_zero] at hy; omega
    have hgz : b i' j z ≠ 0 := fun h0 => by rw [h0, mul_zero] at hz; omega
    have hagree : ∀ ω, ω ≠ x → b i j ω = b i' j ω := by
      intro ω hωx
      by_cases hωy : ω = y
      · rw [hωy]; exact (eq_of_mul_eq_one (hvf y) hy).symm
      by_cases hωz : ω = z
      · rw [hωz]; exact (eq_of_mul_eq_one (hvf z) hz).symm
      rw [hzero ω hωx hωy hωz,
        eq_zero_of_norm3 h3g hxy hxz hyz hgx hgy hgz hωx hωy hωz]
    have hd : b i j ⬝ᵥ b i j' - b i' j ⬝ᵥ b i j' =
        (b i j x - b i' j x) * b i j' x := dotProduct_sub_of_eq_off hagree
    rw [hfh, hgh, sub_zero] at hd
    have hgxv : b i' j x = -b i j x := eq_neg_of_mul_eq_neg_one (hvf x) hx
    rw [hgxv, sub_neg_eq_add] at hd
    have hhx := hvf x
    have hhv := val_of_norm3 (hb.norm3 i j') x
    rcases hhx with h | h | h <;> rw [h] at hd <;> omega
  rcases sum_three_eq_one_cases (mul_val_cases (hvf a₁) (hvg a₁))
      (mul_val_cases (hvf a₂) (hvg a₂)) (mul_val_cases (hvf a₃) (hvg a₃)) hexp with
    ⟨p, q, r⟩ | ⟨p, q, r⟩ | ⟨p, q, r⟩ | ⟨p, q, r⟩ | ⟨p, q, r⟩ | ⟨p, q, r⟩
  · exact caseA a₁ a₂ a₃ h12 h13 h23 hf0 p q r
  · exact caseA a₂ a₁ a₃ h12.symm h23 h13 (fun ω h1 h2 h3 => hf0 ω h2 h1 h3) p q r
  · exact caseA a₃ a₁ a₂ h13.symm h23.symm h12 (fun ω h1 h2 h3 => hf0 ω h2 h3 h1) p q r
  · exact absurd (caseB a₁ a₂ a₃ h12 h13 h23 hf0 p q r) not_false
  · exact absurd (caseB a₂ a₁ a₃ h12.symm h23 h13
      (fun ω h1 h2 h3 => hf0 ω h2 h1 h3) p q r) not_false
  · exact absurd (caseB a₃ a₁ a₂ h13.symm h23.symm h12
      (fun ω h1 h2 h3 => hf0 ω h2 h3 h1) p q r) not_false

/-- Row version of `exists_share_col` (via the transposed grid). -/
theorem exists_share_row (hb : IsBetaGrid b) (i : ι₁) {j j' : ι₂} (hne : j ≠ j') :
    ∃ a : Ω, b i j a = b i j' a ∧ b i j a ≠ 0 ∧
      ∀ ω : Ω, ω ≠ a → b i j ω * b i j' ω = 0 :=
  hb.transpose.exists_share_col hne i

/-- If two entries of a common column are both nonzero at `a`, then `a` *is* their unique
shared coordinate: the values agree and all other coordinatewise products vanish.  The
"reverse" reading of (3.5.2); the Coq `L` test specializes to this. -/
theorem share_col_eq (hb : IsBetaGrid b) {i i' : ι₁} (hne : i ≠ i') {j : ι₂} {a : Ω}
    (ha : b i j a ≠ 0) (ha' : b i' j a ≠ 0) :
    b i j a = b i' j a ∧ ∀ ω : Ω, ω ≠ a → b i j ω * b i' j ω = 0 := by
  obtain ⟨x, hx1, hx2, hx3⟩ := hb.exists_share_col hne j
  by_cases hax : a = x
  · rw [hax]; exact ⟨hx1, hx3⟩
  · exact absurd (hx3 a hax) (mul_ne_zero ha ha')

/-- Row version of `share_col_eq`. -/
theorem share_row_eq (hb : IsBetaGrid b) (i : ι₁) {j j' : ι₂} (hne : j ≠ j') {a : Ω}
    (ha : b i j a ≠ 0) (ha' : b i j' a ≠ 0) :
    b i j a = b i j' a ∧ ∀ ω : Ω, ω ≠ a → b i j ω * b i j' ω = 0 :=
  hb.transpose.share_col_eq hne ha ha'

end IsBetaGrid

end PF3Engine
