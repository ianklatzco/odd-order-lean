/-
Copyright (c) 2026 Ian Klatzco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Klatzco
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The Odd Order Theorem (Feit–Thompson)

Port of the Coq/MathComp formalization in `math-comp/odd-order`
(Gonthier et al., 2012) to Lean 4 / Mathlib.

The target statement corresponds to `stripped_odd_order_theorem.v`:
every finite group of odd order is solvable.
-/

/-- **The Odd Order Theorem** (Feit–Thompson, 1963).
Every finite group of odd order is solvable. -/
theorem odd_order_solvable (G : Type*) [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) : IsSolvable G := by
  sorry
