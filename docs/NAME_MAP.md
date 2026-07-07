# Name map (Coq → Lean)

Tracks the correspondence between MathComp `odd-order` identifiers and their
Lean/Mathlib ports, per `docs/superpowers/plans/2026-07-06-odd-order-port.md` §5 (D1).

| Coq | Lean | File |
|---|---|---|
| `stripped_Odd_Order` | `odd_order_solvable` | `OddOrder/Basic.lean` |
| `pnat` (`π.-nat n`) | `Nat.IsPiNumber` | `OddOrder/Mathlib/GroupTheory/PiGroup.lean` |
| `pgroup` (`π.-group H`) | `Subgroup.IsPiGroup` | `OddOrder/Mathlib/GroupTheory/PiGroup.lean` |
| `pHall` (`π.-Hall(G) H`, for `G := ⊤`) | `Subgroup.IsHall` | `OddOrder/Mathlib/GroupTheory/Hall.lean` |
