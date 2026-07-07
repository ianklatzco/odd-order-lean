# Name map (Coq → Lean)

Tracks the correspondence between MathComp `odd-order` identifiers and their
Lean/Mathlib ports, per `docs/superpowers/plans/2026-07-06-odd-order-port.md` §5 (D1).

| Coq | Lean | File |
|---|---|---|
| `stripped_Odd_Order` | `odd_order_solvable` | `OddOrder/Basic.lean` |
| `pnat` (`π.-nat n`) | `Nat.IsPiNumber` | `OddOrder/Mathlib/GroupTheory/PiGroup.lean` |
| `pgroup` (`π.-group H`) | `Subgroup.IsPiGroup` | `OddOrder/Mathlib/GroupTheory/PiGroup.lean` |
| `pHall` (`π.-Hall(G) H`, for `G := ⊤`) | `Subgroup.IsHall` | `OddOrder/Mathlib/GroupTheory/Hall.lean` |
| `minnormal` (with ambient group `G`) | `Subgroup.IsMinNormal` | `OddOrder/Mathlib/GroupTheory/ChiefFactor.lean` |
| `abelem` (`p.-abelem A`) | `IsElementaryAbelian` | `OddOrder/Mathlib/GroupTheory/ChiefFactor.lean` |
| `minnormal_solvable` / `minnormal_solvable_abelem` | `Subgroup.IsMinNormal.isElementaryAbelian` | `OddOrder/Mathlib/GroupTheory/ChiefFactor.lean` |
| `abelem_pgroup` | `IsElementaryAbelian.isPGroup` | `OddOrder/Mathlib/GroupTheory/ChiefFactor.lean` |
| `pnat_coprime` | `Nat.IsPiNumber.coprime` | `OddOrder/Mathlib/GroupTheory/PiGroup.lean` |
| `Hall_exists` | `Subgroup.exists_isHall` | `OddOrder/Mathlib/GroupTheory/Hall.lean` |
| `SchurZassenhaus_trans_sol` | `Subgroup.IsComplement'.exists_conj_of_coprime` | `OddOrder/Mathlib/GroupTheory/SchurZassenhaus.lean` |
| `Hall_trans` | `Subgroup.isHall_conj` | `OddOrder/Mathlib/GroupTheory/Hall.lean` |
| `Hall_superset` | `Subgroup.IsPiGroup.le_isHall_conj` | `OddOrder/Mathlib/GroupTheory/Hall.lean` |
