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
| `quotient_pHall` | `Subgroup.IsHall.map_mk'` | `OddOrder/Mathlib/GroupTheory/Hall.lean` |
| `pHall_subl` (approximate) | `Subgroup.IsHall.subgroupOf` | `OddOrder/Mathlib/GroupTheory/Hall.lean` |
| `sub_pHall` | `Subgroup.IsHall.eq_of_le` | `OddOrder/Mathlib/GroupTheory/Hall.lean` |
| `pHall_Sylow` / `Sylow_Hall` (approximate) | `Sylow.isHall` | `OddOrder/Mathlib/GroupTheory/Hall.lean` |
| `pHall_coprime` (approximate) | `Subgroup.IsHall.coprime` | `OddOrder/Mathlib/GroupTheory/Hall.lean` |
| `pgroupM` (for the product with a normal subgroup; product form differs — MathComp states it for the product set `H * N`, Lean for the join `H ⊔ N`) | `Subgroup.Normal.isPiGroup_sup` | `OddOrder/Mathlib/GroupTheory/PiGroup.lean` |
| `pcore` (`'O_pi(G)`) | `Subgroup.pcore` | `OddOrder/Mathlib/GroupTheory/PiGroup.lean` |
| `pcore_pgroup` | `Subgroup.pcore_isPiGroup` | `OddOrder/Mathlib/GroupTheory/PiGroup.lean` |
| `pcore_normal` | `Subgroup.pcore_normal` | `OddOrder/Mathlib/GroupTheory/PiGroup.lean` |
| `pcore_char` | `Subgroup.pcore_characteristic` | `OddOrder/Mathlib/GroupTheory/PiGroup.lean` |
| `pcore_max` | `Subgroup.pcore_max` | `OddOrder/Mathlib/GroupTheory/PiGroup.lean` |
| `A \subset 'N(H)` (A-invariance, external form) | `Subgroup.SMulInvariant` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `[~: H, A]` (commutator with an action, external form) | `Subgroup.actionCommutator` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `'C_G(A)` / `gacent` (external action) | `FixedPoints.subgroup` | Mathlib (`Mathlib/GroupTheory/GroupAction/Defs.lean`) |
| `coprime_quotient_cent` | `coprime_fixedPoints_quotient_surjective`, `coprime_fixedPoints_quotient_eq` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `coprime_cent_prod` | `coprime_cent_prod` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `coprime_commGid` | `coprime_commutator_eq` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `coprime_abelian_cent_dprod` | `coprime_abelian_cent_dprod` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `coprime_Hall_exists` | `coprime_hall_exists` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `coprime_Hall_trans` | `coprime_hall_trans` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `p_natP` (`{p}`-number is a `p`-power) | `Nat.IsPiNumber.exists_eq_pow` | `OddOrder/Mathlib/GroupTheory/PiGroup.lean` |
| `Fitting` (`'F(G)`) | `fitting` | `OddOrder/Mathlib/GroupTheory/Fitting.lean` |
| `Fitting_max` | `fitting_max` | `OddOrder/Mathlib/GroupTheory/Fitting.lean` |
| `Fitting_char` | `fitting_characteristic` | `OddOrder/Mathlib/GroupTheory/Fitting.lean` |
| `Fitting_normal` | `fitting_normal` | `OddOrder/Mathlib/GroupTheory/Fitting.lean` |
| `Fitting_nil` (Fitting's theorem) | `fitting_isNilpotent` | `OddOrder/Mathlib/GroupTheory/Fitting.lean` |
| `FittingEgen` (join-of-`'O_p(G)` form) | `fitting_eq_iSup_pcore` | `OddOrder/Mathlib/GroupTheory/Fitting.lean` |
| `cent_sub_Fitting` (B&G 1.3) | `fitting_centralizer_le` | `OddOrder/Mathlib/GroupTheory/Fitting.lean` |
| `minnormal` existence below a normal subgroup (no single MathComp lemma) | `Subgroup.exists_isMinNormal_le` | `OddOrder/Mathlib/GroupTheory/ChiefFactor.lean` |
| `classfun` / `'CF(G)` | `ClassFunction` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `'CF(G, A)` | `ClassFunction.supportedOn` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `cfdot` / `'[phi, psi]` | `ClassFunction.cfInner`, notation `⟪φ, ψ⟫_[G]` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `cfdotC` (`'[phi, psi] = ('[psi, phi])^*`) | `ClassFunction.cfInner_conj_symm` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `dim_cfun` (`\dim 'CF(G) = #|classes G|`; approximate — the previously listed `cfun1`/`cfuni` are the constant-1 and indicator class functions, not this dimension count, and are not ported yet) | `ClassFunction.finrank_classFunction` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `char_inv` (`chi g^-1 = (chi g)^*`) | `Representation.char_inv`, `FDRep.char_inv` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `cfRepr` (character of a `G`-module) | `MonoidAlgebra.moduleCharacter` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `irr G` | `Irr` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `cfdot_irr` (first orthogonality, `'[chi_i, chi_j] = (i == j)%:R`) | `Irr.cfInner_eq` (also `MonoidAlgebra.cfInner_moduleCharacter`, `FDRep.cfInner_classFunction`) | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `free_irr` (irreducible characters are linearly independent) | `Irr.linearIndependent` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `NirrE` / `card_irr` (`#|irr G| = #|classes G|`) | `Irr.card_eq_card_conjClasses` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `irr_basis` (irreducible characters are a basis of `'CF(G)`) | `Irr.basis` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `cfun_sum_cfdot` (`phi = \sum_i '[phi, 'chi_i] *: 'chi_i`) | `ClassFunction.eq_sum_cfInner_smul` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `second_orthogonality_relation` | `Irr.second_orthogonality` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `class_formula` (single class: `#|g ^: G| * #|'C_G[g]| = #|G|`) | `ConjClasses.nat_card_carrier_mul_card_centralizer` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| (center of group algebra ↔ class functions; MathComp `gring` material) | `MonoidAlgebra.mem_center_iff`, `MonoidAlgebra.centerEquivClassFunction`, `MonoidAlgebra.finrank_center` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |

Future work (not ported yet): `coprime_Hall_subset` and the Glauberman-lemma
variants of the coprime-action suite (`glauberman_...`, `ext_coprime_quotient_cent`
for non-solvable kernels) — see the scope note in
`OddOrder/Mathlib/GroupTheory/CoprimeAction.lean`.

Future work (not ported yet): `coprime_abelian_gen_cent1` (B&G 1.16: if `A` is
abelian noncyclic, normalizes `G`, and `gcd(|G|,|A|) = 1`, then `G` is generated by
the centralizers `C_G(a)` for `a ∈ A \ {1}`) and its variant
`coprime_abelian_gen_cent` — see the scope note in
`OddOrder/Mathlib/GroupTheory/CoprimeAction.lean`.
