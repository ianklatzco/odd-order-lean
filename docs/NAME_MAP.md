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
| `A \subset 'N(H)` (A-invariance, internal form; canonical spelling) | `A ≤ normalizer (H : Set G)`; bridges `Subgroup.subgroupOf_smulInvariant_iff`, `Subgroup.le_normalizer_iff_forall_map_conj_eq` | `OddOrder/Mathlib/GroupTheory/CoprimeActionInternal.lean` |
| `[~: H, A]` (internal action commutator dictionary) | `Subgroup.actionCommutator_conjAction_eq`, `Subgroup.actionCommutator_conjAction_map_subtype` | `OddOrder/Mathlib/GroupTheory/CoprimeActionInternal.lean` |
| `'C_H(A)` (internal fixed-point dictionary) | `Subgroup.fixedPoints_conjAction_eq` (`= (centralizer ↑A ⊓ H).subgroupOf H`), `Subgroup.mem_fixedPoints_conjAction_iff`, `Subgroup.fixedPoints_conjAction_map_subtype` | `OddOrder/Mathlib/GroupTheory/CoprimeActionInternal.lean` |
| `commg_subl`-for-normalizing-`A` (`[~: H, A] \subset H`) | `Subgroup.commutator_le_of_le_normalizer` (alias of Mathlib's `le_normalizer_iff_commutator_le_left`) | `OddOrder/Mathlib/GroupTheory/CoprimeActionInternal.lean` |
| `[~: H, A]` (commutator with an action, external form) | `Subgroup.actionCommutator` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `'C_G(A)` / `gacent` (external action) | `FixedPoints.subgroup` | Mathlib (`Mathlib/GroupTheory/GroupAction/Defs.lean`) |
| `coprime_quotient_cent` | `coprime_fixedPoints_quotient_surjective`, `coprime_fixedPoints_quotient_eq` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `coprime_quotient_cent` (internal form) | `coprime_fixedPoints_quotient_surjective_internal`, `coprime_fixedPoints_quotient_eq_internal` | `OddOrder/Mathlib/GroupTheory/CoprimeActionInternal.lean` |
| `coprime_cent_prod` | `coprime_cent_prod` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `coprime_cent_prod` (internal form) | `coprime_cent_prod_internal` (join), `coprime_cent_prod_set_internal` (setwise product) | `OddOrder/Mathlib/GroupTheory/CoprimeActionInternal.lean` |
| `coprime_commGid` | `coprime_commutator_eq` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `coprime_commGid` (internal form) | `coprime_commutator_eq_internal` | `OddOrder/Mathlib/GroupTheory/CoprimeActionInternal.lean` |
| `coprime_abelian_cent_dprod` | `coprime_abelian_cent_dprod` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `coprime_Hall_exists` | `coprime_hall_exists` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `coprime_Hall_exists` (internal form) | `coprime_hall_exists_internal` | `OddOrder/Mathlib/GroupTheory/CoprimeActionInternal.lean` |
| `coprime_Hall_trans` | `coprime_hall_trans` | `OddOrder/Mathlib/GroupTheory/CoprimeAction.lean` |
| `coprime_Hall_trans` (internal form) | `coprime_hall_trans_internal` | `OddOrder/Mathlib/GroupTheory/CoprimeActionInternal.lean` |
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
| `cfun_ring` (class functions form a commutative ring under pointwise `*`, unit `1`) | `ClassFunction.instCommRing`, `ClassFunction.instAlgebra` | `OddOrder/Mathlib/RepresentationTheory/CharacterArith.lean` |
| `cfun1` / `irr1` (the trivial character) | `Irr.one` | `OddOrder/Mathlib/RepresentationTheory/CharacterArith.lean` |
| `character` / `is_char` (a class function that is an ℕ-combination of `Irr`) | `ClassFunction.IsChar` | `OddOrder/Mathlib/RepresentationTheory/CharacterArith.lean` |
| `irr1_deg` (degree `chi 1` is a natural number) | `Irr.exists_degree` | `OddOrder/Mathlib/RepresentationTheory/CharacterArith.lean` |
| `irr1_gt0` (`0 < chi 1`) | `Irr.exists_degree` (the positivity conjunct) | `OddOrder/Mathlib/RepresentationTheory/CharacterArith.lean` |
| `sum_irr1_sq`-shaped corollary of second orthogonality (exact MathComp name unconfirmed at port time) | `Irr.sum_sq_degree` | `OddOrder/Mathlib/RepresentationTheory/CharacterArith.lean` |
| `cfRes` / `'Res[H] phi` (restriction of a class function to a subgroup) | `ClassFunction.res` | `OddOrder/Mathlib/RepresentationTheory/Induced.lean` |
| `cfInd` / `'Ind[G] phi` (induction of a class function, averaging formula) | `ClassFunction.ind` | `OddOrder/Mathlib/RepresentationTheory/Induced.lean` |
| `cfdot_cfInd` / `Frobenius_reciprocity` | `ClassFunction.cfInner_ind_eq_cfInner_res` (flipped form: `ClassFunction.cfInner_ind_right_eq_cfInner_res_left`) | `OddOrder/Mathlib/RepresentationTheory/Induced.lean` |
| `cfRes_char`-shaped (restriction of a character is a character) | `ClassFunction.IsChar.res` | `OddOrder/Mathlib/RepresentationTheory/Induced.lean` |
| `cfInd_char`-shaped (induction of a character is a character) | `ClassFunction.IsChar.ind` | `OddOrder/Mathlib/RepresentationTheory/Induced.lean` |
| `gring` class-sum basis vectors (exact name unconfirmed) | `MonoidAlgebra.classSum` | `OddOrder/Mathlib/RepresentationTheory/ClassSum.lean` |
| (single-sum characterization of the class sum; no separate Coq name) | `MonoidAlgebra.classSum_eq_sum_single` | `OddOrder/Mathlib/RepresentationTheory/ClassSum.lean` |
| `gring` basis of the group-ring center (exact name unconfirmed) | `MonoidAlgebra.classSumBasis` (via `MonoidAlgebra.classFunctionIndicatorBasis`) | `OddOrder/Mathlib/RepresentationTheory/ClassSum.lean` |
| `gring_classM_coef` (structure constants; also the counting formula `gring_classM_coef_sum_eq` — per the BGappendixC entry of `docs/audit/survey-digest.md`) | `MonoidAlgebra.classMulCoeff`, `MonoidAlgebra.classMulCoeff_eq`, `MonoidAlgebra.classSum_mul` | `OddOrder/Mathlib/RepresentationTheory/ClassSum.lean` |
| `χ(g)` is an algebraic integer (`Aint_char`-shaped, exact name unconfirmed) | `Irr.isIntegral_apply` (engine: `Module.End.trace_eq_sum_zeta_pow_mul_natCast`, refactored out of `Module.End.trace_pow_pred_eq_star_trace`) | `OddOrder/Mathlib/RepresentationTheory/CharacterArith.lean` (engine in `ClassFunction.lean`) |
| central character `ω_χ` (`gring`-mode material, exact name unconfirmed) | `Irr.omega`, `Irr.omega_eq` (closed formula), `Irr.omega_mul` (structure constants), `Irr.isIntegral_omega` | `OddOrder/Mathlib/RepresentationTheory/CharacterArith.lean` |
| `dvd_irr1_cardG` (`chi 1 ∣ #G`) | `Irr.exists_degree_dvd_card` | `OddOrder/Mathlib/RepresentationTheory/CharacterArith.lean` |
| `zchar S A` / `'Z[S, A]`, `'Z[S]` (virtual-character lattice; exact Coq identifier for the predicate unconfirmed) | `ClassFunction.VirtualChar`, scoped notation `Z[S, A]` / `Z[S]` (Lean rejects atoms starting with a single `'`, so the MathComp apostrophe is dropped) | `OddOrder/Mathlib/RepresentationTheory/VirtualChar.lean` |
| `zchar_split` (the span/support split of `'Z[S, A]` membership; usage PFsection1.v:208) | `ClassFunction.mem_virtualChar_iff`, `ClassFunction.mem_virtualChar_univ_iff` | `OddOrder/Mathlib/RepresentationTheory/VirtualChar.lean` |
| `rpredD`/`rpredN`/`rpredB` applied to `zchar` (generic closure; usage e.g. PFsection1.v:208) | `ClassFunction.IsVirtualChar.add`/`.neg`/`.sub` | `OddOrder/Mathlib/RepresentationTheory/VirtualChar.lean` |
| `'Z[irr G]` (the `Irr`-indexed lattice) | `ClassFunction.virtualCharIrr`, predicate form `ClassFunction.IsVirtualChar` (equivalence: `ClassFunction.isVirtualChar_iff_mem_virtualCharIrr`) | `OddOrder/Mathlib/RepresentationTheory/VirtualChar.lean` |
| integrality of `'[phi, chi]` for `phi ∈ 'Z[irr G]` (the coefficient half of `zchar_expansion`; exact name unconfirmed) | `ClassFunction.IsVirtualChar.cfInner_mem_intCast` (coefficient extraction: `ClassFunction.cfInner_eq_of_eq_sum_intCast_smul`) | `OddOrder/Mathlib/RepresentationTheory/VirtualChar.lean` |
| `vchar_norm1P` (norm-1 virtual character is `±chi`) | `ClassFunction.IsVirtualChar.exists_eq_or_eq_neg_of_cfInner_self_eq_one` | `OddOrder/Mathlib/RepresentationTheory/VirtualChar.lean` |
| `vchar_norm2` (norm-2 virtual character vanishing at `1`, i.e. in `'Z[irr G, G^#]` → pure difference `'chi_i - 'chi_j`; the shape verified at every PF call site: PFsection1.v:152–153, 217, 233; PFsection5.v:1597) | `ClassFunction.IsVirtualChar.exists_sub_of_cfInner_self_eq_two` (four-pattern variant under the weaker `⟪φ, 1⟫ = 0`: `ClassFunction.IsVirtualChar.exists_sub_or_add_of_cfInner_self_eq_two`; shared engine: `ClassFunction.IsVirtualChar.exists_sign_smul_add_of_cfInner_self_eq_two`) | `OddOrder/Mathlib/RepresentationTheory/VirtualChar.lean` |
| `char_vchar` (a character is a virtual character; exact name unconfirmed) | `ClassFunction.IsChar.isVirtualChar`, `ClassFunction.IsChar.mem_virtualCharIrr` | `OddOrder/Mathlib/RepresentationTheory/VirtualChar.lean` |
| (virtual character whose `Irr`-coefficients all have nonnegative real part is a character; no confirmed Coq name) | `ClassFunction.IsVirtualChar.isChar_of_forall_cfInner_nonneg` | `OddOrder/Mathlib/RepresentationTheory/VirtualChar.lean` |
| `vcharP` (virtual character ↔ difference of two characters; usage PFsection1.v:639) | `ClassFunction.IsVirtualChar.exists_isChar_sub` (converse: `ClassFunction.IsChar.sub_isVirtualChar`; iff: `ClassFunction.isVirtualChar_iff_exists_isChar_sub`) | `OddOrder/Mathlib/RepresentationTheory/VirtualChar.lean` |
| nonvanishing dichotomy (analytic crux of Burnside; likely in mathcomp's `character/integral_char.v` — verify on first mathcomp checkout) | `Irr.eq_zero_or_norm_eq` | `OddOrder/Mathlib/RepresentationTheory/Burnside.lean` |
| character kernel (`cfker`) | `Irr.ker`, `Irr.mem_ker_iff`, `Irr.eq_one_of_ker_eq_top` (promoted from `Burnside.lean` with M3 Task 4, together with the eigen-projection kit and the scalar-action lemma `Module.End.eq_smul_one_of_trace_eq_mul_finrank`; statements unchanged) | `OddOrder/Mathlib/RepresentationTheory/CharacterArith.lean` |
| kernel-intersection separation (column of the character table at `(g, 1)`; no single confirmed Coq name) | `Irr.exists_ne_one_apply_ne` | `OddOrder/Mathlib/RepresentationTheory/CharacterArith.lean` |
| class-size lemma (likely in mathcomp's `character/integral_char.v` — verify on first mathcomp checkout; note the odd-order checkout's `Burnside_normal_complement` in `BGsection1.v` is the *normal p-complement* theorem, a different result) | `not_isSimpleGroup_of_conjClasses_card_eq_prime_pow` | `OddOrder/Mathlib/RepresentationTheory/Burnside.lean` |
| **`p^a q^b` solvability** (headline; likely proved in mathcomp's `character/integral_char.v` — verify on first mathcomp checkout. It is *not* in the odd-order checkout itself: the only Burnside-named result there, `BGsection1.v:846 Burnside_normal_complement`, is the normal p-complement theorem) | **`burnside_solvable`** | `OddOrder/Mathlib/RepresentationTheory/Burnside.lean` |
| `cfConjC` (`phi^*%CF`, valuewise complex conjugation; `classfun.v`) | `ClassFunction.conjC` (named `conjC`, not `conj`: `ClassFunction.conj_apply` is already the conjugation-invariance lemma) | `OddOrder/Mathlib/RepresentationTheory/CharAut.lean` |
| `cfConjCK` (conjugation is an involution; `classfun.v`) | `ClassFunction.conjC_conjC` | `OddOrder/Mathlib/RepresentationTheory/CharAut.lean` |
| `conjC_Iirr` / `conjC_IirrK` (conjugation permutes `Iirr`; `character.v`) | `Irr.conj`, `Irr.conj_conj`, packaged permutation `Irr.conjEquiv` | `OddOrder/Mathlib/RepresentationTheory/CharAut.lean` |
| (`chi^*%CF = chi ↔ chi` real-valued — the rewriting underlying PF (1.1) `odd_eq_conj_irr1`; no single Coq identifier) | `Irr.conj_eq_self_iff` | `OddOrder/Mathlib/RepresentationTheory/CharAut.lean` |
| `cfAut u` restricted to the coprime power automorphisms (the only `cfAut` instances PF1 consumes; `classfun.v`) | `ClassFunction.powTwist` (`φ^(u) g := φ (g ^ u)`; the valuewise-`σ` description is recovered by `Irr.apply_pow`) | `OddOrder/Mathlib/RepresentationTheory/CharAut.lean` |
| `cfAut_irr` (the `σ`-image of an irreducible character is irreducible, via `map_repr`; `character.v`, `mx_representation.v`) | `MonoidAlgebra.exists_isSimpleModule_moduleCharacter_comp` (stated for any `σ : ℂ ≃+* ℂ`) | `OddOrder/Mathlib/RepresentationTheory/CharAut.lean` |
| `aut_Iirr` (the `cfAut` permutation of `Iirr`; `character.v`) | `Irr.powTwist` (coprime-to-`Monoid.exponent G` hypothesis), `Irr.powTwist_bijective`, inverse-twist cancellation `Irr.powTwist_powTwist` | `OddOrder/Mathlib/RepresentationTheory/CharAut.lean` |
| `Qn_aut_exists`-style automorphism production (PFsection1.v, for (1.9); over `algC` no extension step is needed) | `Complex.exists_ringEquiv_pow_of_coprime` (cyclotomic Galois automorphism extended to `ℂ` along a transcendence basis) | `OddOrder/Mathlib/RepresentationTheory/CharAut.lean` |
| `cfun_onS` (support monotonicity of `'CF(G, A)`; `classfun.v`) | `ClassFunction.supportedOn_mono` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `cfunD1E` (`phi \in 'CF(G, G^#) = (phi 1 == 0)`; `classfun.v`) | `ClassFunction.mem_supportedOn_compl_one` (the `G^#` spelling is `({1}ᶜ : Set G)`) | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `cfdotEl`-shaped (inner-product sum restricted to the support; `classfun.v`) | `ClassFunction.cfInner_eq_sum_filter_of_mem_supportedOn` | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `cfdot_complement`-shaped (disjointly supported class functions are orthogonal; `classfun.v`) | `ClassFunction.cfInner_eq_zero_of_supportedOn_disjoint` (also the congruence form `ClassFunction.cfInner_congr_right_of_mem_supportedOn`) | `OddOrder/Mathlib/RepresentationTheory/ClassFunction.lean` |
| `cfRes_on`-shaped (restriction and supports; `classfun.v`) | `ClassFunction.res_mem_supportedOn` | `OddOrder/Mathlib/RepresentationTheory/Induced.lean` |
| `cfInd_on` (`phi \in 'CF(H, A) -> 'Ind[G] phi \in 'CF(G, class_support A G)`; `classfun.v`) | `ClassFunction.ind_mem_supportedOn_conjugatesOfSet` | `OddOrder/Mathlib/RepresentationTheory/Induced.lean` |
| `class_support A G` (`{a ^ g}`; `fingroup.v`) | Mathlib `Group.conjugatesOfSet` (for the full-`G` conjugation the PF supports use) | Mathlib (`Mathlib/Algebra/Group/Subgroup/Basic.lean`) |
| `cfConjg` / `(phi ^ y)%CF` (`inertia.v`) | `ClassFunction.conjg` — **inverse convention**: `conjg φ g = (phi ^ g⁻¹)%CF`, i.e. `(conjg φ g) h = φ (g⁻¹ h g)`, a left action per the M6 Task 1 binding decision; orbits/stabilizers coincide | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `cfConjgE` (`inertia.v`) | `ClassFunction.conjg_apply_mk` (automorphism form: `ClassFunction.conjg_apply`) | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `cfConjgM` / `cfConjgJ1` / `cfConjgK` / `cfConjgKV` / `cfConjg1` (`inertia.v`) | `ClassFunction.conjg_mul` (left-action bracketing) / `conjg_one` / `conjg_conjg_inv` / `conjg_inv_conjg` / `conjg_apply_one` | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `conj_cfConjg` (`inertia.v`) | `ClassFunction.conjC_conjg`, `Irr.conj_conjg` | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `conj_cfInd` / `cfAut_cfRes`-for-conjugation (`classfun.v`; used in PF (1.5)(e)) | `ClassFunction.conjC_ind`, `ClassFunction.conjC_res` | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `conjg_Iirr` (with `cfConjg_irr`; `inertia.v`) | `Irr.conjg` (bijectivity: `Irr.conjg_bijective`) | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `'I_G[phi]` / `inertia` (`inertia.v`) | `ClassFunction.inertia`, `Irr.inertia` (a `Subgroup G`) | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `sub_Inertia` (`inertia.v`) | `ClassFunction.le_inertia`, `Irr.le_inertia` | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `Inertia_sub` (`inertia.v`) | (by construction: `inertia` is a `Subgroup G`) | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `normal_Inertia` (`H ⊴ 'I_G[phi]`; `inertia.v`) | Mathlib `Subgroup.Normal.subgroupOf` composed with `le_inertia` | Mathlib (`Mathlib/Algebra/Group/Subgroup/Basic.lean`) |
| `cfConjg_eqE` (`inertia.v`; right cosets there per the opposite action convention) | `Irr.conjg_eq_conjg_iff` (left-coset form `y⁻¹ * x ∈ 'I_G[θ]`) | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `sub_inertia_Res`-shaped invariance of restrictions (`inertia.v`) | `ClassFunction.conjg_res` | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `cfclass` / `('chi_t ^: G)%CF` (`inertia.v`; a duplicate-free `seq` there) | `Irr.cfclass` (a `Finset (Irr H)`) | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `cfclassP` / `cfclass_refl` / `cfclass_sym` (`inertia.v`) | `Irr.mem_cfclass_iff` / `Irr.self_mem_cfclass` / `Irr.mem_cfclass_symm` (orbit equality: `Irr.cfclass_eq_of_mem`) | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `size_cfclass` (`inertia.v`) | `Irr.card_cfclass` (`= (inertia θ).index`) | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `cfclass_Ind` (`inertia.v`) | `Irr.ind_eq_of_mem_cfclass` (engine: `ClassFunction.ind_conjg`) | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `Clifford_Res_sum_cfclass` (`inertia.v`) | `Irr.res_eq_cfInner_smul_sum_cfclass` (constituents-in-one-orbit form: `Irr.mem_cfclass_of_cfInner_res_ne_zero`) | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `cfResInd_sum_cfclass` (Peterfalvi (1.5)(a); `PFsection1.v`) | `Irr.res_ind_eq_smul_sum_cfclass`, with the `⟪res (ind θ), θ⟫`-corollary `Irr.cfInner_res_ind_self` (the (1.5)(b) norm form `cfnorm_Ind_irr` via Frobenius reciprocity lands with M6 Task 2) | `OddOrder/Mathlib/RepresentationTheory/Inertia.lean` |
| `cfIsom` (`classfun.v`) | `ClassFunction.congr` | `OddOrder/Mathlib/RepresentationTheory/CharacterTransfer.lean` |
| `isom_Iirr` (`inertia.v`) | `Irr.congr` / `Irr.congrEquiv` | `OddOrder/Mathlib/RepresentationTheory/CharacterTransfer.lean` |
| `cfMod` (`(phi %% N)%CF`) / `cfQuo` (`classfun.v`) | `ClassFunction.cfMod` / (descent) `Irr.exists_quo` | `OddOrder/Mathlib/RepresentationTheory/CharacterTransfer.lean` |
| `mod_Iirr` / `quo_Iirr` / `mod_IirrK` (`character.v`) | `Irr.mod` / `Irr.quotientKerEquiv` (kernel-containment bijection); `Irr.le_ker_mod` | `OddOrder/Mathlib/RepresentationTheory/CharacterTransfer.lean` |
| `cfResRes` / `cfIndInd` (nested subgroups; `classfun.v`) | `ClassFunction.resNested` / `ClassFunction.indNested`, with `resNested_res` / `ind_indNested` and Frobenius `cfInner_indNested_eq_cfInner_resNested` | `OddOrder/Mathlib/RepresentationTheory/CharacterTransfer.lean` |
| `lin_char` / `char_abelianP` / `lin_charM` / `lin_charX` (`character.v`) | `Irr.IsLinear` / `Irr.isLinear_of_comm` / `Irr.IsLinear.map_mul` / `Irr.IsLinear.map_pow` (root-of-unity form `IsLinear.apply_pow_orderOf_eq_one`) | `OddOrder/Mathlib/RepresentationTheory/CharacterTransfer.lean` |
| `odd_eq_conj_irr1` (Peterfalvi (1.1); `PFsection1.v`) | `PF1.odd_eq_conj_irr1` | `OddOrder/PF/Section1.lean` |
| `irr_reg_off_ker_0` (Peterfalvi (1.2); `PFsection1.v`) | `PF1.irr_reg_off_ker_0` | `OddOrder/PF/Section1.lean` |
| `equiv_restrict_compl` / `equiv_restrict_compl_ortho` (Peterfalvi (1.3); `PFsection1.v`) | `PF1.equiv_restrict_compl` / `PF1.equiv_restrict_compl_ortho` (restated over a `Basis` of `'CF(H,A)`) | `OddOrder/PF/Section1.lean` |
| `vchar_isometry_base` (+ `vchar_isometry_base3`/`base4`) (Peterfalvi (1.4); `PFsection1.v`) | `PF1.vchar_isometry_base` (+ `PF1.vchar_isometry_base3` / `PF1.vchar_isometry_base4`) (`Fin m`-indexed family) | `OddOrder/PF/Section1.lean` |
| `cfnorm_Ind_irr` (Peterfalvi (1.5)(b); `PFsection1.v`) | `PF1.cfnorm_Ind_irr` | `OddOrder/PF/Section1.lean` |
| `inertia_Ind_irr` (Peterfalvi (1.5)(b); `PFsection1.v`) | `PF1.exists_irr_ind_of_inertia_le` | `OddOrder/PF/Section1.lean` |
| `cfclass_Ind_cases` / `not_cfclass_Ind_ortho` / `cfclass_Ind_irrP` (Peterfalvi (1.5)(c); `PFsection1.v`) | `PF1.cfclass_Ind_cases` / `PF1.not_cfclass_Ind_ortho` / `PF1.cfclass_Ind_irr_iff` | `OddOrder/PF/Section1.lean` |
| `scaled_cfResInd_sum_cfclass` (Peterfalvi (1.5)(d); `PFsection1.v`) | `PF1.scaled_cfResInd_sum_cfclass` | `OddOrder/PF/Section1.lean` |
| `odd_induced_orthogonal` (Peterfalvi (1.5)(e); `PFsection1.v`) | `PF1.odd_induced_orthogonal` | `OddOrder/PF/Section1.lean` |
| `cfInd_sum_Inertia` (Peterfalvi (1.7)(a); `PFsection1.v`) | `PF1.cfInd_sum_Inertia` (Clifford correspondence bijection; Mackey-free route) | `OddOrder/PF/Section1.lean` |
| `cfInd_central_Inertia` / `cfInd_Hall_central_Inertia` (Peterfalvi (1.7)(b),(c); `PFsection1.v`) | **not ported** — need `mul_lin_irr` (tensor of reps), `cfDet`, `extend_solvable_coprime_irr` (absent); the (1.7)(a) bijection they use is done | (pending) |
| `irr1_bound_quo` (Peterfalvi (1.8); `PFsection1.v`) | `PF1.irr1_bound_quo` (stated; residual leaf `PF1.irr1_bound_charCenter` = `irr1_bound`/`cfcenter` bound is the budgeted `TODO`) | `OddOrder/PF/Section1.lean` |
| `extend_coprime_Qn_aut` (Peterfalvi (1.9)(a); `PFsection1.v`) | `PF1.extend_coprime_Qn_aut` (root-of-unity form) | `OddOrder/PF/Section1.lean` |
| `dvd_restrict_cfAut` / `make_pi_cfAut` (Peterfalvi (1.9)(b); `PFsection1.v`) | `PF1.dvd_restrict_cfAut` / `PF1.make_pi_cfAut` (uniform-in-`G0`; `cfAut u χ x` spelled `u (χ x)`) | `OddOrder/PF/Section1.lean` |
| `eqAmod` (`algnum.v`) | `PF1.eqAmod` (+ `eqAmod_refl`/`.symm`/`.trans`/`.add`/`.mul_left`/`eqAmod_sum`) — `IsIntegral ℤ`-based, global algebraic integers | `OddOrder/PF/Section1.lean` |
| `vchar_ker_mod_prim` (Peterfalvi (1.10)(a); `PFsection1.v`) | `PF1.vchar_ker_mod_prim` | `OddOrder/PF/Section1.lean` |
| `int_eqAmod_prime_prim` (Peterfalvi (1.10)(b); `PFsection1.v`) | `PF1.int_eqAmod_prime_prim` | `OddOrder/PF/Section1.lean` |
| `sol_der1_proper` (proper derived subgroup of a nontrivial solvable subgroup) | `Subgroup.commutator_lt_of_isSolvable` (promoted from a private copy in `CoprimeAction.lean` per the deferred-consolidation list; the inlined copy in `SchurZassenhaus.lean` remains) | `OddOrder/Mathlib/GroupTheory/ChiefFactor.lean` |
| `minnormal_solvable_abelem` engine (predicate-parameterized core shared with the `A`-invariant variant; no single MathComp lemma) | `Subgroup.isElementaryAbelian_of_minimal` | `OddOrder/Mathlib/GroupTheory/ChiefFactor.lean` |
| `mxabelem` dictionary, module carrier (`'rV(E)` over `'F_p`; realized as a module-language dictionary — no matrices, no row vectors) | `IsElementaryAbelian.Vec` (type synonym of `Additive ↥V` with global `AddCommGroup`/`Module (ZMod p)` instances) | `OddOrder/Mathlib/GroupTheory/AbelemRepr.lean` |
| `abelem_rV` / `rVabelem` (element-level dictionary) | `IsElementaryAbelian.toVec` (equiv `H ≃ h.Vec`) / `IsElementaryAbelian.Vec.toMul` | `OddOrder/Mathlib/GroupTheory/AbelemRepr.lean` |
| `abelem_rV_X` (approximate; scalar action is group exponentiation) | `IsElementaryAbelian.smul_toVec`, `IsElementaryAbelian.Vec.toMul_zmod_smul` | `OddOrder/Mathlib/GroupTheory/AbelemRepr.lean` |
| subgroup ↔ subspace dictionary of `mxabelem` (`abelem_rV_subg`-shaped, exact name unconfirmed) | `IsElementaryAbelian.toSubmodule` (order iso `Subgroup H ≃o Submodule (ZMod p) h.Vec`; additive half `IsElementaryAbelian.toAddSubgroup`) | `OddOrder/Mathlib/GroupTheory/AbelemRepr.lean` |
| `dim_abelemE` (approximate; with `card_pgroup`: `#|E| = p ^ 'dim E`) | `IsElementaryAbelian.card_eq_pow_finrank` | `OddOrder/Mathlib/GroupTheory/AbelemRepr.lean` |
| `abelem_repr` | `IsElementaryAbelian.conjRepr` (internal, `G` on `V ⊴ G` by conjugation through `ConjAct`); abstract-actor form `IsElementaryAbelian.repr` (composes with Task 1's `normalizerMulDistribMulAction` for `A ≤ 'N(V)` actors) | `OddOrder/Mathlib/GroupTheory/AbelemRepr.lean` |
| `abelem_rV_J` (the representation is conjugation) | `IsElementaryAbelian.conjRepr_apply_coe` (also `repr_apply_toVec`, `Vec.toMul_smul`) | `OddOrder/Mathlib/GroupTheory/AbelemRepr.lean` |
| `mxmodule` dictionary of `mxabelem` (invariant subgroups ↔ submodules) | `IsElementaryAbelian.invariantSubgroupOrderIso` (with `toSubrepresentation`, `smulInvariant_toSubmodule_symm`); conjugation case `Subgroup.smulInvariant_conjAct_iff`, `Subgroup.subgroupOf_smulInvariant_conjAct_iff` | `OddOrder/Mathlib/GroupTheory/AbelemRepr.lean` |
| `abelem_mx_irrP` (approximate; minimal normal ↔ irreducible) | `Subgroup.isMinNormal_iff_isIrreducible`, `Subgroup.isMinNormal_iff_isSimpleModule` (internal); `IsElementaryAbelian.isIrreducible_repr_iff` (abstract actor); surjective-precomposition bridge `Representation.isIrreducible_comp_iff` | `OddOrder/Mathlib/GroupTheory/AbelemRepr.lean` |
| `rker_abelem` (kernel is the centralizer) | `IsElementaryAbelian.conjRepr_ker` (`= centralizer ↑V`); subgroup-actor form `IsElementaryAbelian.repr_ker_of_le_normalizer` (`'C_A(E)` shape of BGsection1); abstract membership `IsElementaryAbelian.mem_ker_repr_iff` | `OddOrder/Mathlib/GroupTheory/AbelemRepr.lean` |
| `abelem_mx_faithful` / `kquo_mx_faithful` (approximate; `mx_faithful` of the quotient representation) | `IsElementaryAbelian.conjQuotientRepr` (representation of `G ⧸ centralizer ↑V`), `IsElementaryAbelian.conjQuotientRepr_injective` | `OddOrder/Mathlib/GroupTheory/AbelemRepr.lean` |
| `semiregular K H` (`frobenius.v`) | `Subgroup.IsSemiregular` (mem forms `IsSemiregular.eq_one_of_commute`, `isSemiregular_iff`) | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `semiprime K H` (`frobenius.v`) | `Subgroup.IsSemiprime` (mem form `IsSemiprime.commute_iff`) | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `semiregular1l` / `semiregular1r` | `Subgroup.isSemiregular_bot_left` / `Subgroup.isSemiregular_bot_right` | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `semiregular_sym` | `Subgroup.IsSemiregular.symm` | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `semiregularS` | `Subgroup.IsSemiregular.mono` | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `semiprime_regular` | `Subgroup.IsSemiprime.isSemiregular` (converse `IsSemiregular.isSemiprime` holds unconditionally; bundled `isSemiregular_iff_isSemiprime`) | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `cent_semiregular` | `Subgroup.IsSemiregular.centralizer_inf_eq_bot` | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `cent_semiprime` | `Subgroup.IsSemiprime.centralizer_inf_eq` (subgroup-restriction corollary `IsSemiprime.of_le`) | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `[Frobenius G = K ><| H]` (`Frobenius_group_with_kernel_and_complement`; the `><|` bundles `K <| G` — see the module docstring for the counterexample showing the counting facts are false without it) | `Subgroup.IsFrobenius` (Prop structure: `isComplement'`, `normal`, `ker_ne_bot`, `compl_ne_bot`, `semiregular`) | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `Frobenius_semiregularP` (B&G 3.1) | definitional: `Subgroup.IsFrobenius.mk` / `.semiregular` | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `Frobenius_context` | `Subgroup.IsFrobenius.context` (plus field projections and `ker_ne_top`/`compl_ne_top`) | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `prime_FrobeniusP` | `Subgroup.isFrobenius_iff_of_prime_card` | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `Frobenius_reg_ker` / `Frobenius_reg_compl` | `Subgroup.IsFrobenius.semiregular` / `Subgroup.IsFrobenius.semiregular_compl` | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `Frobenius_dvd_ker1` | `Subgroup.IsFrobenius.card_compl_dvd_card_ker_sub_one` | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `Frobenius_coprime` | `Subgroup.IsFrobenius.coprime_card_ker_card_compl` | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `Frobenius_ker_Hall` / `Frobenius_compl_Hall` | `Subgroup.IsFrobenius.ker_isHall` / `.compl_isHall` (π-indexed; unbundled coprime forms `coprime_card_ker_index` / `coprime_card_compl_index`) | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `normedTI H^# G H` (malnormality component of `[Frobenius G with complement H]`) | `Subgroup.isFrobenius_iff_inf_map_conj_eq_bot`, directions `IsSemiregular.inf_map_conj_eq_bot` (needs complement + normality) and `isSemiregular_of_forall_inf_map_conj_eq_bot` (hypothesis-free) | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| `FrobeniusJ`-style conjugation invariance | `Subgroup.IsFrobenius.conj` (and `.map` for isomorphisms; likewise `IsSemiregular.conj`/`.map`, `IsSemiprime.conj`/`.map`) | `OddOrder/Mathlib/GroupTheory/Frobenius.lean` |
| **Frobenius' kernel theorem** (no MathComp counterpart: `frobenius.v`/BG take the kernel as *given* via an explicit `sdprod` and consume the `IsFrobenius` interface; approximate) | `Subgroup.exists_isFrobenius_of_malnormal` (internal form: malnormal `H` ⇒ `∃ K`, `↑K = H.frobeniusKernelSet`, `#K = H.index`, `IsFrobenius K H`); action form `MulAction.exists_isFrobenius_stabilizer` (the lean-eval shape) | `OddOrder/Mathlib/GroupTheory/FrobeniusKernel.lean` |
| `Frobenius_partition` (approximate: the Coq lemma states the partition of `G` into `K` and the conjugates of `H^#`; this is the resulting count) | `Subgroup.card_frobeniusKernelSet` (`= H.index`; supporting bijection `(G ⧸ H) × H^# ≃ (frobeniusKernelSet)ᶜ` inlined) | `OddOrder/Mathlib/GroupTheory/FrobeniusKernel.lean` |
| `normedTI_isometry`-correspondent (approximate: the trivial-intersection seed of the Dade isometry, to be consumed by the future PFsection2 task; the Coq lemma is stated for `normedTI` configurations) | `ClassFunction.cfInner_ind_ind_of_malnormal` (`⟪ind α, ind β⟫_[G] = ⟪α, β⟫_[H]` for `α 1 = 0`, `H` malnormal; via `ClassFunction.res_ind_eq_self_of_malnormal`) | `OddOrder/Mathlib/GroupTheory/FrobeniusKernel.lean` |
| self-normalization of a malnormal subgroup (inside MathComp's Frobenius structure theory) | `Subgroup.normalizer_eq_self_of_malnormal` | `OddOrder/Mathlib/GroupTheory/FrobeniusKernel.lean` |
| `solvable_Wielandt_fixpoint` (wielandt_fixpoint.v, the file's only export) | `Subgroup.solvable_wielandt_fixpoint_internal` (statement-faithful internal form) and `solvable_wielandt_fixpoint` (external `MulDistribMulAction` form, the master proof) | `OddOrder/Mathlib/GroupTheory/WielandtFixpoint.lean` |
| `iso_quotient_homocyclic_sdprod` / `is_iso_quotient_homocyclic_sdprod` (approximate: ported in module form — the homocyclic `W` of exponent `p ^ m` with `W ⋊ G`-package and `'ker f = 'Mho^1(W)` becomes a free `ZMod (p ^ e)`-module summand of the regular module with matching fixed-point counts for all subgroups; see the module docstring for the exact correspondence) | `Representation.exists_wielandt_lift` | `OddOrder/Mathlib/GroupTheory/WielandtFixpoint.lean` |
| `coprime_act_abelian_pgroup_structure` (**not ported — bypassed**: the Coq uses it only to locate a homocyclic summand of the regular module over `'Z_q`; on the module route freeness of the summand follows from idempotent lifting + "f.g. projective over the local ring `ZMod (p ^ e)` is free", so no homocyclic decomposition is needed. Re-derive with M4's `Ω`/`℧` toolkit if a later file needs it.) | — (see `ZMod.isLocalRing_prime_pow`, `Module.free_range_of_comp_self_eq` for the replacement ingredients) | `OddOrder/Mathlib/GroupTheory/WielandtFixpoint.lean` |
| `homocyclic W` (as used in wielandt_fixpoint.v; the general predicate is M4 material) | `Module.Free (ZMod (p ^ e)) W` for the associated `ZMod (p ^ e)`-module (a finite abelian `p`-group of exponent dividing `p ^ e` is homocyclic of exponent `p ^ e` iff free) | `OddOrder/Mathlib/GroupTheory/WielandtFixpoint.lean` |
| `'Mho^1(W)` (for abelian `W` of exponent dividing `p ^ e`, as used here) | `p • W` (the kernel condition of the lift is spelled `φ w = 0 ↔ ∃ u, w = (p : ZMod (p ^ e)) • u`) | `OddOrder/Mathlib/GroupTheory/WielandtFixpoint.lean` |
| the trace computation of `solvable_Wielandt_fixpoint` (`gamma i`, `tr_rW_Ai`, the `[~: W, Ai1] \x 'C_W(Ai1)` block decomposition via `coprime_abelian_cent_dprod`) | `Representation.trace_sum_eq_card_mul_finrank_invariants` (averaging projection `Representation.averageMap` instead of the commutator/centralizer splitting) + `Representation.wielandt_trace_sum_eq` | `OddOrder/Mathlib/GroupTheory/WielandtFixpoint.lean` |
| `rCW`/`coprime_quotient_cent` step of `solvable_Wielandt_fixpoint` (`'r('C_W(Ai1)) = rC i`) | `Representation.card_invariants_eq_pow_finrank_of_lift` (private; coprime averaging + purity of the summand) | `OddOrder/Mathlib/GroupTheory/WielandtFixpoint.lean` |
| `factorCA_B` step of `solvable_Wielandt_fixpoint` (`#|'C_B(A i)| * #|'C_(V/B)(A i / B)| = #|'C_V(A i)|`, via `coprime_quotient_cent`) | `card_fixedPoints_eq_card_mul_card` (private; via `coprime_fixedPoints_quotient_eq`; externally the actor is not quotiented, so no `#|A i / B| = #|A i|` bookkeeping is needed) | `OddOrder/Mathlib/GroupTheory/WielandtFixpoint.lean` |

Future work (not ported yet, Frobenius theory): `Frobenius_quotient` /
`Frobenius_proper_quotient` / `Frobenius_normal_proper_ker` — these are proved in
`BGsection3.v` and port with the M4/BG3 task; `Frobenius_ker_dvd_ker1` /
`Frobenius_index_dvd_ker1` (variants of the counting fact, add on demand);
`Frobenius_partition` in literal partition form (the counting corollary is ported, see
above). Frobenius-complement *structure* facts:
`odd_regular_pgroup_cyclic` (BGsection3.v:1571, B&G 3.9 — odd p-groups acting
semiregularly are cyclic, the input making odd Frobenius complements Z-groups; M4) and
the `p = 2` cyclic-or-generalized-quaternion classification (no Mathlib analogue;
irrelevant at odd order). Once "all Sylow cyclic" is available, Mathlib's `IsZGroup`
covers the rest (solvability, metacyclic structure via `isZGroup_iff_exists_mulEquiv`,
`IsZGroup.isCyclic_commutator`, `IsZGroup.coprime_commutator_index`,
`IsZGroup.exponent_eq_card`) — see the audit section in
`OddOrder/Mathlib/GroupTheory/Frobenius.lean`.

Note: `ClassSum.lean` is Task 3 of the M2 plan (class sums, center basis, structure
constants). The plan files this material inside `CharacterArith.lean`; it was split into a
standalone file instead, per the parallel-work isolation protocol (Task 2 implemented
`Induced.lean` concurrently) and the plan's own "split further if any exceeds ~1200 lines"
clause.

Note: Task 4 (algebraic integrality) lands in `CharacterArith.lean` as planned. The Schur
scalar-extraction machinery (`MonoidAlgebra.centralAction`, `centralActionAlgHom`,
`centralScalarAlgEquiv`, `centralScalarHom`) is bundled as an `AlgHom`/`AlgEquiv` chain
(center of the group algebra → `ℂ[G]`-endomorphisms of a simple module → `ℂ`, via Schur's
lemma as an algebra isomorphism) so that `Irr.omega_mul`'s structure-constant identity and
`Irr.isIntegral_omega`'s finitely-generated-module argument both follow from generic
`AlgHom`/`AlgEquiv` API (`map_mul`, `map_sum`) rather than bespoke uniqueness arguments. The
one sanctioned edit to `ClassFunction.lean` refactors the eigenprojection computation inside
`Module.End.trace_pow_pred_eq_star_trace` into a standalone, reusable lemma
`Module.End.trace_eq_sum_zeta_pow_mul_natCast` (no statement changes, no new sorries).

Future work (not ported yet): `coprime_Hall_subset` and the Glauberman-lemma
variants of the coprime-action suite (`glauberman_...`, `ext_coprime_quotient_cent`
for non-solvable kernels) — see the scope note in
`OddOrder/Mathlib/GroupTheory/CoprimeAction.lean`.

Future work (not ported yet): the support-restricted `Z[irr G, A]` bridge for the
`Irr`-indexed lattice — the `zcharD1E`-analogue
`φ ∈ Z[Finset.univ.image (Irr → ClassFunction), {1}ᶜ] ↔ φ.IsVirtualChar ∧ φ 1 = 0`
(MathComp `zcharD1E`, usage e.g. PFsection4.v:305, PFsection11.v:722: membership in
`'Z[irr G, G^#]` is exactly "virtual character vanishing at `1`"). The two sides exist
separately (`ClassFunction.mem_virtualChar_iff`, `ClassFunction.IsVirtualChar`, and the
PF-shaped `vchar_norm2` takes the unbundled `φ 1 = 0` hypothesis directly); the bundled
bridge should land with the PF1 task plan, which fixes the `G^#` spelling. Tracked in the
deferred-items list of `docs/superpowers/plans/STATUS.md`.

Future work (not ported yet): `coprime_abelian_gen_cent1` (B&G 1.16: if `A` is
abelian noncyclic, normalizes `G`, and `gcd(|G|,|A|) = 1`, then `G` is generated by
the centralizers `C_G(a)` for `a ∈ A \ {1}`) and its variant
`coprime_abelian_gen_cent` — see the scope note in
`OddOrder/Mathlib/GroupTheory/CoprimeAction.lean`.

Note: Task 5 (Burnside's `p^a q^b` theorem) lands in `Burnside.lean`, in three stages.
**Stage 1** (the analytic crux, `Irr.eq_zero_or_norm_eq`) departs from the M2 plan's sketched
route: instead of the norm-product argument (`Algebra.norm_eq_prod_embeddings` + rational-
algebraic-integer descent), it uses **Kronecker's theorem**
(`NumberField.Embeddings.pow_eq_one_of_norm_le_one`) — a nonzero algebraic integer all of whose
conjugates lie in the closed unit disc is a root of unity — which needs only a *weak* (`≤ 1`)
per-embedding bound and skips the separability/norm-integrality/rational-descent machinery
entirely (see the task report for the full audit). **Stage 2**'s kernel characterization and
the class-size lemma's scalar-action step both need the *operator* identity behind
`Module.End.trace_eq_sum_zeta_pow_mul_natCast` (the eigen-projections themselves, not just
their trace corollary); rather than exposing this from the already-reviewed
`ClassFunction.lean`, the projection construction is duplicated locally in `Burnside.lean`
(`Module.End.exists_zeta_pow_eigenProjections`) to keep the task's commit scoped to
`Burnside.lean` + `OddOrder.lean` + `NAME_MAP.md`. **Stage 3** additionally exposes
`Irr.degreeNat` (a natural-number degree accessor, choice witness of `Irr.exists_degree`) and
two small number-theoretic helpers (`exists_eq_pow_mul_pow_of_dvd`,
`factorization_pow_mul_pow_self_right`), both private to `Burnside.lean`.

Note: M3 Task 5 (the Wielandt fixpoint order formula) lands in `WielandtFixpoint.lean`.
The port replaces the Coq file's group-theoretic middle third (homocyclic decomposition
`coprime_act_abelian_pgroup_structure`, `Ω`/`℧` calculus, `'Z_q`-row-vector matrix
representations, external `sdpair` semidirect-product gluing) with its module-theoretic
content over `ZMod (p ^ e)`: Maschke (`MonoidAlgebra.Submodule.exists_isCompl`),
idempotent lifting along the nilpotent kernel of
`(ZMod (p ^ e))[G] →+* (ZMod p)[G]` (`exists_isIdempotentElem_eq_of_ker_isNilpotent`),
"finitely generated projective over a local ring is free"
(`Module.free_of_flat_of_isLocalRing`, with the new `ZMod.isLocalRing_prime_pow`), and the
averaging projection `Representation.averageMap` for the trace computation.  The exported
order formula `solvable_Wielandt_fixpoint` — the only lemma of `wielandt_fixpoint.v`
consumed downstream (BGsection3, PFsection9) — is ported sorry-free in both external
(`solvable_wielandt_fixpoint`) and statement-faithful internal
(`Subgroup.solvable_wielandt_fixpoint_internal`) forms; a smoke `example` checks the
BGsection3 (`Frobenius_Wielandt_fixpoint`, Peterfalvi (9.1)) instantiation shape (family
indexed by all subgroups, `A := id`, the `⊥ ↦ #|K|, G ↦ 1` vs `{K} ∪ orbit` weights).
The strong induction on `#|V|` avoids minimal-normal machinery: it splits along any
`G`-invariant normal subgroup and, when none exists, shows `V` elementary abelian
directly (commutator, then `p`-torsion, both invariant-or-full).
