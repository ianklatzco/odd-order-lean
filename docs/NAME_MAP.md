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
| character kernel (`cfker`) | `Irr.ker`, `Irr.mem_ker_iff`, `Irr.eq_one_of_ker_eq_top` | `OddOrder/Mathlib/RepresentationTheory/Burnside.lean` |
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
