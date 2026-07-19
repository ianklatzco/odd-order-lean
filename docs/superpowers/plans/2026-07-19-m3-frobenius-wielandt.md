# M3 — Frobenius Groups + Wielandt Fixpoint (task plan)

> Task-level plan for milestone M3 of the [master plan](2026-07-06-odd-order-port.md), plus the
> two pre-BG gates that precede it. Process: subagent-driven development per STATUS.md (fresh
> implementer per task, adversarial review, fix rounds; sorry budget 1 throughout; conventions per
> STATUS.md §Standing conventions). Execute in order — Tasks 1–2 are independent of each other;
> Task 4 needs Task 3; Task 5 needs Task 2.
>
> Evidence base: `docs/audit/survey-digest.md` entries for `wielandt_fixpoint.v` and
> `BGsection3.v`; the Coq sources ARE on the driving machine at
> `~/feit-thompson/odd-order/theories/` (use them for statement shapes). MathComp's
> `frobenius.v` itself is NOT present — design the Frobenius API from the survey digest plus
> the BG/PF usage sites in the Coq sources.

## Task 1: internal-action transfer layer (pre-BG gate)

New `OddOrder/Mathlib/GroupTheory/CoprimeActionInternal.lean`. For subgroups `H A : Subgroup G`
with `A ≤ H.normalizer`, under the conjugation action (`Subgroup.normalizerMulDistribMulAction`
composed appropriately — grep CoprimeAction.lean for the existing bridge):

- `FixedPoints.subgroup` of the conjugation action identified with
  `(Subgroup.centralizer A ⊓ H).subgroupOf H`-shaped centralizer intersections (exact
  formulation: whatever makes the coprime-suite conclusions restate cleanly — document).
- `actionCommutator` identified with `⁅H, A⁆.subgroupOf H` (commutator computed in `G`).
- Internal restatements (corollaries, not re-proofs) of: `coprime_cent_prod`
  (`H = ⁅H,A⁆ * C_H(A)` for solvable H, coprime), `coprime_commutator_eq` (`⁅H,A,A⁆ = ⁅H,A⁆`),
  `coprime_fixedPoints_quotient_surjective` (fixed points lift through A-invariant quotients,
  internal form), `coprime_hall_exists`/`_trans` (A-invariant Hall subgroups of H, internal).
- These are the shapes BGsection1-16 statements will consume; check 2–3 BG usage sites in the
  Coq sources to validate the formulation before proving.

## Task 2: AbelemRepr — the D9 bridge (pre-BG gate)

New `OddOrder/Mathlib/GroupTheory/AbelemRepr.lean` (or RepresentationTheory/ — implementer's
call, document). MathComp `mxabelem`'s role in module language:

- For `p.Prime` and `V : Subgroup G` normal elementary abelian `p` (use ChiefFactor.lean's
  `IsElementaryAbelian`), package: `V` as a `Module (ZMod p)` (via `AddCommGroup.zmodModule`
  through `Additive`), the conjugation action of `G` (or `G ⧸ centralizer`) as
  `DistribMulAction`/`Representation (ZMod p) G' V`-shaped data, and the dictionary lemmas:
  minimal-normal-in-G ↔ the module is irreducible (`IsSimpleModule`-shaped; MathComp
  `abelem_repr`/`acts_irreducibly`); A-invariant subgroups ↔ submodules.
- Scope discipline: build what Task 5 (Wielandt) and BG1–4 consume (grep survey digest
  BGsection1/2/4 entries for `abelem_repr` mentions); no matrix language, modules only.

## Task 3: Frobenius predicates + basic API

New `OddOrder/Mathlib/GroupTheory/Frobenius.lean`:

- `Subgroup.IsSemiregular (K H : Subgroup G) : Prop` — every nontrivial element of `H` has
  trivial fixed points/centralizer in `K` (MathComp `semiregular`, via conjugation:
  `∀ h ∈ H, h ≠ 1 → centralizer {h} ⊓ K = ⊥`-shaped) and `IsSemiprime` (MathComp `semiprime`:
  `C_K(h) = C_K(H)` for all `h ∈ H^#`) — exact shapes from BGsection3/12/13 usage sites.
- `IsFrobenius (G) (K H : Subgroup G) : Prop` — internal form: `K.Normal`-free statement
  `IsComplement' K H ∧ K ≠ ⊥ ∧ H ≠ ⊥ ∧ IsSemiregular K H` mirroring MathComp's
  `[Frobenius G = K ><| H]` (which does NOT assume K normal a priori — check usage; the kernel
  theorem is what makes K normal in the action form). Also the action-characterization lemma
  connecting to `MulAction` transitive + trivial two-point stabilizers, at whatever strength
  BG needs (check BGsection3's `Frobenius_semiregularP`-shaped rewrites in the Coq source).
- Basic API: conjugation invariance, `Frobenius_context`-shaped destructors, complement is a
  Hall subgroup / kernel order + complement order coprimality-shaped counting facts (from the
  semiregular action: `|H| ∣ |K| - 1`, MathComp `Frobenius_dvd_ker1` — a counting argument via
  the partition of `K^#` into `H`-orbits of size `|H|`), `IsZGroup` coverage audit for
  complement-structure facts (cite what exists, list gaps in NAME_MAP as future work).

## Task 4: Frobenius' kernel theorem (character-theoretic)

In `Frobenius.lean` (or a `FrobeniusKernel.lean` sibling):

- **The theorem**: for a finite `G` acting transitively and faithfully on `X`, `|X| ≥ 2`,
  nontrivial point stabilizers, no nonidentity element fixing two points, the set
  `{1} ∪ {g | ∀ x, g • x ≠ x}` is a (normal) subgroup — AND/OR the internal form: given
  `H ≤ G` malnormal (`H ⊓ H^g = ⊥` for `g ∉ H`), nontrivial proper, the complement set
  `K = G \ ⋃_{g} (H^g)^#` is a normal subgroup with `IsComplement' K H`. Pick the form(s)
  BGsection3 + PF consume (grep Coq usage; the eval problem's action form is a corollary —
  state it too if cheap).
- Proof: the classical induced-character argument (Isaacs 7.2/Peterfalvi 3.1 shape): for each
  nonprincipal `θ : Irr H`, the virtual character `θ^G - θ(1)·(1_H)^G + θ(1)·1_G` has norm 1,
  positive at 1 ⇒ irreducible (M2's `vchar_norm1`-shaped lemma + `cfInner` calculus + Frobenius
  reciprocity + the induced-character support computation on the malnormal configuration);
  `K = ⋂_θ ker` of the resulting irreducibles ⇒ subgroup, normal, order counting
  (`|K| = |G|/|H|`) ⇒ complement. Character kernels: `Irr.ker` exists (Burnside.lean) —
  promote/reuse (this is the sanctioned moment to move it to CharacterArith.lean per the
  deferred list).
- All M2 machinery is in place for this; the reviewer must check the support/counting
  computations especially (`ind` on class functions supported off conjugates of H).

## Task 5: Wielandt fixpoint order formula

Port `wielandt_fixpoint.v` (668 loc, on this machine — read it) into
`OddOrder/Mathlib/GroupTheory/WielandtFixpoint.lean`:

- Prerequisite mini-toolkit (this task builds it, scoped to abelian groups): `IsHomocyclic`
  predicate (direct product of cyclic groups of equal order — formulate module-theoretically
  over `ZMod (p^m)` where possible), Ω_1/℧-for-abelian-p-groups as needed (grep what the Coq
  proof actually uses; do NOT build the general nonabelian Ω/℧ — that is M4 material).
- `coprime_act_abelian_pgroup_structure`: coprime-invariant homocyclic decomposition of an
  abelian p-group (A-invariant factors, A irreducible on Frattini quotients).
- The homocyclic lifting theorem (`iso_quotient_homocyclic_sdprod`): realize a minimal-normal
  elementary abelian `V` under coprime `G`-action as `W/℧(W)` for homocyclic `W` of exponent
  `p^m` inside `W ⋊ G` — via the regular-representation-over-`ZMod (p^m)` module construction
  (Task 2's dictionary; external `SemidirectProduct` + the CoprimeAction semidirect bridge).
- `solvable_Wielandt_fixpoint`: the order formula exactly as stated in the Coq file (read it;
  weighted product over a family `A_i ≤ G` with the `a ∈ G^#` weight-balance hypothesis).
  Consumers: BGsection3's `Frobenius_Wielandt_fixpoint` (PF 9.1) and PFsection9 — the
  statement must transport to those uses; validate against BGsection3.v's derivation.
- This is the hardest M3 task; DONE_WITH_CONCERNS with the sorry-budget protocol is acceptable
  for the lifting theorem ONLY if the order formula lands sorry-free some other honest way —
  otherwise escalate.

## Out of scope (defer with NAME_MAP rows)

- Thompson's kernel-nilpotency (only the solvable case is ever used; the Coq proves it in
  BGsection3 = M4 — port it there).
- General nonabelian Ω_i/℧^i, extraspecial/critical subgroups (M4).
- Frobenius complement structure theory beyond what Task 3's audit finds cheap (cyclic
  Sylow / generalized quaternion classification — M4-adjacent, flag as future work).

## Close-out

STATUS.md current-state + next-work rewrite (M3 ✅; next: BG1 skeleton + M4 plan / PF1 start —
the parallel tracks open); README status + punchlist updates; ledger; full build + sorry
count = 1; push.
