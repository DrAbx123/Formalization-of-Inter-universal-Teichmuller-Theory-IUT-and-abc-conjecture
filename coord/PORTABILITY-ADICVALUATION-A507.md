# PORTABILITY: Mathlib 4.36 AdicValuation / ValuativeRel Completion (A507, read-only)

Scope: v4.36.0-rc2 vs v4.32.2, for
  RingTheory/DedekindDomain/AdicValuation/Completion.lean
  RingTheory/DedekindDomain/AdicValuation/Ramification.lean
  Topology/Algebra/ValuativeRel/Completion.lean
No source was modified; this file is an assessment only.

## 0. Two global blockers for every cherry-pick

1. Module-system syntax: v4.36 files start with 'module', 'public import ...',
   '@[expose] public section'. The v4.32.2 toolchain cannot parse these headers.
   Every port needs a mechanical header rewrite (module removed, public import -> import,
   public section -> section). Low risk but must be scripted.
2. The AdicValuation monolith was split in v4.36: v4.32.2 has only
   RingTheory/DedekindDomain/AdicValuation.lean (1,123 lines, 127 declarations).
   v4.36 splits it into AdicValuation/Valuation.lean + Completion.lean (+ others).
   Of the 60 declarations in the new Completion.lean, 48 already exist (same names)
   in the v4.32.2 monolith; only 12 are genuinely new. Porting the file verbatim is
   impossible (duplicate names); port only the 12.

## 1. RingTheory/DedekindDomain/AdicValuation/Completion.lean

- Size 503 lines / 60 declarations; new declarations (12):
  valuationExtension_toCompletion, valuation_ofCompletion, valueGroupMulEquiv,
  coe_valueGroupMulEquiv, valueGroupOrderMonoidIso, valueGroupOrderMonoidIso_coe,
  embedding_valueGroupOrderMonoidIso, valueGroupOrderMonoidIso_restrict,
  extension_apply_eq_valued, valuedAdicCompletion_apply, valued_toCompletion_apply,
  valued_ofCompletion_apply.
- Dependency problem: almost all new proofs use Valuation.extension, which is a
  new v4.36 definition living in Topology/Algebra/ValuativeRel/Completion.lean
  (v4.32.2 has no Valuation.extension). The old monolith instead uses
  Valued.extensionValuation (present in v4.32.2 AdicValuation.lean).
- Portability effort:
  - Option A (faithful): first port file 3 below, then 12 new declarations -> Large.
  - Option B (rewrite to old API): keep v4.32.2 monolith, re-prove the 12 statements
    using Valued.extensionValuation / Valued.locally_const -> Medium-High; no new deps.
- Benefit for us: value-group isomorphisms and Valued.v normalization on the actual
  adic completion; relevant to local ramification/value-group bookkeeping, but not
  blocking our current O6 objects (HullDetObjectActual uses c3RamificationIndex and
  localRamificationIndex from LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceCompletionDegree.lean).

## 2. RingTheory/DedekindDomain/AdicValuation/Ramification.lean

- Size 118 lines / 3 declarations, all 3 new:
  intValuation_liesOver, valuation_liesOver, uniformContinuous_algebraMap_liesOver.
- Cheap subset is portable. intValuation_liesOver and valuation_liesOver use only old
  v4.32.2 API (verified):
  - intValuation_eq_exp_neg_multiplicity (old AdicValuation.lean)
  - Ideal.ramificationIdx'_eq_ramificationIdx (old NumberTheory/RamificationInertia/Ramification.lean)
  - emultiplicity_map_eq_ramificationIdx'_mul (old NumberTheory/RamificationInertia/Valuation.lean)
  - FiniteMultiplicity.of_prime_left (old AdicValuation.lean)
  - valuation_of_algebraMap, IsFractionRing.div_surjective (old, Mathlib)
  - Ideal.ramificationIdx_pos_of_isDedekindDomain' is new in v4.36
    RingTheory/RamificationInertia/Ramification.lean (4 new declarations:
    ramificationIdx_bot_eq_one, ramificationIdx_pos_of_mem_minimalPrimes,
    ramificationIdx_pos_of_isDedekindDomain, ramificationIdx_pos_of_isDedekindDomain').
    Their proofs need only one extra old-missing private lemma,
    Ideal.mem_minimalPrimes_of_ne_bot (tiny, 4 lines, new in v4.36
    RingTheory/DedekindDomain/Basic.lean:66).
- Hard subset: uniformContinuous_algebraMap_liesOver uses WithVal.valuation,
  ValuativeRel.ValueGroupWithZero.orderMonoidIso, valueGroup0_equiv_withZeroMulInt,
  vle_iff_le, Valuation.extension and the new valuative-topology API; porting it drags
  in file 3. Skip it (not needed for our ramification bridge).
- Estimated effort for the cheap subset: Small (about 120 lines: 4 positivity lemmas
  + 2 liesOver theorems + imports; no new layer).
- Benefit for us: directly targets the named local/global ramification comparison in
  LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceCompletionDegree.lean
  (localRamificationIndex vs ramificationIdx'); can partially fill that named gap and
  support the O6 hull-radius ramification object. Highest value/effort ratio of the 3.

## 3. Topology/Algebra/ValuativeRel/Completion.lean

- Size 513 lines / 34 declarations, entirely new in v4.36; v4.32.2 dir contains only
  ValuativeTopology.lean.
- All imports exist in v4.32.2 (UniformField, ValuativeRel/ValuativeTopology,
  WithZeroTopology), but the base files changed:
  - ValuativeTopology.lean: 432 -> 488 lines, 138 diff lines vs v4.32.2
  - Topology/Algebra/Valued/WithVal.lean: 695 -> 663 lines, 82 diff lines
  - Topology/Algebra/UniformField.lean: 215 -> 211 lines, 18 diff lines
  - Topology/Algebra/WithZeroTopology.lean: 187 = 187, 10 diff lines
  and the new file uses new names absent from v4.32.2, e.g. vle_iff_le,
  exists_coe_mem_extension_eq, valueMonoid_eq_closure, while another helper
  valueGroup0_equiv_withZeroMulInt exists in old RingTheory/Valuation/Discrete/RankOne.lean.
- Portability: Medium-High effort (module-syntax rewrite + port the small new helpers
  from the changed base files + adapt 34 declarations). It is the natural first step
  if we ever want option A of file 1, but it is a 500-line new layer and gives little
  to the current hull/theta-log-volume lane (our completions use
  Valued.extensionValuation/NormalizedCompletion; new valuative topology is not on the
  object-critical path).
- Benefit for us: valuative completion continuous/closed maps; may simplify future
  local-field continuity arguments, not recommended now.

## 4. Effort / value summary

| File | new decls | new-layer deps | effort | value for our lane | recommendation |
|---|---|---|---|---|---|
| AdicValuation/Ramification.lean (2 of 3 decls) | 2 theorems + 4 small positivity lemmas | none (old API) | Small (~120 lines) | direct (local ramification bridge) | do this first (if scheduled) |
| AdicValuation/Completion.lean (12 decls) | 12 | needs Valuation.extension or old-API rewrite | Medium-High | value-group normalization | defer |
| Topology/Algebra/ValuativeRel/Completion.lean | 34 | base-file drift | High (500+ lines) | low for now | do not port now |

## 5. Suggested next executable step

1. tmp/newmathlib/AdicValuation/RamificationLiesOver.lean: import old monolith
   AdicValuation + NumberTheory/RamificationInertia/{Ramification,Valuation}; port
   Ideal.mem_minimalPrimes_of_ne_bot + 4 ramificationIdx_pos_* lemmas; then
   intValuation_liesOver and valuation_liesOver. Queue closure with
   node tools/extras_add_closure.mjs <file>.
2. Only if the local/global ramification comparison actually blocks a proof:
   Option B port of the 12 Completion.lean declarations against Valued.extensionValuation.
3. Do not port ValuativeRel/Completion.lean unless a concrete consumer appears.

Evidence: file:line refs above from tmp/mathlib4-4.36.0-rc2/Mathlib/... (v4.36.0-rc2)
and .lake/packages/mathlib/Mathlib/... (v4.32.2); declaration name sets extracted from files.