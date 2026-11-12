# SKELETON-IUTIV-ABCBRIDGE — node graph: IUTIV (14) + ABCBridge (164) modules

Status: inventory/graph only (Lead A429). No new wiring, no closure claims.
Generated 2026-11-11 for stepxi (史蒂). Registry frozen 14041; gate NOT PASSED.
Machine-readable full edge list: `coord/skeleton-iutiv-abcbrige-edges.tsv`
(178 rows: dir, module, thm/def/struct/abbrev counts, olean status, pending/interface,
imports (internal basenames), consumers (internal basenames)).

Method: scanned every `.lean` under `LeanFormal/IUT/IUTIV` (14) and
`LeanFormal/IUT/ABCBridge` (164); counted declarations, extracted internal imports,
inverted them into consumer lists, checked olean presence/freshness in
`.lake/build/lib/lean`, grepped pending/interface obligations and sorry/axiom text.
Citable evidence for representative core declarations:
`tmp/sheaf/xif/paper/_FOUNDATIONS-IUTIV-CitableProbe.lean` EXIT=0 (results:210254),
axioms for deg_pullback/ndeg_pullback/iutIVProp17/iutIVProp21ii_theta_two_sided/
processionAverage_le/stepVPaperLogVolumeBound/measure_hull_lt_top/
hull_logVolume_lt_top/sum_completionNormDegree_eq_fieldDegree/
cor312ToABCBridge_abcConjecture = [propext, Classical.choice, Quot.sound].

---

## 1. IUTIV (14 modules, all oleans fresh)

| module | thm/def | key declarations | status |
|---|---|---|---|
| ArithmeticDivisorDegree | 104/24 | IUTIVPlace, weight, localDegree, IUTIVArithmeticDivisor, deg/ndeg, pullback, deg_pullback, ndeg_pullback, HeightBoxLayer(absValAt, hweightvol, hpoint) | **OK (REAL)** |
| ArchimedeanTensorMetric | 13/1 | complexTensorToProd_(inner/norm_sq/injective/bijective), complexTensor_algEquiv_inner, inner_unitMul_conjOpt | **OK (REAL, partial Prop 1.5)** |
| ArchimedeanMultiTensorMetric | 32/3 | tensorMetric_tprod, conjTwist_apply, characterIndex, twistPattern | **OK (REAL)** |
| DifferentTowerEstimate | 3/0 | count_differentIdeal_tower, iutIVProp13i_normalizedDifferent_ge | **OK (REAL, Prop 1.3(i)) ** |
| DifferentTameEquality | 4/0 | count_differentIdeal_eq_of_tame, iutIVProp13i_normalizedDifferent_eq_of_tame | **OK (REAL, Prop 1.3(i) equality)** |
| DifferentDegreeUpperBound | 12/0 | not_map_dvd_differentIdeal_of_degree_not_mem, dvr_ideal_eq_pow_factorCount, ... | **OK (REAL, Prop 1.3(ii) partial)** |
| ElementaryEstimates | 6/0 | iutIVThm110_e1..e4, e5/e6 | **OK (REAL, Thm 1.10 finite bookkeeping)** |
| Section1 | 6+props/1 | iutIVSection1 (Obligation), iutIVProp17 family | **PENDING obligation** (text row only); Prop 1.7 REAL |
| Section2 | 11+props/2 | iutIVSection2 (Obligation), iutIVProp21i, iutIVProp21ii_theta_two_sided_eventually, iutIVProp16_* | **PENDING obligation** (text row only); proved estimates REAL |
| StepVProcessionAverage | 8/1 | collectionBound, sum_collectionBound, processionAverage_eq, processionAverage_le, exceptionalSum_le_r4 | **OK (REAL, Thm 1.10 step (v))** |
| StepVDivisorAverage | 2/0 | weight_finite_eq_inertiaDeg_mul_log, eDegreeUnnormalized_eq_weightedAverage | **OK (REAL)** |
| StepVDistinguishedSlotAverage | 4/0 | weightedSum_collectionChoiceBound_independent, weightedAverage_collectionChoiceBound, weightedAverage_le_of_distinguishedBound | **OK (REAL)** |
| StepVProcessionAverageAxiomProbe | 0/0 | (probe only) | probe, not a node |
| StepVDivisorAverageAxiomProbe | 0/0 | (probe only) | probe, not a node |

Key gaps against paper (see `coord/FOUNDATIONS-IUTIV.md` §3): Prop 1.1 tensor ring,
Prop 1.2, Prop 1.4 local log-volume, Prop 1.5 general archimedean, Prop 1.8 elliptic/Serre,
Thm 1.10 actual log-volume estimate, explicit PNT constants, arithmetic transition objects.
The two PENDING obligations above are bookkeeping rows; the REAL theorems in Section1/2
are the proved elements (Prop 1.3(i), Prop 1.6, Prop 1.7, Prop 2.1).

---

## 2. ABCBridge (164 modules)

Root: `Statement.lean` (def ABCConjecture:32), `UnprovedTarget.lean` (documentation only).

### 2.1 Bridge (18 modules)
| module | status | key declarations |
|---|---|---|
| ABCEllipticHeightCriterion | OK | ABCFreyJProductHeightCriterion, ABCLegendreJProductHeightCriterion, equivalence theorems :61/:118/:188/:196 |
| ABCFrontier | IFACE | FrontierHeightComparisonClause, FrontierRegionComparisonClause, ABCFrontier, bridgeInterface_of_frontier, abcConjecture_of_frontier:213, abcConjecture_of_frontierRealLine:309 |
| ABCFrontierHeightWeightRefutation | OK | isABCTriple_one_eight_nine, oneAdd_tenth_mul_arithmeticWeight_lt_logHeight (refutes factorization through additive bound) |
| ABCFrontierPointwisePremiseReduction | OK | frontierSplitClause_of_unitMembership, frontierUnitMembership_weightRegionClause_* |
| ABCFrontierReductions | IFACE | FrontierHeightWeightClause, FrontierWeightRegionClause, FrontierUnitNormalizationClause, FrontierSplitClause, abcConjecture_of_frontierGapReduced:301, ...PointwiseReduced:313 |
| ABCFrontierSingletonReduction | IFACE | FrontierSingletonWeightVolumeClause, FrontierRegionFinitenessClause, ABCFrontierGapReducedV2, abcConjecture_of_frontierGapReducedV2:137 |
| ABCGap2FiniteC3Supply | **MISSING OLEAN** | ABCGap2RegionVolume_finiteC3 (not built; red/absent) |
| Cor312CarrierRealizationSpec | OK | cor312CarrierSpec_isABCTriple_one_two_three, cor312CarrierSpec_logHeight, ... |
| Cor312ComparisonGapReduction | IFACE | cor312Gap2_normalizedComparisonRegion_eq_scaleShift_union, cor312Gap2_hull_logVolume_le_normalizedComparisonRegion, cor312Gap2_region_logVolume_le_add_of_subadditive |
| Cor312ComparisonGapSupplyLayer | OK | cor312GapSupply_sourceSetVolume_singleton, cor312GapSupply_sourceInterface_* |
| Cor312GapDictionaryLayer | OK | cor312GapDict_abcRationalPoint_logHeight, cor312GapDict_singletonVolume_toReal_eq_max, ... |
| Cor312PointwiseMembershipWeakening | OK | ABCFrontierPointwiseWeakened, pointwiseWeakened_of_pointwiseReduced, abcConjecture_of_frontierPointwiseWeakened:227 |
| Cor312PointwiseResidualSupply | IFACE | cor312Pointwise_spikeCarrier_logVolume_singleton, cor312Pointwise_not_forall_singleton_logVolume_lt_top, cor312Pointwise_sourceInterface_hptfin |
| Cor312ToABCBridgeInterface | IFACE | Cor312EpsilonArithmeticComparison:224 (two named IUT IV §2 gaps), Cor312ToABCBridgeInterface:404, cor312ToABCBridge_heightBound:426, cor312ToABCBridge_abcConjecture:446, strength iff:605 |
| Cor312ToABCCards | PENDING/IFACE | Cor312ToABCChainCard, cor312ToABCChainStep{Cor312ToC2,ExcToBDBound,MonoComplexToSzpiro}Card |
| FreyOddConductorHeightCriterion | OK | IsABCTriple.mem_abcOddBadPrimeSupport_iff_dvd_oddConductor, ... |
| IUTToABC | PENDING | cor312ToABCBridge (pending obligation def), abcConjecture_iff_abcLogConjecture:36, abcConjecture_iff_abcArithmeticWeightHeightBound:64 |
| ThetaBoundToHeightWeight | OK | exists_oneAdd_sq_le_oneAdd, heightWeightBound_of_normalizedVolumeComparison:67 |

### 2.2 Arithmetic (15 modules, all OK)
| module | key declarations |
|---|---|
| ABCHeightArithmeticWeightComparison | abcRationalPoint_logHeight, ABCHeightWeightAdditiveBoundV2, abcConjecture_iff_ABCHeightWeightAdditiveBoundV2:167 |
| ABCInvariantCoprimality | abcInvariantPolynomial, abcInvariantNumerator/Denominator, abcInvariantCancellation |
| ABCInvariantHeight | abcInvariantFraction_num_natAbs/den, abcInvariantFraction_mulHeight_eq/le_max |
| ABCInvariantLocalHeight | abcRationalPoint_log_abs_le_zero, abcRationalPoint_logHeight, abcRationalPoint_den_factorization... |
| ABCInvariantLocalValuations | IsABCTriple.abcInvariantPolynomial_mod_two/odd, two_not_dvd_..., product_pos |
| ABCInvariantRadicalBridge | abcJInvariant_den_primeFactors_double/radical_double, abcInvariant_natRadical_double_le_twice |
| ABCNonemptyOddBadSupport | positive_nat_eq_two_pow_of_only_two_prime_divisors, IsABCTriple.eq_one_one_two_of_only_two_prime_divisors |
| LogarithmicBoundEquivalence | logLeIffLeExpMulRpow, ABCLogBound, ABCLogConjecture:63 |
| PrimitiveTriple | ABCPairwiseCoprime, IsABCTriple.coprime_left_right, pairwise_coprime |
| RationalBoundaryPrimeSupport | mem_arithmeticPrimeSupport_iff_*, prime_of_mem_arithmeticPrimeSupport |
| RationalBoundaryValuations | padicValRat_eq_natAbs_sub_den, padicValRat_one_sub..., boundary_sign_pattern |
| RationalDifferent | discr_eq_one_of_finrank_one, differentIdeal_eq_top_of_finrank_one, log_rootDiscr_eq_log_abs_discr_div_finrank |
| RationalLocalHeightDecomposition | real_log_nat_eq_sum_factorization/padicValNat, rat_log_abs_eq_log_num_natAbs_sub_log_den |
| RationalPointDictionary | PositivePrimitiveAdditiveTriple, isABCTriple_iff_positivePrimitiveAdditiveTriple, abcRationalPoint |
| RationalPrimeSupport | arithmeticPrimeSupport, natRadical_cast_pos/log_eq_sum_primeFactors, arithmeticPrimeSupport_abcRationalPoint |

### 2.3 Galois (6 modules, all OK)
EllipticDivisionField, EllipticDivisionPolynomialEvaluation, EllipticPrimeTorsionCardinality,
EllipticPrimeTorsionGalois, EllipticTorsionAlgebraicity, EllipticTorsionConsumerWiring
(torsion fields/coordinates/algebraicity; consumer wiring to finite-dimensionality/Galois).

### 2.4 Geometry (123 modules, 1335 thm / 253 def)
| group | count | thm/def | status/notes |
|---|---|---|---|
| FinitePlace* | 76 | 589/152 | FinitePlaceIQHull* (interface/certificate/volume/log-shell), FinitePlaceArithmeticIQHull*/Tensor*/TupleHull*, FinitePlaceStepV*, FinitePlaceSource*; one PENDING (FinitePlaceCompletionLocalInputs), MISSING olean: FinitePlaceHolomorphicDifferentBase; STALE: FinitePlaceLocalInclusionTensorization, FinitePlaceThetaPilotScaledRegion |
| Frey* | 26 | 397/36 | Frey conductor/discriminant/torsion/Legendre: FreyConductorOdd/TwoAdic, FreyWeierstrassCurve, FreyTate*, FreyTwoAdic* (minimality/reduction cases), FreyDiscriminantRadical, FreySplittingFields; all OK |
| Legendre* | 9 | 211/55 | LegendreJFunctionDivisor, LegendreJTwoAdicValuation, LegendreLevelTwoStructure, LegendreParameter*, LegendreProjectiveMap, LegendreWeierstrassCurve; all OK |
| AdicCompletion* | 4 | 22/1 | AdicCompletionChineseRemainder, ...ValuationUniqueness; two AxiomProbe files MISSING olean (probes, not nodes) |
| P1* | 1 | 9/5 | P1CarrierDesignActual |
| other | 7 | 107/4 | ABCModelHeightComparison, ABCResidueDiscriminant, BoundedDegreeLegendreIsomorphisms, QuadraticTwistArithmetic, RelativeCompletionFinrankReduction, TateOggSaitoTwoAdicCards, RationalCommonPrimeFinrank; all OK |

Full per-module rows (counts, imports, consumers) are in the TSV; internal consumer edges show
e.g. Cor312ComparisonGapSupplyLayer -> Cor312ComparisonGapReduction -> Cor312ToABCBridgeInterface
and FinitePlaceStepV* -> FinitePlaceStepVAssembly -> (IUT IV step (v) consumers).

---

## 3. The last chain: IUT IV comparison -> ABCConjecture (Lean theorem path)

Base definitions:
- `LeanFormal.IUT.ABCConjecture`: `LeanFormal/IUT/ABCBridge/Statement.lean:32`
- `LeanFormal.IUT.ABCLogConjecture`: `Arithmetic/LogarithmicBoundEquivalence.lean:63`
- `abcConjecture_iff_abcLogConjecture`: `Bridge/IUTToABC.lean:36`
- `abcConjecture_iff_abcArithmeticWeightHeightBound`: `Bridge/IUTToABC.lean:64`

Path A (the Cor 3.12 route actually wired):
1. `Cor312EpsilonArithmeticComparison` (`Bridge/Cor312ToABCBridgeInterface.lean:224`) —
   data `logShellPoint` + TWO NAMED IUT IV §2 gaps:
   `height_le_normalizedRegionVolume` (height vs normalized region log-volume; IUT IV §2)
   `regionVolume_le_normalizedWeight` (region log-volume computation; IUT IV §2, conditional
   on Cor 3.12 finiteness).  Region finiteness itself is DERIVED: `comparisonRegion_logVolume_lt_top:267`.
2. `cor312ToABCBridge_heightBound` (:426), via
   `ThetaBoundToHeightWeight.heightWeightBound_of_normalizedVolumeComparison:67`:
   forall eps>0 exists A, height <= (1+eps)*weight + A on IsABCTriple.
3. `cor312ToABCBridge_abcConjecture` (:446), using
   `abcConjecture_iff_abcArithmeticWeightHeightBound` (IUTToABC:64).
4. `ABCConjecture` (Statement.lean:32).
Strength calibration: `cor312ToABCBridgeInterface_nonempty_iff_abcConjecture:605` —
the interface is exactly as strong as ABC; no gap is proved.

Path B (frontier interfaces, equivalent conditional endpoints):
`ABCConjecture` <= `abcConjecture_of_frontier` (`Bridge/ABCFrontier.lean:213`)
<= `abcConjecture_of_frontierRealLine` (:309)
<= `abcConjecture_of_frontierGapReduced` (`ABCFrontierReductions.lean:301`)
<= `abcConjecture_of_frontierPointwiseReduced` (:313)
<= `abcConjecture_of_frontierGapReducedV2` (`ABCFrontierSingletonReduction.lean:137`)
<= `abcConjecture_of_frontierPointwiseWeakened` (`Cor312PointwiseMembershipWeakening.lean:227`).
These consume the frontier structures (IFACE: FrontierHeightComparisonClause,
FrontierRegionComparisonClause, ...) and do not prove them.

Path C (Cor312 gap-reduction layer, named reduced inputs):
`Cor312ComparisonGapSupplyLayer` (assembly of reduced gap inputs) ->
`Cor312ComparisonGapReduction` (IFACE: cor312Gap2_* lemmas) ->
`Cor312ToABCBridgeInterface` (two gaps).  `Cor312GapDictionaryLayer` provides dictionary
identities; `Cor312PointwiseResidualSupply` and `Cor312PointwiseMembershipWeakening`
are additional IFACE reductions.  `Cor312CarrierRealizationSpec` gives concrete
validation carriers (model, not the paper carrier).

Path D (IUT IV §1 -> Cor 3.12 display, external to this graph):
`tmp/sheaf/xif/paper/S3171IUTIVSection1DisplayActual.thm110_final_display` states the
exact Thm 1.10 Step (v) display, conditional on `Thm110DisplayInputs`
(`hCor312` from the Cor 3.12 route (b)/(c) consumer, and `hSlack` = paper step-(v)
arithmetic, class B).  This is NOT a Lean edge into Path A: Path A's two gaps are IUT IV
§2 comparisons, not the §1 display.  There is currently no theorem connecting the
IUT IV §1 display to the §2 Cor312 comparison gaps; that edge is a paper-level task.

Caution: `ABCFrontierHeightWeightRefutation` proves a factorization through the
additive height-weight bound cannot give the frontier (counterexample at (1,8,9)); keep
this in mind before proposing any new route through `ABCHeightWeightAdditiveBoundV2`.

---

## 4. Unmapped references (outside IUTIV/ABCBridge but used by/using these nodes)

Search: `grep -l "ABCFrontier\|Cor312ToABCBridgeInterface\|abcConjecture\|IQHull\|ABCConjecture"`
over LeanFormal/** excluding the two dirs produced 385 hits (plus tmp paper). Grouped:

- **IUT III Cor 3.12 hull layer** (producers/consumers of `IQHullLogVolumeInterface`):
  `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/*` — SourceHullCompactnessReduction,
  IQCarrierHaarData, IQCarrierConcreteModel, SourceHullInterfaceDischarge,
  SourceHullNormalizationConditionalClosure, CertificateHullWiring*, CardHullReal*,
  HaarTranslate*, HullDeterminantLogVolumeReduction, LocalFieldProductHull, ...
- **IUT III Theorem 3.11 layer**: `Theorem311/HullDirectednessCovolumeSignProbe`,
  HullLambdaDilationLayer, HullPresentationAlternativeProbe, QRegionCarrierInterface,
  SourceOneCircUGeometry.
- **IUT II/III Kummer/theta**: `IUTII/Kummer/SourceLogShellIQTensorPacket`.
- **Project root**: `Project.lean` imports IQHull layer.
- **tmp/sheaf/xif paper consumers**: Cor312ComparisonRegionV2Actual, AbsTopIII05RefinedActual,
  Mzk1HullEInputsActual, Mzk1Cor312ToABCConsumerActual (parked per Lead A409),
  S3171IUTIVSection1* display/estimates, S3178 gate rows, AG14/AG15 consumers.
These are the interface/consumer edges the skeleton graph should grow next; they are NOT
currently part of the 178-node compile graph here.

---

## 5. Coverage and next extension nodes

- Compile coverage: 178 modules; oleans fresh for 172; **MISSING**: ABCGap2FiniteC3Supply,
  AdicCompletionChineseRemainderAxiomProbe, AdicCompletionRingEquivAxiomProbe,
  FinitePlaceHolomorphicDifferentBase; **STALE**: FinitePlaceLocalInclusionTensorization,
  FinitePlaceThetaPilotScaledRegion.  No actual `sorry`/axiom declarations (grep hits are
  documentation text); probes with missing oleans are not nodes.
- IUT IV: 205 theorems / 31 defs; only two PENDING `Obligation` records (Section1/2); REAL
  estimates are usable as-is.
- ABCBridge: 7 IFACE + 2 PENDING nodes in Bridge; 1 PENDING in Geometry; the rest are
  concrete definitions/theorems (ports/adaptations) — reuse-as-is, but their *paper
  identification* is not claimed.
- To close ABC target, attach in this order (no new math beyond paper):
  1. prove the two `Cor312EpsilonArithmeticComparison` gaps (IUT IV §2 height comparison /
     region log-volume), which converts `cor312ToABCBridge_abcConjecture` into an
     unconditional theorem;
  2. feed them from `Cor312ComparisonGapReduction/SupplyLayer` reduced inputs and the
     hull/carrier layer (`IQHullLogVolumeInterface` + Cor 3.12 finiteness + carrier
     realization), not from the calibrated model;
  3. prove/replace the ABCFrontier clauses if the frontier route is kept (currently IFACE);
  4. connect the IUT IV §1 display (`S3171...`) to the §2 comparison gaps — the missing
     §1->§2 paper edge;
  5. supply explicit PNT constants and the missing §1 objects listed in
     `coord/FOUNDATIONS-IUTIV.md` (Prop 1.1/1.2/1.4/1.5/1.8, Thm 1.10 actual estimate).

---

## 6. Cross-references

`coord/FOUNDATIONS-IUTIV.md` (REAL/MODEL/IFACE/gap inventory),
`coord/IUTIV-SECTION1-PLAN.md` (Thm 1.10 display plan),
`coord/IUT-EXTERNAL-OBJECTS-INVENTORY.md` §L8,
`coord/OPEN-HARD-PROBLEMS.md`, `coord/CURRENT-HARD-POINTS.md`.
TSV edge list: `coord/skeleton-iutiv-abcbrige-edges.tsv`.
Status: no closure claims; GATE NOT PASSED; binding HOLD; pins 14041.

---

## 7. Pins, merge status, E-5/IUT IV edge updates (A430)

- Canonical gate pin: **FINAL PIN V150@18248/CFC6CE08**; GATE NOT PASSED; binding HOLD;
  L8 FROZEN; registry 14041 / record 18800 (coord/STATE.md 23:59).
- This skeleton + TSV (coord/skeleton-iutiv-abcbrige-edges.tsv, 25128B) are the IUTIV/ABCBridge
  node-graph source; merged into coord/MASTER-SKELETON.md §1 FINAL CHAIN (G0-G8), §2 layered
  graph L4, §3 node table N7/N8, §6 merge register (S5 FOUNDATIONS-IUTIV).
- REAL-object citable evidence (E-5/IUT IV edges):
  * compile/olean coverage re-checked for all 178 modules (172 fresh; 4 MISSING, 2 STALE — see §5);
  * axiom evidence probe tmp/sheaf/xif/paper/_FOUNDATIONS-IUTIV-CitableProbe.lean EXIT=0
    (results:210254), trio [propext, Classical.choice, Quot.sound] for deg_pullback, ndeg_pullback,
    iutIVProp17, iutIVProp21ii_theta_two_sided_eventually, processionAverage_le,
    stepVPaperLogVolumeBound, measure_hull_lt_top, hull_logVolume_lt_top,
    sum_completionNormDegree_eq_fieldDegree, cor312ToABCBridge_abcConjecture;
  * FOUNDATIONS-IUTIV.md extended to 27163B: §6 REAL closure table (R1-R19, file:line +
    declarations + citable + REUSE-AS-IS vs EXTEND), §7 MODEL/IFACE table (M1-M5, I1-I9),
    §8 extension plan (10 ordered items; no new math).
- E-5/IUT IV edges status for E-EXTENSION-PLAN.md E-5: existing closures unchanged
  (S3171 statement/estimates/inputs/display + UniformHeightConsumer); missing layer remains
  (b) UndilatedHeightBound + (c) UndilatedRegionBound named; the §1-display -> §2-comparison
  edge is still a GAP (no Lean theorem; paper-level task).
- Remaining integration gaps in this graph: 4 MISSING oleans (ABCGap2FiniteC3Supply,
  AdicCompletionChineseRemainderAxiomProbe, AdicCompletionRingEquivAxiomProbe,
  FinitePlaceHolomorphicDifferentBase), 2 STALE (FinitePlaceLocalInclusionTensorization,
  FinitePlaceThetaPilotScaledRegion); IUTIV Section1/2 PENDING obligations are bookkeeping
  rows (their REAL theorems are proved); Bridge has 7 IFACE + 2 PENDING nodes
  (IUTToABC.cor312ToABCBridge pending; Cor312ToABCCards pending).

Status: no gate edit; no closure claims; GATE NOT PASSED; binding HOLD; pins 14041.
