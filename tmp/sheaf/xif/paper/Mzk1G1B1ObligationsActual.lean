/-
# B1 / G-C outstanding obligations (status as of 19:10, v8)

Per Lead ruling: explicit parameters and conditional interfaces are OBLIGATIONS.  They are not
counted as closed nodes and must not be packaged as results.  Status: OPEN / REDUCED /
CERT-AVAILABLE / DONE.

## O1. hpsi (branch inclusion, first half)
  hpsi : hPolyL h hh '' Branch (psiFixed n T) subset boundarySetGlued
  Status: REDUCED (DONE as a reduction): Mzk1G1PsiHPsiReductionActual (04:22:02)
    hpsi_branch_reduction : hPolyL h hh '' Branch (psiFixed n T) subset boundary
      <-> hPoly h hh '' (p1Inv '' Branch (psiFixed n T)) subset boundary
  supported by Mzk1G1PsiP1InvBoundaryActual (04:14:29, 21 theorems):
    p1Inv_image_boundarySetGlued, p1Inv_image_subset_iff, p1Inv_inv, hPolyL_image_boundary_iff.
  Remaining: the hPoly-level inclusion, which needs O3(ii).

## O2. hb (branch inclusion, second half)
  hb : Branch (hPolyL h hh) subset boundarySetGlued
  Status: OPEN.  Blocked on O3(ii) (no scheme-level donor for hPolyL ramification).

## O3. P1ValueDictionary (three fields)
  (i) chart value dictionaries: DONE (lambda: Mzk1G1PhiFixedLChart0BoundaryActual 00:36:22;
      t-chart: Mzk1G1PhiFixedLChartInfBoundaryActual 01:00:39).
  (ii) scheme-level bridge Branch (hPoly h hh) = critical values of h union {infinity}:
      (a) VALUE LAYER: DONE (grace 04:35:08) Mzk1G1B1O3ValueLayerActual.o3a_aeval_of_derivative_zero
          and o3a_criticalValues_subset (criticalValues of the M2 target inside {0,1});
          note: import via the pre-ported tmp.external.ported.tauceti_belyi_core ...CriticalValues;
      (b) SCHEME LAYER Branch(hPoly) -> critical value set: OPEN, recorded as an explicit
          obligation (grace; branch_hPolyL_eq = Branch(hPolyL) = p1Inv '' Branch(hPoly) in progress).
      Available inputs:
      Mzk1G1PhiFixedLChartInfBoundaryActual.chartMorphismInf_comp_hPoly, deduped with
      Mzk1G1B1P1DictActual.hPolyL_localChart0_apply (grace 04:18:06) on the lambda side.
  (iii) hval_branch : Branch (psiFixed n T) subset val^{-1} (branchFixedFinite T):
      OPEN (grace + henry coe_branchFixedFinite).
  WARNING: the phiFixedL t-chart formula t' = h(v) is FALSE (counterexample h = 1 + X,
  T = {0}, r = 1: true lambda' = 2, false form gives lambda' = 1/2).  Use the psiFixed-level
  statements psiFixed_qPiece_notMem_boundary_iff / psiFixed_comp_hPoly_qPiece_mem_boundary_iff.

## O4. LocallyOfFinitePresentation instances
  [(psiFixed n T)], [(hPoly h hh)], [(hPolyL h hh)], [(phiFixedL n T h hh)]
  Status: DONE (unconditional).  Mzk1G1B1HPolyLoFPActual (05:26:19):
     evalAt_finitePresentation, locallyOfFinitePresentation_chartMorphism0,
     hPolyChartInf/_Chart1/_Chart0_locallyOfFinitePresentation,
     hPolyLocallyOfFinitePresentation_of_fp (h) (hh) : LoFP (hPoly h hh),
     hPolyL_locallyOfFinitePresentation_of_fp (h) (hh) : LoFP (hPolyL h hh).
   (Earlier partial: hPolyL part from IsIso p1Inv, 05:14:26.)
   - hPoly part: REDUCED to the single ring-theoretic input
     RingHom.FinitePresentation (evalAt h); the geometric half is proved:
     Mzk1G1B1HPolyBranchSchemeActual.hPoly_locallyOfFinitePresentation_of_charts
     (via IsZariskiLocalAtSource.iff_of_openCover and hPoly_iota_c0/c1/c2),
     plus locallyOfFinitePresentation_specMap / _chartMorphismInf.
     In flight: Mzk1G1B1HPolyLoFPActual.
   - psiFixed / phiFixedL instances: OPEN (still typeclass parameters).

## O5. T subset DTFixed selection  (NOT closed)
  hT : (T : Set (fermatCurveScheme n)) subset DTFixed n Tr
  Status: OPEN in general (route 4.1 RR / grace psiGeneral); CERT-AVAILABLE only for chart-0
  rational points:
    Mzk1G1B1DTSubsetActual.chart0_point_mem_DTFixed / _of_rational (grace 04:08:58).
  andrew's Mzk1G1B1Chart0Actual uses this certificate; general geometric T: OPEN (route 4.1).

## O6. analytic h existence (B side)
  hbranch : forall T, exists Tr h hh, Tr.Nonempty and 0 < h.natDegree
  Status: SHAPE DONE: Mzk1G1PsiM2BranchDataActual.b1_hbranch_uniform (00:56:19).
  Analytic content = M2AnalyticTarget: OPEN (henry/kurt, route 4.3).

## O3(ii)(b) latest status (v7, 13:50:24)
  Mzk1G1B1HPolySmoothLocusActual (DONE 05:50:24, 22 declarations) reduces hbridge to ONE
  explicit obligation:
    SmoothCriterion h := forall q, q in smoothLocus (chartMorphismInf h) <-> derivative h notin q
  and closes the degenerate case derivative h = 0 unconditionally.
  IMPORTANT CORRECTION: the donor-shaped obligation
    hpts : Branch (hPoly h hh) subset chartMorphismInf h '' derivativeZeroSet h
  is FALSE for deg h >= 2 (it would force Branch (hPoly) subset range localChartInf,
  formalised as branch_subset_range_of_hpts, but 0 is a critical value and t = infinity is a
  ramification point with value p1Zero).  The correct statement adds the harmless point p1Zero:
    Branch (hPoly) subset chartMorphismInf h '' derivativeZeroSet h union p1Zero
  and the WIRED reductions are:
    hbH_of_value_and_ram_union_p1Zero (hval) (hpts) : Branch (hPoly) subset boundarySetGlued
    hbH_of_hbridge_and_out (hval) (hbridge) (hout)   : Branch (hPoly) subset boundarySetGlued
    branch_image_ram_inter_chart0_subset (hbridge)   : the shape hbH really needs
  Remaining explicit obligations:
    (a) SmoothCriterion h -- ACCEPTED AS EXPLICIT OBLIGATION (v8, Lead ruling).
        Diagnosis: same-type double Algebra diamond (evalAt h : Q[lambda] -> Q[lambda]);
        Mathlib's algebraOfLiesOver is deliberately not an instance.  Two fixes recorded:
        (i) irreducible type synonym for Q[lambda] plus transport;
        (ii) submersive presentation Q[lambda][T,Z]/(lambda - h(T), h'(T)Z - 1)
             (Jacobian -h'^2, made a unit by the second relation) =>
             IsStandardSmoothOfRelativeDimension 0 => Algebra.Smooth;
             missing: the graph iso Q[lambda][T]/(lambda - h(T)) ~ Q[t] and
             Algebra.basicOpen_subset_smoothLocus_iff.
        Files: Mzk1G1B1SmoothCriterionActual (18:42:08, five evalAlg helpers + diagnosis),
               Mzk1G1B1SmoothCriterionSubmActual (route (ii), in progress).
        Only direction B + the Spec/stalk bridge are needed; direction A (Kaehler) is NOT needed.
    (b) hout : DONE unconditionally 10:32:11 (Mzk1G1B1HoutActual, 9 declarations);
        key results: compl_range_localChartInf_eq_p1Zero (equality), hPoly_image_p1Zero_subset,
        hRev_not_mem_of_X_mem.
  => O3(ii)(b) consumer should use hbH_of_value_and_ram_union_p1Zero / hbH_of_hbridge_and_out,
     NOT the older hbH_of_value_and_ram.

## v9 update (21:12): submersive route SUCCEEDED for the ring core

The route (ii) above was carried out (Mzk1G1B1SmoothCriterionSubmActual, DONE 11:15:00):
  smoothModelRel, smoothModelPre : PreSubmersivePresentation,
  smoothModel_det : jacobiMatrix.det = -(h' * h'), smoothModel_deriv_isUnit,
  smoothModel_jacobian_isUnit, smoothModelPresentation, smoothModel_isStandardSmooth,
  smoothModel_smooth, smoothModel_formallySmooth,
  isSmoothAt_of_formallySmooth, smoothAt_of_derivative_notMem (h) (hG : GraphIso h) (q) (hq).
So SmoothCriterion is now reduced to the SINGLE algebra item:
  GraphIso h := Nonempty (smoothModelRing h ~=a[Q[lambda]] Localization.Away (hDerivElt h))
with the graph iso Q[lambda][T]/(lambda - h(T)) ~ Q[t] as its only missing ingredient.
P1/P3 sides of it are DONE (Mzk1G1B1GraphIsoActual 11:24:24): away_algEquiv_quotient,
isLocalization_away_quotient, graphIso_lambda_side, and the chartT variants; Mathlib's
Localization.awayEquivAdjoin + AdjoinRoot-definitional-equality make them one-liners.
The assembly of graphIso_holds by two-sided AlgEquiv.ofAlgHom is written in
Mzk1G1B1GraphIsoModelActual (bridge identities hAtT_eq_aeval, hDerivAtT_eq_aeval,
pderiv_aeval_X0_derivative, map_aeval_apply, smoothModelEval_X0 all proved); only local tactic
steps near toAway_chartToModel_X / toAway_chartToModel remain (see
coord/B1-GRAPHISO-P2-HANDOFF.md).

## v10 update (21:58): GraphIso CLOSED; adapter for the PsiPoly line added

(1) GraphIso is now PROVED unconditionally:
    Mzk1G1B1GraphIsoModelActual.graphIso_holds (h : Polynomial Q) :
      GraphIso h                                   -- DONE 13:21:22, three axioms
    Mzk1G1B1GraphIsoModelActual.graphIsoEquiv (h) :
      smoothModelRing h ~=a[Q[lambda]] Localization.Away (hDerivElt h)
    Technical note that cost several attempts: IsLocalization.Away.lift must be used in
    APPLIED form only (a term of the localization as an explicit argument, so that S comes
    from the argument type and P from the return type).  Naming the result as ->+* / ->a gives
    "Type mismatch" at the application site, while @-explicit or (R:=)(S:=)(P:=) forms blow up
    into 3,000,000-heartbeat timeouts.  See the AUDIT_LEDGER entry of 21:20 for the same lesson.

(2) The last algebraic item on the B1 hbridge path is therefore the SCHEME/STALK bridge
      smoothCriterion_of_chartT (h) (hh) [LoFP (chartMorphismInf h)] :
        Mzk1G1B1HPolySmoothLocusActual.SmoothCriterion h
    being written as Mzk1G1B1SchemeRamBridgeActual (in progress).  Inputs ready:
    graphIso_holds, smoothAt_of_derivative_notMem, smoothLocus_chartInf_eq_specMap,
    mem_chartInf_smoothLocus_iff, smoothCriterion_iff_ram, and the Kahler rank-one material
    in Mzk1G1OmegaActual / OmegaBasis (Omega[Q[t]/Q[lambda]] ~ Q[t]/(h')).

(3) General-T line (replaces the restricted DTFixed form): the interface adapter
      Mzk1G1B1BranchPolyAdapterActual.b1FiniteProducer_of_branchPoly (n) (hn)
        (DTPoly : Finset (curve n) -> Set (curve n))
        (hbranchPoly : forall T, exists h hh, 0 < h.natDegree and T subset DTPoly T and
           h.eval 0 notin {0,1})
        (hcover : forall T, exists Tr, Tr.Nonempty and (T inter DTPoly T) subset DTFixed n Tr) :
        B1FiniteProducer n
    is DONE 13:56:55 (three axioms).  Once grace's Mzk1G1B2PsiPolyActual lands, instantiate
    DTPoly T := zero divisor of psiPoly n T, with hbranchPoly from
    psiPoly_preimage_p1Zero_eq_DTZero + T subset DTZero, and hcover from the inclusion of that
    zero divisor into a rational DTFixed.  The havoid side then needs the DTZero version of
    phiFixedL_T_avoid_data (h(0) outside {0,1} read on the psiPoly zero set).

## v11 update (22:25): reused donors recorded; UL localization, conductor, DTZeroElem

REPO-FIND (do not duplicate): the different/conductor localization layer already exists.
Reused donors, all DONE, with the exact names:
  Mzk1ULDifferentLocalizationActual (DONE 23:21:30):
    multiplicity_differentIdeal_map_atPrime,
    count_normalizedFactors_map_atPrime,
    iutIVProp13ii_normalizedDifferent_le_zLocalization  (paper Prop 1.3(ii))
  Mzk1ULLocalConductorDegActual (DONE 14:13:26):
    localLogF_eq, sum_localLogF_eq_finrank_mul
  Mzk1G1LocalConductorInhabitantActual (DONE 22:37:13)
  Mzk1G1B2PsiPolyDTZeroActual (grace, DONE 14:1x): DTZeroElem, mem_DTZeroElem_iff,
    DTZero_eq_DTZeroElem, DTZeroElemInf, mem_DTZeroElemInf_iff, DTZeroElemAll,
    b1BranchDTZeroElem, b1BranchDTZeroElem_psiPolyCoord
  Mzk1G1B2PsiPolyActual (grace): DTZero, mem_DTZero_iff, b1BranchDTZero

NEW FILES (this lane, arithmetic layer only, orthogonal to the donors above):
  Mzk1ULLocalDifferentizationInterfaceActual: localFSum, rawLocalDelta, localLogD,
    localLogD_mul_localFSum, rawLocalF, localLogF, localLogF_mul_localFSum
    (raw and deg_E normalisations plus the multiply-back wrappers).
  Mzk1ULLocalDifferentizationAdapterActual: delta_v_eq_count_normalizedFactors,
    delta_v_differentIdeal, localLogD_pairing  (projections of the donor lemmas;
    depends on the interface file's olean).
  Mzk1ULFiberAggregateActual: sum_fiber_aggregate, sum_fiber_aggregate',
    sum_le_sum_fiber  (Finset.sum_biUnion under pairwise disjoint fibers).

hbad status (david): hsumF and hsumD are provable from those donors plus the fiber
aggregation; the only genuinely new mathematics is the local support inequality
  (obligation: prop13_local_support)   -- paper Prop 1.3(i), per-place
  log s_vQ <= 2 (log d_vQ + log f_vQ),
which stands on iutIVProp13ii_normalizedDifferent_le_zLocalization but is not derived from
the existing tree material.  The dNo term is NOT provable by per-prime counting: that only
yields coefficient [F:Q], not 2 d_mod.

RULINGS (approved by Lead), recorded for the constant bookkeeping:
  (c) use the F-level S_ar, with the F vs Ftpd difference <= 21 absorbed (paper L1414-1425);
      the 21 must be checked against kurt's C3 constant 56.
  hbad is stated in coefficient-2 form; paper's 2 d_mod form follows from d_mod >= 1 plus
  nonnegativity of the logs (no need for log d = sum (1/p) log d_vQ).

B1 side: b1FiniteProducer_of_branchPoly (DONE 13:56:55) can be instantiated with
  DTPoly T := DTZeroElem n (psiPolyCoord n S),  hbranchPoly from
  b1BranchDTZeroElem_psiPolyCoord,  and hcover (DTZeroElem contained in some DTFixed n Tr)
  as an explicit parameter (obligation: DTFixed_cover) until grace supplies it.

## Closed (no obligations)
- boundary three point fibres + phiFixedL_boundaryPreimage_finite (08:16:13);
- both chart scheme/value dictionaries (00:36:22, 01:00:39);
- phiFixedL_T_avoid_data (AvoidsBoundary from hT and aeval 0 h outside {0,1});
- p1Inv boundary invariance + hpsi reduction (04:14:29, 04:22:02);
- assembly interfaces b1FiniteProducer_of_inputs / b1_hbranch_uniform / b1Witness_of_T_avoid;
- chart-0 rational-point case of B1 (andrew Mzk1G1B1Chart0Actual, in flight).
-/