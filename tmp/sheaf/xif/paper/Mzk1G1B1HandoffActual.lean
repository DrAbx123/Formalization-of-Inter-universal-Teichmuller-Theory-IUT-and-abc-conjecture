/-
# B1 / G-C handoff page (pure documentation, no declarations)

## Closed pieces (all watchdog DONE, axioms exactly [propext, Classical.choice, Quot.sound])

### 1. psi and hPolyL layers (unconditional)
- Mzk1G1PsiGlueCompatActual.psi / psi_ι_false / psi_ι_true
- Mzk1G1PsiFixedActual.psiFixed / psiFixed_ι_false / psiFixed_ι_true
- Mzk1G1PsiHPolyLambdaActual.hPolyL / hPolyL_def / p1Inv / phiFixedL
- Mzk1G1PsiHPolyLambdaFactsActual.phiFixedL_ι_false / phiFixedL_ι_true / phiFixedL_chart0

### 2. Finite half of B1 (A): boundary preimage of phiFixedL is finite
- Mzk1G1PhiFixedLLambdaPointActual.phiFixedL_fiber_finite_p1Zero / _p1One
- Mzk1G1PhiFixedLInfinityActual.phiFixedL_fiber_finite_p1Infinity
- Mzk1G1PhiFixedLChart0Actual.phiFixedL_chart0_eq / _apply / _fibre_subset / _fiber_finite
- Mzk1G1PhiFixedLFiberActual.phiFixedL_fiber_subset / _fiber_finite_of_chart0
- Mzk1G1PhiFixedLFiberFiniteActual.phiFixedL_fiber_finite_of_boundary
- Mzk1G1PhiFixedLBoundaryActual.phiFixedL_boundaryPreimage_finite (n T h hh) (hn : 0<n) (hT) (hdeg : 0<h.natDegree)
- support: Mzk1G1PsiPhiFixedLZeroFiberActual.finite_primes_of_coord_zero;
  Mzk1G1PsiProtectedDivisorFiniteActual.protectedDivisor_quot_finite(_of_mem);
  Mzk1G1PsiFiberFiniteActual.finite_primes_of_finite_quotient;
  Mzk1G1PsiFiberFiniteC2Actual.finite_primes_of_hPolyLam

### 3. Scheme-level branch contract
- Mzk1G1PhiFixedLBranchSupportActual.branch_phiFixedL_comp_subset (grace branch_comp_subset)
- Mzk1G1PhiFixedLBranchSupportActual.branch_phiFixedL_comp_subset_boundary
- Mzk1G1PhiFixedLBranchSupportActual.phiFixedL_branch_subset (n T h hh) (hpsi) (hb)
  where hpsi : hPolyL h hh '' Branch (psiFixed n T) subset boundarySetGlued
        hb   : Branch (hPolyL h hh) subset boundarySetGlued

### 4. Scheme/value dictionary on the lambda chart (new, 00:36:22)
- Mzk1G1PhiFixedLChart0BoundaryActual.chartMorphism0_mem_boundarySetGlued_iff
    : chartMorphism0 a p in boundarySetGlued iff a in p.asIdeal or a - 1 in p.asIdeal
- phiFixedL_chart0_point_eq : point form over evalAt
- phiFixedL_chart0_point_mem_p1Zero_iff / _mem_p1One_iff / _mem_boundary_iff / _notMem_boundary_iff
- phiFixedL_chart0_ram_mem_boundary_of_value
- evalAt_apply_aeval : evalAt a q = Polynomial.aeval a q

### 5. Assembly interfaces
- Mzk1G1B1ProducerAssemblyActual.b1FiniteProducer_of_inputs / b1Witness_of_boundaryPreimage_finite
- Mzk1G1B1FinalActual.b1FiniteProducer_of_data (T-dependent, route-faithful)
- Mzk1G1B1FinalActual.b1FiniteProducer_of_DT_data (adds the T subset DTFixed guard; needs henry analytic h)
- Mzk1G1PsiM2BranchDataActual.hbranch_data_of_target / hbranch_data / h0_data (h = M2 target q)

## Still open (precise gaps)
1. t-chart (second chart) scheme/value dictionary: needed to discharge hpsi at scheme level.
2. hb : Branch (hPolyL h hh) subset boundarySetGlued: no scheme-level donor for hPolyL
   ramification/critical values in the tree; remains an explicit input.
3. B (analytic h existence): henry/kurt M2AnalyticTarget for the actual branch set;
   Mzk1G1PsiM2AnalyticAssemblyActual gives m2AnalyticTarget_of_witness etc.
4. C (havoid): andrew lane; use phiFixedL_chart0_point_notMem_boundary_iff plus the unit
   argument for D_T.  Mzk1G1B1TAvoidFinalActual must be repaired first (it is red).
5. B1FiniteProducer itself is unchanged: forall T exists phi with finite boundary preimage
   and avoidance on T (Mzk1G1PsiB1Actual).

## Do not import
- Mzk1G1B1TAvoidFinalActual (red, axioms contain sorryAx).
- dag/watchdog/emmy-backup/Mzk1G1PhiFixedLSchemeBranchActual.deprecated.lean

## Process notes
- module docstrings (/ -! ... - /) must come after imports, not before.
- after rw always close with rfl explicitly, otherwise error recovery may inject sorryAx.
- p1Infinity is a point SET (localChartInf '' chartPoint 0), not a point.
- olean read failures / std::bad_alloc are concurrent-OOM pseudo failures: touch and retry.
-/