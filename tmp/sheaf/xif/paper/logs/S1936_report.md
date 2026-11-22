# S1936: the homogeneous decomposition of the S1925 projective closure is a graded-ring decomposition

Date: 2026-11-01.
Source: tmp/sheaf/xif/paper/S1936GradedResidualActual.lean
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1936GradedResidualActual.olean

## Verification

- Build command: lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1936GradedResidualActual.olean tmp/sheaf/xif/paper/S1936GradedResidualActual.lean
- EXIT=0, 0 errors, 0 warnings.
- Source SHA256: 227D9F55050BD4BDAD82A0753FC38C3BAAB500A9AD0CE1037243FAEC2F4A6704
- Source bytes: 13506
- Olean SHA256: D8E9D168C390438223DC54572C4B0479EB923E634098FC941C40227A6B922F9F
- Olean bytes: 288080
- Olean import re-check: EXIT=0 (a scratch module imports the olean, #checks the three main
  declarations, and elaborates the graded-ring instance for Wang).
- All #print axioms report only [propext, Classical.choice, Quot.sound]; no sorryAx, no axiom
  declaration, no placeholder.

## What is proved unconditionally

Generic part (R a commutative ring, F in R[X,Y,Z] homogeneous of degree 3):

1. decP_coeAddMonoidHom:
   DirectSum.coeAddMonoidHom (CohomGr F) (decP F p) = quo F p.
   Method: DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum over the support of
   decP p, extension to range (p.totalDegree + 1), MvPolynomial.sum_homogeneousComponent.
2. decA_leftInverse:
   Function.LeftInverse (DirectSum.coeAddMonoidHom (CohomGr F)) (decA F hF).
3. decP_eq_dfinsupp_single:
   for p homogeneous of degree n, decP F p = DFinsupp.single n <quo F p, _>.
4. decA_of_homogeneous / decA_of_mem:
   decA F hF is DirectSum.of (= DFinsupp.single) on a homogeneous class.
5. decA_rightInverse:
   Function.RightInverse (DirectSum.coeAddMonoidHom (CohomGr F)) (decA F hF).
   Method: both sides are additive maps out of the direct sum; DirectSum.addHom_ext reduces
   to a single summand, closed by decA_of_mem.
6. S1925DecompositionResidual_holds:
   S1925DecompositionResidual F hF, i.e. the exact residual named in S1925 is closed.
7. S1936GradedRing F hF : GradedRing (CohomGr F).
   This is exactly S1925GradedRingOfResidual F hF applied to
   S1925DecompositionResidual_holds F hF.
8. S1936Decomposition : DirectSum.Decomposition (CohomGr F), with decomposition map decA.
9. S1936IsInternal : DirectSum.IsInternal (CohomGr F).

Actual model (F' = S1726K, Wang the S1925 homogeneous Weierstrass polynomial):

10. Global instance S1936GradedRingWang : GradedRing (CohomGr Wang).
11. S1936Proj = Proj (CohomGr Wang), S1936AffineChart = Proj.awayι ... (D_+(Z)),
    S1936AffineChart_isOpenImmersion, S1936AffineChart_opensRange.
12. The S1925 objects S1925Proj, S1925AffineChart, S1925AffineChart_isOpenImmersion and
    S1925AffineChart_opensRange now elaborate with this instance; this is checked in-file.

## Exact first missing after S1936

None for the S1925DecompositionResidual / GradedRing target: it is closed.

The remaining named residuals of the S1925 compactification are unchanged and are not
addressed in this file:

- S1925ChartIso : (Away WGr Zbar) ≃+* S1726CoordinateRing (chart identification);
- S1925DenseChart : Dense (Proj.basicOpen WGr Zbar) (density of the affine chart).

## Notes

- No Mathlib graded-quotient construction is used; the decomposition is the explicit one
  built in S1925, and the two inverse laws are proved here.
- The right inverse is genuinely a DFinsupp.single statement: outside degree n every
  homogeneous component of a degree-n homogeneous polynomial vanishes.
- The left inverse uses DFinsupp.sum, not a new quotient-ring theorem.
