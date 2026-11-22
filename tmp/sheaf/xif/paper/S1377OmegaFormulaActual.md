# S1377: omega formula and the exact elliptic-net bridge

Date: 2026-10-31 (Asia/Shanghai)
Workspace: D:\lean

## Deliverables

| file | SHA256 | status |
|---|---|---|
| tmp/sheaf/xif/paper/S1377OmegaFormulaActual.lean | 1D2C3E7E185135F3213EB3E5270AEA15EA8F28E12C4D710132BA6A3002B86A60 | EXIT=0 |
| tmp/sheaf/xif/paper/S1377OmegaBase.lean | 8AD874B9082E01D6103AC0DE9186177CD5EEADC40BAB59A9AA7AA974B2C3E2A4 | EXIT=0 |

Compile (both succeed):

    lake env lean tmp/sheaf/xif/paper/S1377OmegaFormulaActual.lean

and, avoiding Lake reconfiguration under load,

    # LEAN_PATH must have .lake/packages/mathlib/... before .lake/build/lib/lean
    lean -R . -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1377OmegaFormulaActual.olean \
      tmp/sheaf/xif/paper/S1377OmegaFormulaActual.lean

Axiom footprint of all main results: propext, Classical.choice, Quot.sound.
No sorry/admit/axiom/opaque.

## What is proved (no hypotheses beyond those displayed)

1. wCoord_add_of_X_ne: the auxiliary addition recursion
   w(A+P) = (w(P)(x_A - x_{A+P}) - w(A)(x_P - x_{A+P}))/(x_P - x_A)
   for A = (u,v), P = (x,y), x_A != x_P, from Mathlib's
   WeierstrassCurve.Affine.addY_sub_negY_addY.

2. xDiff_succ / xDiff_pred: the point-level differences
   Phi_n/W_n^2 - Phi_{n-1}/W_{n-1}^2 = -W_{2n-1}/(W_n^2 W_{n-1}^2),
   Phi_{n-1}/W_{n-1}^2 - x = -W_n W_{n-2}/W_{n-1}^2,
   from phi_eval and the odd recurrence.

3. omega_step_algebra: the algebraic step
   f/a^4 = -d/b^4 + (g - d/b^4)(e/(a^3 c))
   from the two even recurrences, the odd recurrence, and the single
   elliptic relation Rel_3(n,2,n-1):
   b^2 c F - a^2 B E = g^2 e.

4. w_recursion_algebra: the rational rewriting from the geometric recursion
   to the displayed form.

5. omegaFormula_two: the unconditional n = 2 case
   w(2P) = psi_4(P)/psi_2(P)^4 (curve-equation identity
   prePsi_4 = (a_1 B + 2A) prePsi_3 - B^4).

6. rel3_of_ellipticNet: Mathlib's IsEllipticNet at the evaluated sequence
   implies Rel_3; rel3_special specializes to (n,2,n-1).

7. xCoordinate_and_omega_of_ellipticNet: the simultaneous induction.  For all
   n >= 1, if the evaluated sequence n |-> psi_n(P) is an elliptic net and
   psi_1(P),...,psi_{n+1}(P) != 0, then
     x(nP) = Phi_n(P)/psi_n(P)^2
     w(nP) = 2 y(nP) + a_1 x(nP) + a_3 = psi_{2n}(P)/psi_n(P)^4.

8. Corollaries xCoordinateFormula_of_ellipticNet,
   omegaFormula_of_ellipticNet, S1372XCoordinateFormula_of_ellipticNet,
   S1372OmegaFormula_of_ellipticNet.

9. S1377Rel3AtPoint: the exact (weaker) algebraic input actually used,
   and S1377Rel3AtPoint_of_ellipticNet.

## Exact first missing EDS lemma

    S1372EllipticNetAtPoint W x y :
      IsEllipticNet (fun n : Z => W.evalDivisionPolynomial x y n)

i.e. the evaluated division-polynomial sequence is an elliptic net.  Equivalently,
the missing Mathlib theorem is IsEllipticNet (normEDS b c d) / the passage from
the even-odd recurrence to the elliptic relation; Mathlib 4.32.2 has the
definition and normEDS recurrences but the theorem is a TODO in
Mathlib/NumberTheory/EllipticDivisibilitySequence.lean.

The local port tmp/sheaf/xif/paper/S1372EllSequencePort.lean does NOT compile
against Mathlib 4.32.2.  Observed API drift (approx. 40 errors):
- SubNegMonoid/AddGroup section variables that are used only in proofs must be
  brought in with include (Lean 4 no longer auto-includes them);
- Submonoid.closure_induction now has a membership-dependent motive;
- Tuple.sort needs import Mathlib.Data.Fin.Tuple.Sort;
- Int.negOnePow_eq_iff needs Mathlib.Algebra.Ring.NegOnePow;
- Int.odd_iff_not_even renamed (Int.not_even_iff_odd);
- several convert_to/simp/rw calls changed API.
The corrected mathlib PR #13155 (elliptic relations from even-odd recursion)
is still unmerged; porting/fixing it is the direct next step.

## Intermediate nonvanishing gap

The theorem assumes psi_k(P) != 0 for 1 <= k <= n+1.  The target
S1372OmegaFormula only assumes psi_n(P) != 0.  Removing the intermediate
hypothesis needs either

  (a) torsion detection: psi_k(P) = 0 iff kP = 0, and reduction of n modulo
      the order of P, or
  (b) a generic-point / specialization argument proving the polynomial identity
      first over the function field, then specializing.

Both are absent from Mathlib 4.32.2 and are not assumed in S1377.

## Next executable step

Fix the ported elliptic-relation induction (S1372EllSequencePort.lean) against
the current API, or prove only the special relation Rel_3(n,2,n-1) for the
division-polynomial net; then S1372EllipticNetAtPoint follows, and S1377 gives
the unconditional (modulo torsion reduction) omega formula.
