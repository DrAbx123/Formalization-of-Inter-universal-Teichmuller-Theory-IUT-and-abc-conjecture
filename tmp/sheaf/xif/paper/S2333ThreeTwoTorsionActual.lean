import tmp.sheaf.xif.paper.S2327TorsionTransportActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-! # S2333: three rational 2-torsion -- exact missing API

Mathlib provides `WeierstrassCurve.twoTorsionPolynomial`, whose roots over a
splitting field are the X-coordinates of the nonzero 2-torsion points, and
`WeierstrassCurve.Affine.Point.mk` for an equation-satisfying pair.  However
the tree has no lemma identifying `twoTorsionPolynomial.eval x = 0` with
`W.Equation x 0` (the Mathlib file only states the root description in
comments / TODO), and no 2-torsion point constructor.

Therefore constructing three distinct nonzero 2-torsion points, their rational
affine representatives, and their transport to `SideKPoint T b` still needs:
1. roots of the cubic over the algebraic closure;
2. `Equation x 0` from each root;
3. `torsion23_rational` representatives;
4. `Affine.Point.baseChange` F -> Fv -> LF;
5. `Projective.Point.toAffineAddEquiv` and `pointTransport_galois` (S1550);
6. `IsGaloisFixed`, `2 • P = 0`, pairwise distinctness.

No witness is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2333ThreeTwoTorsionActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual
open LeanFormal.IUT.XiFPaper.S2296TateBaseUnitActual
open LeanFormal.IUT.XiFPaper.S2327TorsionTransportActual

universe u

#check WeierstrassCurve.twoTorsionPolynomial
#check WeierstrassCurve.Affine.Point.mk
#check WeierstrassCurve.Affine.Point.baseChange
#check WeierstrassCurve.Projective.Point.toAffineAddEquiv
#check pointTransport_galois
#check S2296ThreeRationalTwoTorsion

end LeanFormal.IUT.XiFPaper.S2333ThreeTwoTorsionActual

end
