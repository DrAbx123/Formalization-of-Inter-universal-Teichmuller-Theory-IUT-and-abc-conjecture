import tmp.sheaf.xif.paper.S2296TateBaseUnitActual
import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual

/-! # S2327: three rational 2-torsion transport -- exact missing

`T.clauseC.torsion23_rational` is the proposition `AllNTorsionRational 6`: it
says every 6-torsion point over the algebraic closure has an F-rational affine
representative.  It does **not** provide three explicit distinct nonzero
2-torsion points, nor their images in `SideKPoint T b`.

The construction of `S2296ThreeRationalTwoTorsion` therefore needs:
1. three pairwise distinct nonzero 2-torsion points of the base elliptic
   curve over the algebraic closure (e.g. roots of the 2-division polynomial);
2. their rational affine representatives from `torsion23_rational`;
3. base change F -> Fv -> LF, `Projective.Point.toAffineAddEquiv`, and
   `pointTransport_galois` (S1550) to land in `SideKPoint T b`;
4. proofs of `IsGaloisFixed`, `2 • P = 0`, and pairwise distinctness.

None of (1)-(4) is constructed here; no fake witness is produced.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2327TorsionTransportActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual
open LeanFormal.IUT.XiFPaper.S2296TateBaseUnitActual

universe u

#check PuncturedEllipticCurve.Torsion23Rational
#check PuncturedEllipticCurve.AllNTorsionRational
#check S2296ThreeRationalTwoTorsion
#check S2296LCoprimeRepresentative
#check pointTransport_galois

end LeanFormal.IUT.XiFPaper.S2327TorsionTransportActual

end
