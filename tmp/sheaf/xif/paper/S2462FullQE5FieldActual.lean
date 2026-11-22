import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual

noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual

#check S1667Curve.toAffine
#check S1667Curve.toAffine.baseChange (AlgebraicClosure ℚ)
#check (S1667Curve.toAffine.baseChange (AlgebraicClosure ℚ)).Point
#check WeierstrassCurve.Affine.Point.xCoord
#check WeierstrassCurve.Affine.Point.yCoord
#check WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xCoord_eq
#check WeierstrassCurve.Affine.Point.xCoord_map
#check WeierstrassCurve.Affine.Point.map
#check WeierstrassCurve.Affine.Point.map_add
#check IntermediateField.adjoin ℚ ({0} : Set (AlgebraicClosure ℚ))
#check IntermediateField.mem_adjoin_iff
#check Algebra.adjoin
