import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
namespace LeanFormal.IUT.XiFPaper.S3119CoordinateRingEquivTargets
set_option backward.isDefEq.respectTransparency false
variable {l : PrimeGeFive}

/-- Mathlib's affine coordinate ring of the S1348 curve (AdjoinRoot). -/
abbrev S3119MathlibCoordinateRing : Type :=
  (S1348Curve l).toAffine.CoordinateRing

/-- Minimal ring-equivalence target: the MvPolynomial quotient is the Mathlib
AdjoinRoot coordinate ring. -/
def S3119CoordinateRingEquivTarget : Prop :=
  Nonempty (S1348CoordinateRing l ≃ₐ[S1348K l]
    (S1348Curve l).toAffine.CoordinateRing)

#check WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq
#check WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis
#check WeierstrassCurve.Affine.CoordinateRing.degree_norm_ne_one
#check AdjoinRoot.liftAlgHom
#check AdjoinRoot.mk_self
#check AdjoinRoot.liftAlgHom_mk
#check S3119MathlibCoordinateRing
#check S3119CoordinateRingEquivTarget
end LeanFormal.IUT.XiFPaper.S3119CoordinateRingEquivTargets
end
