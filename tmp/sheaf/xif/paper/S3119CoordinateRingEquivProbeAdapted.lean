import tmp.sheaf.xif.paper.S3119CoordinateRingEquivTargets
import tmp.sheaf.xif.paper.S3119AutoClassificationTargets
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119AutoClassificationTargets
open LeanFormal.IUT.XiFPaper.S3119CoordinateRingEquivTargets
namespace LeanFormal.IUT.XiFPaper.S3119CoordinateRingEquivProbeAdapted
set_option backward.isDefEq.respectTransparency false
variable {l : PrimeGeFive}

noncomputable def S3119Forward :
    (S1348Curve l).toAffine.CoordinateRing →ₐ[S1348K l]
      S1348CoordinateRing l :=
  AdjoinRoot.liftAlgHom
    ((S1348Curve l).toAffine.polynomial)
    (Polynomial.aeval (S3119x0 (l := l)))
    (S3119y0 (l := l))
    (by
      simp [WeierstrassCurve.Affine.polynomial, weierstrassAffinePolynomial,
        S1348AffinePolynomial, S3119x0, S3119y0, Polynomial.eval₂_at_apply,
        MvPolynomial.aeval_def])

#check S3119Forward
end LeanFormal.IUT.XiFPaper.S3119CoordinateRingEquivProbeAdapted
end
