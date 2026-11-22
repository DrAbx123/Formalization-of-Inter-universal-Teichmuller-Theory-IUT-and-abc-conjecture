import tmp.sheaf.xif.paper.S3119OverAutoAlgHomActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3119OverAutoAlgHomActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt
namespace LeanFormal.IUT.XiFPaper.S3119AutoClassificationProbeAdapted
set_option backward.isDefEq.respectTransparency false

variable {l : PrimeGeFive}

#check S1348CoordinateRing
#check S1348PointAlgHom_X0
#check S1348PointAlgHom_X1
#check S1348_aeval_affinePolynomial
#check S1348_aeval_affinePolynomial_eq_zero
#check S3119NegInvolutionAlgEquiv
#check S3119AlgHomOfOverAuto
#check Spec.map_surjective
#check Spec.map_injective
#check Spec.map_eq_id

theorem S3119OverAutoAlgHom_classification :
    S3119OverAutoAlgHomClassificationTarget (l := l) := by
  intro β

end LeanFormal.IUT.XiFPaper.S3119AutoClassificationProbeAdapted
end
