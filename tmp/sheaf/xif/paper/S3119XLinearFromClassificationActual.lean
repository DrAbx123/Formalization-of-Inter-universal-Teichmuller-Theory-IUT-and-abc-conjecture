import tmp.sheaf.xif.paper.S3119XCoordinateFixingTargets
import tmp.sheaf.xif.paper.S3119AutoClassificationTargets
import tmp.sheaf.xif.paper.S3119NegInvolutionCoreActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119AutoClassificationTargets
open LeanFormal.IUT.XiFPaper.S3119XCoordinateFixingTargets
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt
namespace LeanFormal.IUT.XiFPaper.S3119XLinearFromClassificationActual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
variable {l : PrimeGeFive}

theorem S3119NegInvolution_x0 :
    S3119NegInvolutionAlgEquiv (l := l) (S3119x0 (l := l)) =
      S3119x0 (l := l) := by
  rw [S3119x0, S3119NegInvolutionAlgEquiv]
  change S3119NegQuotientHom (l := l)
    (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
      (MvPolynomial.X 0)) =
    Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
      (MvPolynomial.X 0)
  rw [S3119NegQuotientHom_mk, S3119NegPolyHom_X0]

theorem S3119XLinear_of_autIdOrNeg
    (h : S3119AutIdOrNegTarget (l := l)) :
    S3119XLinearTarget (l := l) := by
  intro φ
  rcases h φ with hφ | hφ
  · subst hφ
    exact ⟨0, 1, by simp⟩
  · subst hφ
    exact ⟨0, 1, by rw [S3119NegInvolution_x0]; simp⟩

#check S3119NegInvolution_x0
#check S3119XLinear_of_autIdOrNeg
#print axioms S3119XLinear_of_autIdOrNeg
end LeanFormal.IUT.XiFPaper.S3119XLinearFromClassificationActual
end
