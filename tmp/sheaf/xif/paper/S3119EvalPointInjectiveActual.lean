import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
namespace LeanFormal.IUT.XiFPaper.S3119EvalPointInjectiveActual
set_option backward.isDefEq.respectTransparency false
variable {l : PrimeGeFive}

/-- The affine evaluation map on K-points of the S1348 coordinate ring is
injective: two K-algebra homs with the same projective point agree on x and y,
hence on the whole coordinate ring. -/
theorem S1348EvalPoint_injective :
    Function.Injective (S1348EvalPoint (l := l)) := by
  intro ψ θ h
  have h' := congrArg (fun P =>
    WeierstrassCurve.Projective.Point.toAffineLift
      (W := (S1348Curve l).toProjective) P) h
  simp only [S1348EvalPoint,
    WeierstrassCurve.Projective.Point.fromAffine_some,
    WeierstrassCurve.Projective.Point.toAffineLift_some] at h'
  rw [WeierstrassCurve.Affine.Point.some.injEq] at h'
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact h'.1
  · exact h'.2

#check S1348EvalPoint_injective
#print axioms S1348EvalPoint_injective
end LeanFormal.IUT.XiFPaper.S3119EvalPointInjectiveActual
end
