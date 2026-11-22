import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import Mathlib.RingTheory.Ideal.Quotient.Operations
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S3119GeometricCorePrefixAttempt

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped SpecOfNotation
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3119GeometricCorePrefixAttempt
open MvPolynomial
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt

variable {l : PrimeGeFive}

/-- Coefficient lemmas for the S1280 Gaussian curve y^2 + xy = x^3 + 5. -/
theorem S3119_curve_a1 : (S1348Curve l).a₁ = (1 : S1348K l) := by
  change (concreteSplitCurve.map (algebraMap ℚ (S1348K l))).a₁ = (1 : S1348K l)
  rw [WeierstrassCurve.map_a₁]
  simp [concreteSplitCurve]

theorem S3119_curve_a3 : (S1348Curve l).a₃ = (0 : S1348K l) := by
  change (concreteSplitCurve.map (algebraMap ℚ (S1348K l))).a₃ = (0 : S1348K l)
  rw [WeierstrassCurve.map_a₃]
  simp [concreteSplitCurve]

theorem S3119_curve_a2 : (S1348Curve l).a₂ = (0 : S1348K l) := by
  change (concreteSplitCurve.map (algebraMap ℚ (S1348K l))).a₂ = (0 : S1348K l)
  rw [WeierstrassCurve.map_a₂]
  simp [concreteSplitCurve]

theorem S3119_curve_a4 : (S1348Curve l).a₄ = (0 : S1348K l) := by
  change (concreteSplitCurve.map (algebraMap ℚ (S1348K l))).a₄ = (0 : S1348K l)
  rw [WeierstrassCurve.map_a₄]
  simp [concreteSplitCurve]

theorem S3119_curve_a6 : (S1348Curve l).a₆ = (5 : S1348K l) := by
  change (concreteSplitCurve.map (algebraMap ℚ (S1348K l))).a₆ = (5 : S1348K l)
  rw [WeierstrassCurve.map_a₆]
  simp [concreteSplitCurve]

/-- The coordinate-ring homomorphism (x,y) ↦ (x, -y - x). -/
noncomputable def S3119NegPolyHom :
    MvPolynomial (Fin 2) (S1348K l) →ₐ[S1348K l]
      MvPolynomial (Fin 2) (S1348K l) :=
  MvPolynomial.aeval (fun i : Fin 2 =>
    if i = 0 then MvPolynomial.X 0
    else -MvPolynomial.X 1 - MvPolynomial.X 0)

theorem S3119NegPolyHom_X0 :
    S3119NegPolyHom (l := l) (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [S3119NegPolyHom]

theorem S3119NegPolyHom_X1 :
    S3119NegPolyHom (l := l) (MvPolynomial.X 1) =
      -MvPolynomial.X 1 - MvPolynomial.X 0 := by
  simp [S3119NegPolyHom]

theorem S3119NegPolyHom_affinePolynomial :
    S3119NegPolyHom (l := l) (S1348AffinePolynomial l) = S1348AffinePolynomial l := by
  rw [S1348AffinePolynomial, weierstrassAffinePolynomial,
    S3119_curve_a1, S3119_curve_a2, S3119_curve_a3, S3119_curve_a4, S3119_curve_a6]
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero,
    MvPolynomial.C_0, MvPolynomial.C_1, MvPolynomial.algHom_C,
    MvPolynomial.algebraMap_eq,
    S3119NegPolyHom_X0, S3119NegPolyHom_X1]
  ring

#check S3119NegPolyHom
#check S3119NegPolyHom_X0
#check S3119NegPolyHom_X1

/-- The polynomial involution squares to the identity. -/
theorem S3119NegPolyHom_sq :
    S3119NegPolyHom (l := l).comp S3119NegPolyHom =
      AlgHom.id (S1348K l) (MvPolynomial (Fin 2) (S1348K l)) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change S3119NegPolyHom (l := l)
      (S3119NegPolyHom (l := l) (MvPolynomial.X (0 : Fin 2))) =
        MvPolynomial.X (0 : Fin 2)
    have h := congrArg (S3119NegPolyHom (l := l))
      (S3119NegPolyHom_X0 (l := l))
    rw [h, S3119NegPolyHom_X0 (l := l)]
  · change S3119NegPolyHom (l := l)
      (S3119NegPolyHom (l := l) (MvPolynomial.X (1 : Fin 2))) =
        MvPolynomial.X (1 : Fin 2)
    have h := congrArg (S3119NegPolyHom (l := l))
      (S3119NegPolyHom_X1 (l := l))
    rw [h, map_sub, map_neg, S3119NegPolyHom_X1 (l := l),
      S3119NegPolyHom_X0 (l := l)]
    ring

/-- The induced quotient endomorphism R -> R, R = K[x,y]/(f). -/
noncomputable def S3119NegQuotientHom :
    S1348CoordinateRing l →ₐ[S1348K l] S1348CoordinateRing l :=
  Ideal.Quotient.liftₐ (Ideal.span {S1348AffinePolynomial l})
    ((Ideal.Quotient.mkₐ (S1348K l)
      (Ideal.span {S1348AffinePolynomial l})).comp S3119NegPolyHom)
    (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      rcases ha with ⟨c, rfl⟩
      simp only [AlgHom.comp_apply]
      rw [map_mul, S3119NegPolyHom_affinePolynomial]
      change Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
        (S1348AffinePolynomial l * S3119NegPolyHom c) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right (S3119NegPolyHom c)
        (Ideal.span {S1348AffinePolynomial l})
        (Ideal.subset_span (Set.mem_singleton _)))

theorem S3119NegQuotientHom_mk (x : MvPolynomial (Fin 2) (S1348K l)) :
    S3119NegQuotientHom (l := l)
        (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) x) =
      Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
        (S3119NegPolyHom (l := l) x) :=
  rfl

/-- The quotient involution squares to one. -/
theorem S3119NegQuotientHom_sq :
    S3119NegQuotientHom (l := l).comp S3119NegQuotientHom =
      AlgHom.id (S1348K l) (S1348CoordinateRing l) := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro x
  change S3119NegQuotientHom (l := l)
      (S3119NegQuotientHom (l := l)
        (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) x)) =
    Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) x
  rw [S3119NegQuotientHom_mk (l := l), S3119NegQuotientHom_mk (l := l)]
  rw [show S3119NegPolyHom (l := l) (S3119NegPolyHom (l := l) x) = x from
    AlgHom.congr_fun (S3119NegPolyHom_sq (l := l)) x]

/-- The negative-point involution as an actual K-algebra automorphism of the
affine coordinate ring. -/
noncomputable def S3119NegInvolutionAlgEquiv :
    S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l :=
  AlgEquiv.ofAlgHom S3119NegQuotientHom S3119NegQuotientHom
    (S3119NegQuotientHom_sq (l := l))
    (S3119NegQuotientHom_sq (l := l))

#check S3119NegPolyHom_sq
#check S3119NegQuotientHom
#check S3119NegQuotientHom_sq
#check S3119NegInvolutionAlgEquiv
#print axioms S3119NegPolyHom_sq
#print axioms S3119NegQuotientHom_sq
#print axioms S3119NegInvolutionAlgEquiv

#check S3119NegPolyHom_affinePolynomial
#print axioms S3119NegPolyHom_affinePolynomial

end LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt
end
