import tmp.sheaf.xif.paper.S3119NegInvolutionOverActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionOverActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3128SignRankTwoActual
variable {l : PrimeGeFive}
abbrev R (l : PrimeGeFive) := S1348CoordinateRing l
noncomputable def S3128x (l : PrimeGeFive) : R l := Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 0)
noncomputable def S3128y (l : PrimeGeFive) : R l := Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 1)
/-- The anti-invariant element t = 2y + x. -/
noncomputable def S3128t (l : PrimeGeFive) : R l :=
  S3128y (l := l) + S3128y (l := l) + S3128x (l := l)
theorem S3128t_anti : S3119NegQuotientHom (l := l) (S3128t (l := l)) = -(S3128t (l := l)) := by
  simp only [S3128t, S3128x, S3128y, S3119NegQuotientHom_mk, S3119NegPolyHom_X0, S3119NegPolyHom_X1, map_add, map_sub, map_neg]
  ring
theorem S3128_xy_relation : (S3128y (l := l)) ^ 2 + S3128x (l := l) * S3128y (l := l) = (S3128x (l := l)) ^ 3 + 5 := by
  have hzero : Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (S1348AffinePolynomial l) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hzero' : Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
      ((MvPolynomial.X 1 : MvPolynomial (Fin 2) (S1348K l)) ^ 2 +
        (MvPolynomial.X 0 : MvPolynomial (Fin 2) (S1348K l)) *
          (MvPolynomial.X 1 : MvPolynomial (Fin 2) (S1348K l)) -
        ((MvPolynomial.X 0 : MvPolynomial (Fin 2) (S1348K l)) ^ 3 + MvPolynomial.C (5 : S1348K l))) = 0 := by
    convert hzero using 2
    simp [S1348AffinePolynomial, weierstrassAffinePolynomial, S3119_curve_a1,
      S3119_curve_a2, S3119_curve_a3, S3119_curve_a4, S3119_curve_a6]
  have hrel : Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
      ((MvPolynomial.X 1 : MvPolynomial (Fin 2) (S1348K l)) ^ 2 +
        (MvPolynomial.X 0 : MvPolynomial (Fin 2) (S1348K l)) *
          (MvPolynomial.X 1 : MvPolynomial (Fin 2) (S1348K l))) =
      Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
        ((MvPolynomial.X 0 : MvPolynomial (Fin 2) (S1348K l)) ^ 3 + MvPolynomial.C (5 : S1348K l)) := by
    have := hzero'
    rw [map_sub] at this
    exact sub_eq_zero.mp this
  simpa [S3128x, S3128y, map_ofNat] using hrel

theorem S3128t_sq : (S3128t (l := l)) ^ 2 = 4 * (S3128x (l := l)) ^ 3 + (S3128x (l := l)) ^ 2 + 20 := by
  calc (S3128t (l := l)) ^ 2 = 4 * ((S3128y (l := l)) ^ 2 + S3128x (l := l) * S3128y (l := l)) + (S3128x (l := l)) ^ 2 := by
        simp [S3128t]; ring
    _ = 4 * ((S3128x (l := l)) ^ 3 + 5) + (S3128x (l := l)) ^ 2 := by rw [S3128_xy_relation]
    _ = 4 * (S3128x (l := l)) ^ 3 + (S3128x (l := l)) ^ 2 + 20 := by ring
theorem S3128t_sq_fixed : S3119NegQuotientHom (l := l) ((S3128t (l := l)) ^ 2) = (S3128t (l := l)) ^ 2 := by
  rw [map_pow, S3128t_anti]; ring
#check S3128t_anti
#check S3128_xy_relation
#check S3128t_sq
#check S3128t_sq_fixed
end LeanFormal.IUT.XiFPaper.S3128SignRankTwoActual
end
