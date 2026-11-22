import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1898DegreeProbeAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36

example : MvPolynomial.degreeOf 1
    (MvPolynomial.C (-125/64 : S1726K) * MvPolynomial.X 0 :
      MvPolynomial (Fin 2) S1726K) = 0 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp [MvPolynomial.degreeOf_X_of_ne, h10]

example : MvPolynomial.degreeOf 1
    (MvPolynomial.C (61/64 : S1726K) * MvPolynomial.X 0 ^ 2 :
      MvPolynomial (Fin 2) S1726K) = 0 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp [MvPolynomial.degreeOf_X_of_ne, h10]

example : MvPolynomial.degreeOf 1
    (MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) S1726K) = 0 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp [MvPolynomial.degreeOf_X_pow_of_ne, h10]

theorem degreeOf_one_affinePolynomial :
    MvPolynomial.degreeOf 1 S1726AffinePolynomial = 2 := by
  rw [S1726AffinePolynomial, weierstrassAffinePolynomial,
    S1726Curve_a₁, S1726Curve_a₃]
  rw [sub_eq_add_neg]
  rw [MvPolynomial.degreeOf_add_eq_of_degreeOf_lt]
  · simp
  · have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp [MvPolynomial.degreeOf_X_of_ne, h10]

theorem y_not_mem_span :
    MvPolynomial.X 1 ∉
      Ideal.span ({S1726AffinePolynomial} :
        Set (MvPolynomial (Fin 2) S1726K)) := by
  intro hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨q, hq⟩ := hmem
  have hf_ne : S1726AffinePolynomial ≠ 0 := by
    intro h0
    have hdeg := degreeOf_one_affinePolynomial
    rw [h0, MvPolynomial.degreeOf_zero] at hdeg
    norm_num at hdeg
  have hq_ne : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hq
    have : (MvPolynomial.X 1 : MvPolynomial (Fin 2) S1726K) = 0 := hq
    simpa using congrArg (MvPolynomial.coeff (Finsupp.single 1 1)) this
  have hd := congrArg (MvPolynomial.degreeOf 1) hq
  rw [MvPolynomial.degreeOf_mul_eq hf_ne hq_ne,
    degreeOf_one_affinePolynomial, MvPolynomial.degreeOf_X_self] at hd
  omega

theorem y_ne_zero :
    Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
      (MvPolynomial.X 1) ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact y_not_mem_span

end LeanFormal.IUT.XiFPaper.S1898DegreeProbeAdapted

end