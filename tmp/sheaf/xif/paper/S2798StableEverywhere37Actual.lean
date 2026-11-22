import tmp.sheaf.xif.paper.S2797ClauseA37ConditionalActual
import tmp.sheaf.xif.paper.S2794Multiplicative37Actual
import tmp.sheaf.xif.paper.S2782Semistable37a1Actual
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import LeanFormal.IUT.Foundations.Geometry.LocalReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2794Multiplicative37Actual
open LeanFormal.IUT.XiFPaper.S2782Semistable37a1Actual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2782Curve37a1Actual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2798StableEverywhere37Actual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The rational 37a1 punctured curve. -/
def S2798E37Q : PuncturedEllipticCurve ℚ where
  curve := E37
  isElliptic := E37_isElliptic
  puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩

/-- Local model at a Gaussian place agrees with the base change of E37/Q(i). -/
theorem S2798_curve_baseChange_eq_localQi
    (P : NumberField.FinitePlace GaussianField) :
    E37QiPunctured.curve.baseChange
        ((NumberFieldFinitePlace.underlyingPrime P).adicCompletion GaussianField) =
      localCurve37Qi P := by
  ext <;> simp [E37QiPunctured, E37Qi, E37, localCurve37Qi,
    localIntegralModel37Qi, WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- Local model at a rational place agrees with the base change of E37/Q. -/
theorem S2798_curve_baseChange_eq_localQ
    (v : NumberField.FinitePlace ℚ) :
    S2798E37Q.curve.baseChange
        ((NumberFieldFinitePlace.underlyingPrime v).adicCompletion ℚ) =
      localCurve37 v := by
  ext <;> simp [S2798E37Q, E37, localCurve37, localIntegralModel37,
    WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- Good reduction at Gaussian places away from 37. -/
theorem S2798_goodOutside37 :
    ∀ P : NumberField.FinitePlace GaussianField,
      residueCharacteristic (comap (k := ℚ) P) ≠ 37 →
        E37QiPunctured.HasGoodReductionAt P := by
  intro P h37
  let v : NumberField.FinitePlace ℚ := comap (k := ℚ) P
  have hv : residueCharacteristic v ≠ 37 := h37
  have hX : S2798E37Q.HasGoodReductionAt v := by
    unfold PuncturedEllipticCurve.HasGoodReductionAt
    simp only [NumberFieldFinitePlace.underlyingPrime]
    refine ⟨1, ?_⟩
    simpa [S2798E37Q, E37, localCurve37, localIntegralModel37,
      WeierstrassCurve.baseChange, WeierstrassCurve.map]
      using localCurve37_hasGoodReduction v hv

  have hbase := PuncturedEllipticCurve.hasGoodReductionAt_baseChange S2798E37Q P hX
  unfold PuncturedEllipticCurve.HasGoodReductionAt at hbase ⊢
  simp only [NumberFieldFinitePlace.underlyingPrime] at hbase ⊢
  convert hbase using 2
  rfl

/-- Multiplicative reduction at Gaussian places above 37. -/
theorem S2798_multiplicative37 :
    ∀ P : NumberField.FinitePlace GaussianField,
      residueCharacteristic (comap (k := ℚ) P) = 37 →
        E37QiPunctured.HasMultiplicativeReductionAt P := by
  intro P h37
  have hP37 : residueCharacteristic P = 37 := by
    rw [← NumberFieldFinitePlace.residueCharacteristic_comap (k := ℚ) P]
    exact h37
  unfold PuncturedEllipticCurve.HasMultiplicativeReductionAt
  simp only [NumberFieldFinitePlace.underlyingPrime]
  refine ⟨1, ?_⟩
  simpa [E37QiPunctured, E37Qi, E37, localCurve37Qi, localIntegralModel37Qi,
    WeierstrassCurve.baseChange, WeierstrassCurve.map]
    using localCurve37Qi_hasMultiplicativeReduction P hP37

/-- Stable reduction everywhere for E37/Q(i). -/
theorem S2798_hasStableReductionEverywhere :
    E37QiPunctured.HasStableReductionEverywhere := by
  intro P
  by_cases h37 : residueCharacteristic (comap (k := ℚ) P) = 37
  · exact Or.inr (S2798_multiplicative37 P h37)
  · exact Or.inl (S2798_goodOutside37 P h37)

#check S2798_curve_baseChange_eq_localQi
#check S2798_goodOutside37
#check S2798_multiplicative37
#check S2798_hasStableReductionEverywhere
#print axioms S2798_hasStableReductionEverywhere

end LeanFormal.IUT.XiFPaper.S2798StableEverywhere37Actual
end
