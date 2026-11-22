import tmp.sheaf.xif.paper.S2765CurveOutsideTwoActual
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2765CurveOutsideTwoActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

local instance s2767GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := by
  apply Fact.mk
  apply X_pow_sub_C_irreducible_of_prime (p := 2) Nat.prime_two
  intro b hb
  have hnonneg : 0 <= b ^ 2 := sq_nonneg b
  rw [hb] at hnonneg
  exact (not_le_of_gt (neg_lt_zero.mpr zero_lt_one)) hnonneg

namespace LeanFormal.IUT.XiFPaper.S2767GaussianOutsideTwoActualAdapted

/-- The rational punctured curve y^2 = x^3 - x. -/
def XQ : PuncturedEllipticCurve ℚ where
  curve := curveY2EqX3SubX
  isElliptic := curveY2EqX3SubX_isElliptic
  puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩

theorem XQ_curve : XQ.curve = curveY2EqX3SubX := rfl

/-- The local curve used in S2765 is the completion of XQ. -/
theorem XQ_localCurve_eq (v : NumberField.FinitePlace ℚ) :
    (XQ.curve.baseChange (v.maximalIdeal.adicCompletion ℚ)) =
      localCurve v := by
  ext <;>
    simp [XQ, localCurve, localIntegralModel, curveY2EqX3SubX,
      WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- Good reduction at a rational place outside 2. -/
theorem XQ_hasGoodReductionAt (v : NumberField.FinitePlace ℚ)
    (h2 : residueCharacteristic v ≠ 2) :
    XQ.HasGoodReductionAt v := by
  rw [PuncturedEllipticCurve.HasGoodReductionAt]
  convert localCurve_hasGoodReductionOnMinimalModel v h2 using 2
  · rfl
  · exact XQ_localCurve_eq v

/-- The Gaussian base-changed curve has good reduction at every Gaussian place
whose contracted rational place is outside 2. -/
theorem gaussianOutsideTwo_hasGoodReductionAt
    (P : NumberField.FinitePlace GaussianField)
    (h2 : residueCharacteristic (comap (k := ℚ) P) ≠ 2) :
    (XQ.baseChange GaussianField).HasGoodReductionAt P :=
  PuncturedEllipticCurve.hasGoodReductionAt_baseChange XQ P
    (XQ_hasGoodReductionAt (comap (k := ℚ) P) h2)

#check XQ
#check XQ_localCurve_eq
#check XQ_hasGoodReductionAt
#check gaussianOutsideTwo_hasGoodReductionAt
#print axioms gaussianOutsideTwo_hasGoodReductionAt

end LeanFormal.IUT.XiFPaper.S2767GaussianOutsideTwoActualAdapted
end
