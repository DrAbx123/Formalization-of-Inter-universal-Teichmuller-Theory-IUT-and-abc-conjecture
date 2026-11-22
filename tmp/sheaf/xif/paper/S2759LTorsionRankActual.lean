import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import LeanFormal.IUT.IUTII.Frobenioid.Example36OddDivisionPolynomialBounds
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2759LTorsionRankActual

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.DivisionTorsionThree
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OddDivisionPolynomialBounds

/-- The concrete label 5. -/
def S2759FiveLabel : PrimeGeFive where
  value := 5
  prime := Nat.prime_five
  ge_five := by norm_num

/-- The concrete curve y² = x³ - x over ℚ, once-punctured at infinity. -/
def S2759Curve : PuncturedEllipticCurve ℚ where
  curve := y2x3xCurve (K := ℚ)
  isElliptic := by
    rw [WeierstrassCurve.isElliptic_iff]
    rw [show (y2x3xCurve (K := ℚ)).Δ = 64 by
      simp [y2x3xCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      norm_num]
    norm_num
  puncture := 0

/-- Exact degree of the 5-division polynomial: (5² - 1)/2 = 12. -/
theorem S2759_prePsi5_natDegree :
    (S2759Curve.curve.preΨ (5 : ℤ)).natDegree = 12 := by
  simpa using y2x3xCurve_preΨ_natDegree_odd (K := ℚ) (n := 5)
    (by norm_num) (by norm_num)

/-- The 5-division polynomial is nonzero over ℚ. -/
theorem S2759_prePsi5_ne_zero :
    S2759Curve.curve.preΨ (5 : ℤ) ≠ 0 := by
  change (y2x3xCurve (K := ℚ)).preΨ (5 : ℤ) ≠ 0
  exact y2x3xCurve_preΨ_ne_zero_odd (K := ℚ) (n := 5) (by norm_num) (by norm_num)

/-- Target: the 5-torsion subgroup is a 2-dimensional ZMod-5 space. -/
def S2759FiveTorsionRankTarget : Prop :=
  letI := PuncturedEllipticCurve.lTorsionModule (X := S2759Curve) S2759FiveLabel
  Module.finrank (ZMod S2759FiveLabel.value)
    (S2759Curve.LTorsion S2759FiveLabel) = 2

/-- Equivalent cardinality target: the 5-torsion subgroup has 25 elements. -/
def S2759FiveTorsionCardTarget : Prop :=
  Nat.card (S2759Curve.LTorsion S2759FiveLabel) = 25

#check S2759Curve
#check S2759FiveLabel
#check S2759_prePsi5_natDegree
#check S2759_prePsi5_ne_zero
#check S2759FiveTorsionRankTarget
#check S2759FiveTorsionCardTarget
#print axioms S2759_prePsi5_natDegree
#print axioms S2759_prePsi5_ne_zero

end LeanFormal.IUT.XiFPaper.S2759LTorsionRankActual
end
