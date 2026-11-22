import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionCarrierReduction
import Mathlib.Tactic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2760ElevenA1SerreTargetActual

/-- 11a1: y^2 + y = x^3 - x^2 - 10x - 20, in Weierstrass form
(a1,a2,a3,a4,a6) = (0,-1,1,-10,-20). -/
def E11a1Curve : WeierstrassCurve ℚ :=
  WeierstrassCurve.mk 0 (-1) 1 (-10) (-20)

@[simp] theorem E11a1Curve_a1 : E11a1Curve.a₁ = 0 := rfl
@[simp] theorem E11a1Curve_a2 : E11a1Curve.a₂ = (-1 : ℚ) := rfl
@[simp] theorem E11a1Curve_a3 : E11a1Curve.a₃ = (1 : ℚ) := rfl
@[simp] theorem E11a1Curve_a4 : E11a1Curve.a₄ = (-10 : ℚ) := rfl
@[simp] theorem E11a1Curve_a6 : E11a1Curve.a₆ = (-20 : ℚ) := rfl

/-- Discriminant of 11a1: -11^5 = -161051. -/
theorem E11a1Curve_discriminant : E11a1Curve.Δ = (-161051 : ℚ) := by
  norm_num [E11a1Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem E11a1Curve_discriminant_ne_zero : E11a1Curve.Δ ≠ 0 := by
  rw [E11a1Curve_discriminant]
  norm_num

/-- 11a1 is elliptic (Δ is a unit over QQ). -/
instance E11a1Curve_isElliptic : E11a1Curve.IsElliptic :=
  ⟨by rw [isUnit_iff_ne_zero]; exact E11a1Curve_discriminant_ne_zero⟩

/-- The punctured elliptic curve 11a1 over QQ. -/
def E11a1 : PuncturedEllipticCurve ℚ where
  curve := E11a1Curve
  isElliptic := E11a1Curve_isElliptic
  puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩

/-- j-invariant of 11a1: -2^12 * 31^3 / 11^5 = -122023936/161051. -/
theorem E11a1_jInvariant :
    E11a1.jInvariant = (-122023936 / 161051 : ℚ) := by
  rw [PuncturedEllipticCurve.jInvariant_spec]
  change E11a1Curve.j = (-122023936 / 161051 : ℚ)
  rw [WeierstrassCurve.j]
  have hunit : E11a1Curve.Δ' = Units.mk0 E11a1Curve.Δ E11a1Curve_discriminant_ne_zero :=
    Units.ext rfl
  have hc4 : E11a1Curve.c₄ = (496 : ℚ) := by
    norm_num [E11a1Curve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄]
  rw [hunit, Units.val_inv_eq_inv_val, Units.val_mk0, E11a1Curve_discriminant, hc4]
  norm_num

def S2760FiveLabel : PrimeGeFive where
  value := 5
  prime := by norm_num
  ge_five := by norm_num

/-- The target Serre-style large-image statement for 11a1 at l=5. -/
def S2760SerreLargeImageTarget : Prop :=
  SerreStyleLargeImageStatement E11a1 S2760FiveLabel

#check E11a1Curve
#check E11a1Curve_discriminant
#check E11a1_jInvariant
#check S2760SerreLargeImageTarget

end LeanFormal.IUT.XiFPaper.S2760ElevenA1SerreTargetActual
end