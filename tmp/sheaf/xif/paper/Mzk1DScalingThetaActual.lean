import LeanFormal.IUT.IUTIII.Theorem311.SourceLabelWeightedDiagonal
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1DScalingThetaActual — D-scaling Theta^{j^2} object from the finite theta packet

Reuse of `SourceLabelWeightedDiagonal` (label weights j^2, thetaScale power law)
and the finite theta packet: a real D-scaling object whose values are the
Gaussian theta values `q^{j^2}`.  No Prop placeholder; the object stores the
actual theta values and weights. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DScalingThetaActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLabelWeightedDiagonal

universe u

/-- D-scaling data: Gaussian theta values and their j^2 weights. -/
structure DScalingTheta (l : PrimeGeFive) where
  value : SignedLabel l.value → ℝ
  value_eq : ∀ j, value j = gaussianFiveThetaQ ^ labelWeight j
  weight : SignedLabel l.value → ℕ
  weight_eq : ∀ j, weight j = labelWeight j

/-- The canonical D-scaling object from the finite theta packet. -/
def dScalingTheta (l : PrimeGeFive) : DScalingTheta l where
  value := fun j => gaussianFiveThetaQ ^ labelWeight j
  value_eq := fun _ => rfl
  weight := fun j => labelWeight j
  weight_eq := fun _ => rfl

theorem dScalingTheta_value_eq_thetaScale (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    (dScalingTheta l).value j = ConcreteSourceEtaleThetaBridge.thetaScale l j := by
  rw [dScalingTheta]
  exact (thetaScale_eq_gaussianFiveThetaQ_pow l j).symm

theorem dScalingTheta_value_mul (l : PrimeGeFive)
    (j k : SignedLabel l.value) :
    (dScalingTheta l).value j * (dScalingTheta l).value k =
      gaussianFiveThetaQ ^ (labelWeight j + labelWeight k) := by
  rw [dScalingTheta]
  exact (pow_add gaussianFiveThetaQ (labelWeight j) (labelWeight k)).symm

theorem dScalingTheta_weight_zero (l : PrimeGeFive) :
    (dScalingTheta l).weight (zeroLabel (l := l.value)) = 0 := by
  rw [dScalingTheta]
  show labelWeight (zeroLabel (l := l.value)) = 0
  exact labelWeight_zeroLabel

end LeanFormal.IUT.XiFPaper.Mzk1DScalingThetaActual

end
