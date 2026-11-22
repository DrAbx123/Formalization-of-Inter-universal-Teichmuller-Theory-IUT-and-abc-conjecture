import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# qVFamTensorBlock local norm/coefficient alignment

The one-factor qVFam tensor block at b has actual coefficient
qVFamTensorCoefficient T b = (qVFamily T b).order and actual F-place
qVFamTensorPlace T b.

This file records the actual equalities available from the production q-side API:

* the qVFam coefficient times the actual F-place residue-norm logarithm equals
  the qVFamily order times that same norm logarithm;
* the same coefficient expression is the negative of the actual local signed
  q log at b.

The rational-prime form

  (order * [F_w:Q_p]) * log p_b = order * localDegree * log(residueNormBase b.1)

requires the actual identity between the rational prime p_b and the rational
residue norm of the F-place. That identity is not proved by the production API
used here; it is recorded as the exact proposition
qVFamTensorRationalPrimeLogObstruction. No inequality is asserted.

No True/PUnit, empty type, axiom, or sorry is used.
-/

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.QVFamTensorBlockAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual local residue degree [F_w : (F_mod)_v]. -/
noncomputable def qVFamTensorLocalDegree : Nat :=
  localResidueDegree (k := T.arithmetic.Fmod) (qVFamTensorPlace T b)

/-- The actual rational completion degree [F_w : Q_p]. -/
noncomputable def qVFamTensorRationalDegree : Nat :=
  localResidueDegree (k := ℚ) (qVFamTensorPlace T b)

/-- The actual coefficient/norm equality at the actual F-place. -/
theorem qVFamTensorBlock_norm_alignment :
    qVFamTensorCoefficient T b *
        Real.log (residueNormBase (qVFamTensorPlace T b)) =
      ((qVFamily T b).order : Real) *
        Real.log (residueNormBase (qVFamTensorPlace T b)) := by
  unfold qVFamTensorCoefficient
  ring

/-- The actual local signed q log is the negative of the same coefficient
expression at the actual F-place residue norm. -/
theorem qVFamTensorBlock_localSignedLog_alignment :
    localSignedLog (qVFamily T b) =
      - (qVFamTensorCoefficient T b *
          Real.log (residueNormBase (qVFamTensorPlace T b))) := by
  rw [localSignedLog_eq_neg_magnitude]
  rw [localLogMagnitude_eq_order_mul_log]
  unfold qVFamTensorCoefficient
  ring

/-- Exact proposition obstacle for the rational-prime form: the rational
degree times log p_b must equal the F-place residue-norm logarithm. This is the
precise missing rational-norm identification; it is not asserted. -/
def qVFamTensorRationalPrimeLogObstruction : Prop :=
  (qVFamTensorRationalDegree T b : Real) * Real.log (qVFamTensorP T b) =
    Real.log (residueNormBase (qVFamTensorPlace T b))

end LeanFormal.IUT.XiFPaper.QVFamTensorBlockAlignmentActual

end
