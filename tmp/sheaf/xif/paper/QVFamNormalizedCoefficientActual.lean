import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual

/-! # qVFamily normalized coefficient and root comparison

The normalized qVFamily tensor coefficient is the actual qVFamily order
coefficient

  qVFamNormalizedCoefficient b = order(qVFamily T b)

(the qVFamTensorCoefficient of QVFamTensorCoefficientActual).  The root
coefficient is

  qVFamPaperRootCoefficient b = order(qVFamily T b) / (2l).

Since 2l >= 1 and the order is nonnegative:

  qVFamPaperRootCoefficient b <= qVFamNormalizedCoefficient b.

This is the exact coefficient inequality used by the classical-region-in-root-
hull inclusion.  No fake inequality; no equality of log-volumes is asserted.
No sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual normalized qVFamily tensor coefficient: the order. -/
noncomputable def qVFamNormalizedCoefficient : Real :=
  qVFamTensorCoefficient T b

/-- The normalized coefficient is exactly qVFamTensorCoefficient (order). -/
theorem qVFamNormalizedCoefficient_eq_tensor :
    qVFamNormalizedCoefficient T b = qVFamTensorCoefficient T b := rfl

/-- The normalized coefficient is the actual qVFamily order. -/
theorem qVFamNormalizedCoefficient_eq_order :
    qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real) := rfl

/-- The normalized coefficient is nonnegative. -/
theorem qVFamNormalizedCoefficient_nonneg :
    0 ≤ qVFamNormalizedCoefficient T b := by
  unfold qVFamNormalizedCoefficient
  exact qVFamTensorCoefficient_nonneg T b

/-- The actual coefficient inequality c_root <= c_norm. -/
theorem qVFamPaperRootCoefficient_le_normalized :
    qVFamPaperRootCoefficient T b ≤ qVFamNormalizedCoefficient T b := by
  unfold qVFamPaperRootCoefficient qVFamNormalizedCoefficient
    qVFamTensorCoefficient
  have horder : (0 : Real) ≤ ((qVFamily T b).order : Real) := by positivity
  have hl : (1 : Real) ≤ (2 * l.value : Real) := by
    have hpos : 0 < l.value := l.prime.pos
    exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos (by norm_num) hpos))
  calc
    ((qVFamily T b).order : Real) / (2 * l.value : Real)
        ≤ ((qVFamily T b).order : Real) / 1 :=
          div_le_div_of_nonneg_left horder zero_lt_one hl
    _ = ((qVFamily T b).order : Real) := div_one _

/-- Actual normalized/root coefficient data. -/
structure QVFamNormalizedCoefficientData where
  cNorm : Real
  cNorm_eq : cNorm = qVFamNormalizedCoefficient T b
  cRoot : Real
  cRoot_eq : cRoot = qVFamPaperRootCoefficient T b
  cRoot_le_cNorm : cRoot ≤ cNorm

/-- The actual normalized/root coefficient data constructor. -/
noncomputable def qVFamNormalizedCoefficientData :
    QVFamNormalizedCoefficientData T b where
  cNorm := qVFamNormalizedCoefficient T b
  cNorm_eq := rfl
  cRoot := qVFamPaperRootCoefficient T b
  cRoot_eq := rfl
  cRoot_le_cNorm := qVFamPaperRootCoefficient_le_normalized T b

end LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual

end
