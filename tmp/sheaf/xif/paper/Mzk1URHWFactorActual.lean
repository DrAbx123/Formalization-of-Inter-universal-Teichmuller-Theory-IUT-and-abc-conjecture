import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.Mzk1ULR1CPrimeFiberActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import Mathlib.Tactic

/-!
# The hW weight identity: exact algebraic factor (no K/F degree assumption)

hW : nativeBadLocalWeight_b * qVFamNormalizedCoefficient_b = (1/(2l)) * cPFullFiber_b

Pure algebra: hW holds iff cpFullFiber_b = 2l * (weight_b * qVFamNormalizedCoefficient_b).
No degree, no [K:F] = 2l, no new hypothesis is used.
-/

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1URHWFactorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR1CPrimeFiberActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- `qVFamNormalizedCoefficient` is `qVFamTensorCoefficient` (definitional). -/
theorem normalized_eq_tensor (b : Bad (nativePlaceSelection T)) :
    qVFamNormalizedCoefficient (l := l) T b = qVFamTensorCoefficient (l := l) T b := rfl

/-- **hW, exact factor form**: equivalent to `cPFullFiber = 2l * (weight * cNorm)`. -/
theorem hW_iff_cPFullFiber_eq (h2l : (2 * (l.value : Nat) : Real) ≠ 0)
    (b : Bad (nativePlaceSelection T)) :
    (nativeBadLocalWeight (l := l) T b * qVFamNormalizedCoefficient (l := l) T b =
        (1 / (2 * (l.value : Real))) * cPFullFiber (l := l) T b) ↔
      cPFullFiber (l := l) T b =
        (2 * (l.value : Real)) *
          (nativeBadLocalWeight (l := l) T b * qVFamNormalizedCoefficient (l := l) T b) := by
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    rw [h]
    field_simp

#print axioms normalized_eq_tensor
#print axioms hW_iff_cPFullFiber_eq
end LeanFormal.IUT.XiFPaper.Mzk1URHWFactorActual