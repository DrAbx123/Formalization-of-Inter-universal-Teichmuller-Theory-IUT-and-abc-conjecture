import tmp.sheaf.xif.paper.BadPlacePaperConstantsActual
import tmp.sheaf.xif.paper.TwoLthRootKummerActual
import tmp.sheaf.xif.paper.S636ThetaNormalizationAuditActual

-- S638: use the existing actual paper theta normalization, not realThetaValue.
-- Paper theta value = hodgeTwoLthRoot^(j^2); classical q^(j^2) coefficient
-- is 2l times the paper root coefficient.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S638PaperThetaNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S636ThetaNormalizationAuditActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

theorem hodgeRoot_pow_twoL :
    hodgeTwoLthRoot (l := l) T b ^ (2 * l.value) = qVAlgClosedUnit T b :=
  hodgeTwoLthRoot_pow (l := l) T b

theorem paperThetaValueRoot_eq_actual_root_power (j : SignedLabel l.value) :
    qVFamPaperThetaValueRoot T b j =
      (hodgeTwoLthRoot (l := l) T b) ^ (gaussExponent j.1).toNat :=
  paperThetaValueRoot_is_root_power (l := l) T b j

theorem classicalThetaCoefficient_is_twoL_times_paper
    (j : SignedLabel l.value) :
    qVFamThetaTensorCoefficient T b j () =
      (2 * l.value : Real) * paperThetaCoefficient T b j :=
  classicalThetaCoefficient_eq_twoL_mul_paper (l := l) T b j

/-- Exact conclusion: paper theta values are root powers; the classical
q^(j^2) coefficient is 2l times the paper root coefficient. -/
def PaperThetaNormalizationConclusion : Prop :=
  (∀ j : SignedLabel l.value,
      qVFamPaperThetaValueRoot T b j =
        (hodgeTwoLthRoot (l := l) T b) ^ (gaussExponent j.1).toNat) ∧
    (∀ j : SignedLabel l.value,
      qVFamThetaTensorCoefficient T b j () =
        (2 * l.value : Real) * paperThetaCoefficient T b j)

theorem paperThetaNormalizationConclusion_proved :
    PaperThetaNormalizationConclusion (l := l) T b :=
  ⟨paperThetaValueRoot_eq_actual_root_power (l := l) T b,
   classicalThetaCoefficient_is_twoL_times_paper (l := l) T b⟩

-- The root lives in the algebraic closure, not the completion (S342).

#check paperThetaValueRoot_eq_actual_root_power
#check classicalThetaCoefficient_is_twoL_times_paper
#check paperThetaNormalizationConclusion_proved

end LeanFormal.IUT.XiFPaper.S638PaperThetaNormalizationActual

end