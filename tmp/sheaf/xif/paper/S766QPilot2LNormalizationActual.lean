import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S766QPilot2LNormalizationActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def paperQPilotScalar : Real :=
  -((((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real)) /
    (2 * (l.value : Real)))

noncomputable def paperQPilotMagnitude : Real :=
  (((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real)) /
    (2 * (l.value : Real))

theorem paperQPilotScalar_eq_neg_magnitude :
    paperQPilotScalar T b = -paperQPilotMagnitude T b := by
  unfold paperQPilotScalar paperQPilotMagnitude
  ring

noncomputable def classicalQPilotDegree : Real :=
  ((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real)

theorem classicalQPilotDegree_eq_twoL_mul_paper :
    classicalQPilotDegree T b =
      (2 * (l.value : Real)) * paperQPilotMagnitude T b := by
  unfold classicalQPilotDegree paperQPilotMagnitude
  have htwo : (2 * (l.value : Real)) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  have hl : (l.value : Real) ≠ 0 := by
    exact_mod_cast l.prime.ne_zero
  field_simp [htwo, hl]

theorem s695_s714_classical_eq_twoL_mul_paper :
    ((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real) =
      (2 * (l.value : Real)) * paperQPilotMagnitude T b :=
  classicalQPilotDegree_eq_twoL_mul_paper T b

end LeanFormal.IUT.XiFPaper.S766QPilot2LNormalizationActual
end