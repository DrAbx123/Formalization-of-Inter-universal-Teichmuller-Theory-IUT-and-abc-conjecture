import tmp.sheaf.xif.paper.S914PaperLVExInstantiationActual
/-! # S1133: paper scalar LVEx gluing
Reuse S907 glue/rho and S914 paper R/S log volumes.  The paper scalar gluing
is pure arithmetic: if R <= S, rho > 1 and R >= 0, then
  glue(R) = R / rho <= R <= S.
The source comparison R <= S is NOT proved here; it is an exact input.
No duplicate object; new file is only the scalar gluing layer. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1133PaperLVExGluingActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S907LVExToyActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
/-- Paper R log-volume from the S914 qPilot region. -/
noncomputable def paperRLog : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (s914R (l := l) T b)
/-- Paper S log-volume from the S914 nonzero root theta hull. -/
noncomputable def paperSLog : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (s914S (l := l) T b)
/-- Paper gluing scale rho = R / lambda. -/
noncomputable def paperRho (lam : Real) : Real := paperRLog (l := l) T b mu / lam
/-- Paper LVEx glue: lambda = R / rho. -/
noncomputable def paperGlue (lam : Real) : Real :=
  paperRLog (l := l) T b mu / paperRho (l := l) T b mu lam
theorem paperGlue_eq_lam (lam : Real) (hR : paperRLog (l := l) T b mu ≠ 0)
    (hlam : lam ≠ 0) : paperGlue (l := l) T b mu lam = lam := by
  unfold paperGlue paperRho
  field_simp [hR, hlam]
theorem paperGlue_le_R (lam : Real) (hRnonneg : 0 ≤ paperRLog (l := l) T b mu)
    (hrho : 1 < paperRho (l := l) T b mu lam) :
    paperGlue (l := l) T b mu lam ≤ paperRLog (l := l) T b mu := by
  unfold paperGlue
  exact div_le_self hRnonneg (le_of_lt hrho)
/-- Scalar gluing conclusion: glue(R) <= S from R <= S and the paper rho > 1.
The R <= S comparison is the exact input; it is not proved here. -/
theorem paperGlue_le_S (lam : Real)
    (hRS : paperRLog (l := l) T b mu ≤ paperSLog (l := l) T b mu)
    (hRnonneg : 0 ≤ paperRLog (l := l) T b mu)
    (hrho : 1 < paperRho (l := l) T b mu lam) :
    paperGlue (l := l) T b mu lam ≤ paperSLog (l := l) T b mu :=
  (paperGlue_le_R (l := l) T b mu lam hRnonneg hrho).trans hRS
def S1133ExactInput (lam : Real) : Prop :=
  paperRLog (l := l) T b mu ≤ paperSLog (l := l) T b mu ∧
    0 ≤ paperRLog (l := l) T b mu ∧
    1 < paperRho (l := l) T b mu lam
end LeanFormal.IUT.XiFPaper.S1133PaperLVExGluingActual
