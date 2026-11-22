import tmp.sheaf.xif.paper.S820FiniteLScalingGeneratorActual
import tmp.sheaf.xif.paper.S817StackRootUnitNormActual
import tmp.sheaf.xif.paper.QVFamNormalizedRootRelationActual

-- S825: StackRootUnitFactorOne iff c_norm = order; paper normalization
-- absorption audit for the exact e_v factor.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S825StackFactorCNormEquivActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedRootRelationActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S820FiniteLScalingGeneratorActual
open LeanFormal.IUT.XiFPaper.S817StackRootUnitNormActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem stackRootUnitFactor_eq_one_iff_norm_eq_paperNorm (i : qVFamTensorV) :
    stackRootUnitFactor (l := l) T b i = 1 ↔
      ‖((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
          rootStackExtension T b)‖ = stackRootUnitPaperNorm (l := l) T b := by
  have hcoef : paperRootCoefficientFamily T b i = ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := by
    unfold paperRootCoefficientFamily
    exact qVFamPaperRootCoefficient_eq_order_div (l := l) T b
  unfold stackRootUnitFactor stackRootUnitPaperNorm
  rw [hcoef]
  simp only [neg_div]
  rw [div_eq_one_iff_eq]
  · rfl
  · exact ne_of_gt (Real.rpow_pos_of_pos
      (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos) _)

theorem stackRootUnitFactorOne_iff_norm_eq_paperNorm :
    StackRootUnitFactorOne (l := l) T b ↔
      ‖((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
          rootStackExtension T b)‖ = stackRootUnitPaperNorm (l := l) T b := by
  constructor
  · intro h
    exact (stackRootUnitFactor_eq_one_iff_norm_eq_paperNorm (l := l) T b ()).mp
      (h ())
  · intro h i
    exact (stackRootUnitFactor_eq_one_iff_norm_eq_paperNorm (l := l) T b i).mpr h

/-- Main iff: all exact e_v factors are one iff c_norm = order. -/
theorem StackRootUnitFactorOne_iff_cNorm_eq_order :
    StackRootUnitFactorOne (l := l) T b ↔
      qVFamNormalizedCoefficient (l := l) T b = ((qVFamily T b).order : Real) := by
  rw [stackRootUnitFactorOne_iff_norm_eq_paperNorm (l := l) T b]
  exact stackRootUnit_norm_eq_paperNorm_iff (l := l) T b

/-- Exact normalization absorption would force c_norm = order. -/
def PaperNormalizationAbsorbsStackFactor : Prop :=
  stackRootNormExponentDifference (l := l) T b = 0

theorem paperNormalizationAbsorbs_iff_cNorm_eq_order :
    PaperNormalizationAbsorbsStackFactor T b ↔
      qVFamNormalizedCoefficient (l := l) T b = ((qVFamily T b).order : Real) := by
  unfold PaperNormalizationAbsorbsStackFactor stackRootNormExponentDifference
  constructor
  · intro h
    have hden : (2 * (l.value : Real)) ≠ 0 := by
      exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
    have hl : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
    field_simp [hden, hl] at h
    linarith
  · intro h
    rw [h]; ring

/-- Any common nonzero paper weight cancels from the e_v ratio, so it cannot
absorb the factor. -/
theorem common_weight_cancels_stack_eFactor (w : Real) (hw : w ≠ 0) :
    (w * ‖((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
        rootStackExtension T b)‖) /
      (w * stackRootUnitPaperNorm (l := l) T b) =
    ‖((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
        rootStackExtension T b)‖ / stackRootUnitPaperNorm (l := l) T b := by
  field_simp [hw]

#check StackRootUnitFactorOne_iff_cNorm_eq_order
#check paperNormalizationAbsorbs_iff_cNorm_eq_order
#check common_weight_cancels_stack_eFactor

end LeanFormal.IUT.XiFPaper.S825StackFactorCNormEquivActual

end