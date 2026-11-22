import tmp.sheaf.xif.paper.S885RootStackUniformizerNormActual
import tmp.sheaf.xif.paper.S824RootStackyHaarVolumeActual

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1124EUnitFactorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S878RootStackCharacterNormDirectActual
open LeanFormal.IUT.XiFPaper.S885RootStackUniformizerNormActual
open LeanFormal.IUT.XiFPaper.S824RootStackyHaarVolumeActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Actual E unit-factor: a norm-one unit of the finite root stack has Haar
factor one.  This is the E-side analogue of the L-side actual theorem, proved
via invariance of the compact unit ball. -/
theorem s1124UnitFactorOne_actual :
    S885UnitFactorOne (l := l) T b := by
  intro u hu
  unfold rootStackHaarFactor
  haveI hhaar : (rootStackHaar (l := l) T b).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_addHaarMeasure (K₀ := Classical.arbitrary _)
  have hball : u • stackUnitBall (l := l) T b = stackUnitBall (l := l) T b := by
    rw [closedBall_smul_unit_eq (l := l) T b u, hu]
    rfl
  have hpos : rootStackHaar (l := l) T b (stackUnitBall (l := l) T b) ≠ 0 :=
    (unitBall_pos (l := l) T b (rootStackHaar (l := l) T b)).ne'
  have hfin : rootStackHaar (l := l) T b (stackUnitBall (l := l) T b) ≠ ⊤ :=
    (unitBall_fin (l := l) T b (rootStackHaar (l := l) T b)).ne
  have hchar : MeasureTheory.distribHaarChar (rootStackExtension T b) u = 1 := by
    apply MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul
      (μ := rootStackHaar (l := l) T b) (g := u)
      (s := stackUnitBall (l := l) T b) (r := 1) hpos hfin
    rw [hball]
    simp
  rw [hchar]
  simp

/-- Exact E unit-factor is now actual; the remaining exact input is the
uniformizer norm, DVR decomposition, uniformizer factor, and factor-norm power. -/
def S1124UniformizerExactRemainder (pi : (rootStackExtension T b)ˣ) : Prop :=
  ‖(pi : rootStackExtension T b)‖ < 1 ∧
    S885UnitDecomposition (l := l) T b pi ∧
      S885UniformizerFactor (l := l) T b pi ∧
        RootStackHaarFactorNormPow (l := l) T b (dQpFactor (l := l) T b)

/-- S885 exact data from the exact remainder and the actual unit-factor theorem. -/
noncomputable def s1124UniformizerData_of_remainder
    (pi : (rootStackExtension T b)ˣ)
    (h : S1124UniformizerExactRemainder (l := l) T b pi) :
    S885UniformizerData (l := l) T b where
  pi := pi
  pi_norm_lt_one := h.1
  unit_factor_one := s1124UnitFactorOne_actual (l := l) T b
  decomposition := h.2.1
  uniformizer_factor := h.2.2.1
  factor_norm_pow := h.2.2.2

end LeanFormal.IUT.XiFPaper.S1124EUnitFactorActual

end
