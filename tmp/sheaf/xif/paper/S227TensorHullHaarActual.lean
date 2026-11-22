import tmp.sheaf.xif.paper.S214RootThetaNormTensorActual
import tmp.sheaf.xif.paper.PaperRootTensorHaarActual

/-! # S227: tensor/L hull Haar transport -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S227TensorHullHaarActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.S214RootThetaNormTensorActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable instance tensorBlockMeasurableSpace :
    MeasurableSpace (rootTensorBlock T b) :=
  MeasurableSpace.map (tensorBlockLinearEquiv T b).symm
    (borel (rootNormedExtension T b))

noncomputable def tensorHaarTransport : Measure (rootTensorBlock T b) :=
  (rootNormedHaar T b).map (tensorBlockLinearEquiv T b).symm

noncomputable def tensorLambdaOHull : Set (rootTensorBlock T b) :=
  tensorThetaHullPreimage T b

noncomputable def LFieldUnitHull : Set (rootNormedExtension T b) :=
  LThetaClosureHull T b

theorem tensorBlockLinearEquiv_image_tensorLambdaOHull :
    tensorBlockLinearEquiv T b '' tensorLambdaOHull T b = LFieldUnitHull T b := by
  unfold tensorLambdaOHull LFieldUnitHull tensorThetaHullPreimage
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨(tensorBlockLinearEquiv T b).symm y, ?_, ?_⟩
    · change tensorBlockLinearEquiv T b
        ((tensorBlockLinearEquiv T b).symm y) ∈ LThetaClosureHull T b
      rw [LinearEquiv.apply_symm_apply]
      exact hy
    · exact (tensorBlockLinearEquiv T b).apply_symm_apply y

structure TensorHullHaarLogData where
  tensorHaar : Measure (rootTensorBlock T b)
  tensorHaar_eq : tensorHaar = tensorHaarTransport T b
  tensorHull : Set (rootTensorBlock T b)
  tensorHull_eq : tensorHull = tensorLambdaOHull T b
  LHaar : Measure (rootNormedExtension T b)
  LHaar_eq : LHaar = rootNormedHaar T b
  LHull : Set (rootNormedExtension T b)
  LHull_eq : LHull = LFieldUnitHull T b
  tensorHullLog : Real
  LHullLog : Real
  hull_log_relation : Prop

noncomputable def tensorHullHaarLogData :
    TensorHullHaarLogData (l := l) T b where
  tensorHaar := tensorHaarTransport T b
  tensorHaar_eq := rfl
  tensorHull := tensorLambdaOHull T b
  tensorHull_eq := rfl
  LHaar := rootNormedHaar T b
  LHaar_eq := rfl
  LHull := LFieldUnitHull T b
  LHull_eq := rfl
  tensorHullLog := Real.log (tensorHaarTransport T b (tensorLambdaOHull T b)).toReal
  LHullLog := Real.log (rootNormedHaar T b (LFieldUnitHull T b)).toReal
  hull_log_relation := tensorHaarTransport T b (tensorLambdaOHull T b) = rootNormedHaar T b (LFieldUnitHull T b)

/-- Pushforward measure on a CLE-preimage equals the L measure. -/
theorem tensorHaarTransport_preimage (S : Set (rootNormedExtension T b))
    (hS : MeasurableSet S) :
    tensorHaarTransport T b (tensorBlockLinearEquiv T b ⁻¹' S) =
      rootNormedHaar T b S := by
  unfold tensorHaarTransport
  rw [Measure.map_apply]
  · congr 1
    ext y
    simp [LinearEquiv.apply_symm_apply]
  · exact Measurable.of_le_map le_rfl
  · rw [MeasurableSpace.map_def]
    have hpre : ((tensorBlockLinearEquiv T b).symm ⁻¹'
        ((tensorBlockLinearEquiv T b) ⁻¹' S)) = S := by
      ext y
      simp [LinearEquiv.apply_symm_apply]
    rw [hpre]
    exact hS

/-- The L field-unit hull is measurable (finite theta image). -/
theorem LFieldUnitHull_measurable :
    MeasurableSet (LFieldUnitHull T b) := by
  have hfin : (Set.range (rootNormedThetaValueInL T b)).Finite :=
    Set.finite_range _
  have hclosed : IsClosed (Set.range (rootNormedThetaValueInL T b)) :=
    hfin.isClosed
  unfold LFieldUnitHull LThetaClosureHull
  rw [hclosed.closure_eq]
  exact hfin.measurableSet

/-- Exact measure relation: the transported tensor hull Haar equals the L hull
Haar. -/
theorem tensorHaarTransport_tensorLambdaOHull_eq :
    tensorHaarTransport T b (tensorLambdaOHull T b) =
      rootNormedHaar T b (LFieldUnitHull T b) := by
  unfold tensorLambdaOHull LFieldUnitHull tensorThetaHullPreimage
  exact tensorHaarTransport_preimage T b (LThetaClosureHull T b)
    (LFieldUnitHull_measurable T b)

end LeanFormal.IUT.XiFPaper.S227TensorHullHaarActual

end
