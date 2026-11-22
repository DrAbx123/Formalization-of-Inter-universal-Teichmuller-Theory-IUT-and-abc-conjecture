import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullScalingActual

/-! # Actual field-unit scaling for the root image hull -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullScalingActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Nonempty positive ThetaLabel type. -/
instance rootThetaLabelNonempty : Nonempty (ThetaLabel (l := l)) :=
  ⟨⟨oneLabel l, by rw [oneLabel_val]; norm_num⟩⟩

/-- Actual finite maximum index for the root theta norm, using Fintype choice. -/
noncomputable def rootThetaMaxIndex (b : Bad (nativePlaceSelection T)) :
    ThetaLabel (l := l) :=
  Classical.choose (Finset.exists_max_image (Finset.univ : Finset (ThetaLabel (l := l)))
    (fun j => ‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
      rootNormedExtension T b)‖) Finset.univ_nonempty)

/-- The chosen maximum index really maximizes the root theta norm. -/
theorem rootThetaMaxIndex_spec (b : Bad (nativePlaceSelection T))
    (j : ThetaLabel (l := l)) :
    ‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
      rootNormedExtension T b)‖ ≤
      ‖(rootNormedThetaValueInL T b
        (thetaLabelToSigned (l := l) (rootThetaMaxIndex T b)) :
        rootNormedExtension T b)‖ :=
  (Classical.choose_spec (Finset.exists_max_image
    (Finset.univ : Finset (ThetaLabel (l := l)))
    (fun j => ‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
      rootNormedExtension T b)‖) Finset.univ_nonempty)).2 j (Finset.mem_univ j)

/-- Actual field-unit lambda at coordinate b: the maximizing root theta value. -/
noncomputable def rootThetaFieldLambda (b : Bad (nativePlaceSelection T)) :
    rootNormedExtension T b :=
  rootNormedThetaValueInL T b
    (thetaLabelToSigned (l := l) (rootThetaMaxIndex T b))

/-- Scaled lambda-O hull at coordinate b: actual field multiplication of the
closed unit ball by the maximizing root theta value. -/
def rootThetaFieldLambdaO (b : Bad (nativePlaceSelection T)) :
    Set (rootNormedExtension T b) :=
  (rootThetaFieldLambda T b) • rootExtensionUnitBall T b

/-- Field-scaled product hull. -/
def rootExtensionProductFieldScaledHull :
    Set (RootExtensionProductCarrier T) :=
  Set.pi Set.univ (fun b => rootThetaFieldLambdaO T b)

/-- The field scaling has norm equal to the image radius. -/
theorem rootImageRadius_eq_norm_fieldLambda (b : Bad (nativePlaceSelection T)) :
    (rootImageRadius T b : Real) = ‖(rootThetaFieldLambda T b :
      rootNormedExtension T b)‖ := by
  apply le_antisymm
  · have hsup : rootImageRadius T b ≤
        (⟨‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖,
          norm_nonneg _⟩ : NNReal) := by
      unfold rootImageRadius
      exact Finset.sup_le (fun j _ => rootThetaMaxIndex_spec (T := T) (b := b) j)
    exact_mod_cast hsup
  · exact rootImageRadius_ge (T := T) b (rootThetaMaxIndex T b)

/-- The field-scaled lambda-O hull is exactly the coordinatewise closed ball
of radius ||lambda||. -/
theorem rootThetaFieldLambdaO_eq_closedBall (b : Bad (nativePlaceSelection T)) :
    rootThetaFieldLambdaO T b =
      Metric.closedBall (0 : rootNormedExtension T b)
        ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
  unfold rootThetaFieldLambdaO
  unfold rootExtensionUnitBall
  rw [smul_unitClosedBall]

/-- The field-scaled product hull equals the metric image hull. -/
theorem rootExtensionProductFieldScaledHull_eq_imageHull :
    rootExtensionProductFieldScaledHull T = rootExtensionProductImageHull T := by
  ext x
  constructor
  · intro hx b hb
    have h := hx b hb
    change (x b : rootNormedExtension T b) ∈ rootThetaFieldLambdaO T b at h
    rw [rootThetaFieldLambdaO_eq_closedBall] at h
    change (x b : rootNormedExtension T b) ∈
      Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real)
    rw [rootImageRadius_eq_norm_fieldLambda]
    exact h
  · intro hx b hb
    have h := hx b hb
    have h' : (x b : rootNormedExtension T b) ∈
        Metric.closedBall (0 : rootNormedExtension T b)
          ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
      rw [← rootImageRadius_eq_norm_fieldLambda]
      exact h
    change (x b : rootNormedExtension T b) ∈ rootThetaFieldLambdaO T b
    rw [rootThetaFieldLambdaO_eq_closedBall]
    exact h'

/-- Root image is contained in the field-scaled lambda-O hull. -/
theorem rootExtensionProductThetaImageSet_subset_fieldScaledHull :
    rootExtensionProductThetaImageSet T ⊆ rootExtensionProductFieldScaledHull T := by
  rw [rootExtensionProductFieldScaledHull_eq_imageHull]
  exact rootExtensionProductThetaImageSet_subset_imageHull T

end LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual

end