import tmp.sheaf.xif.paper.RootThetaToCompletionImageMapActual
import tmp.sheaf.xif.paper.PaperC3TensorBlockActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

/-!
# Completion-side hull of the root Theta power image

The S70 power image is

  ThetaLabel j |-> qUnit_v^(j^2)

in the product completion carrier.  This file maps it to the actual completion
tensor block (pure tensor) and puts it inside the actual qUnit lambda-O hull of
PaperC3TensorBlockActual.

This is a completion qUnit hull, not the extension root hull.  The extension
root hull normalized log and the exact hull comparison remain an exact gap.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.RootThetaCompletionHullActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.RootThetaToCompletionImageMapActual
open MeasureTheory

universe u v

variable {l : PrimeGeFive}
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Actual completion tensor image of the root Theta power image. -/
noncomputable def rootThetaCompletionTensorImagePoint
    (j : ThetaLabel (l := l)) : Block (G := G) :=
  arithmeticTupleTprod (fun v (_ : Unit) => G.place v) (fun _ => ())
    (rootThetaCompletionImagePoint (G := G) j)

/-- The completion tensor image is exactly the block q-parameter image point. -/
theorem rootThetaCompletionTensorImagePoint_eq
    (j : ThetaLabel (l := l)) :
    rootThetaCompletionTensorImagePoint (G := G) j =
      paperQParameterImagePoint (G := G) (l := l)
        (thetaLabelToSigned (l := l) j) := rfl

/-- Actual containment of the root power image in the completion qUnit lambda-O
hull, under the unit norm condition. -/
theorem rootThetaCompletionTensorImagePoint_mem_qUnitLambdaHull
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1)
    (j : ThetaLabel (l := l)) :
    rootThetaCompletionTensorImagePoint (G := G) j ∈
      qParameterUnitLambdaHull (G := G) := by
  rw [rootThetaCompletionTensorImagePoint_eq]
  have hmem : paperQParameterImagePoint (G := G) (l := l)
      (thetaLabelToSigned (l := l) j) ∈
      paperQParameterNonzeroImageSet (G := G) (l := l) :=
    ⟨thetaLabelToSigned (l := l) j,
      thetaLabel_gaussExponent_one_le (l := l) j, rfl⟩
  exact paperQParameterNonzeroImageSet_subset_qParameterUnitLambdaRegion
    (G := G) (l := l) hq hmem

/-- Actual completion-side image/hull data. -/
structure CompletionPowerHullData where
  image : ThetaLabel (l := l) → Block (G := G)
  image_eq : image = rootThetaCompletionTensorImagePoint (G := G)
  hull : Set (Block (G := G))
  hull_eq : hull = qParameterUnitLambdaHull (G := G)
  image_subset_hull : ∀ j : ThetaLabel (l := l), image j ∈ hull

/-- Actual completion-side hull data. -/
noncomputable def completionPowerHullData
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    CompletionPowerHullData (G := G) (l := l) where
  image := rootThetaCompletionTensorImagePoint (G := G)
  image_eq := rfl
  hull := qParameterUnitLambdaHull (G := G)
  hull_eq := rfl
  image_subset_hull := fun j =>
    rootThetaCompletionTensorImagePoint_mem_qUnitLambdaHull
      (G := G) (l := l) hq j

/-- Actual completion-side normalized log of the qUnit hull. -/
noncomputable def completionPowerHullLog
    [MeasurableSpace (Block (G := G))]
    (mu : Measure (Block (G := G))) : Real :=
  arithmeticTupleNormalizedLogVolume
    (fun v (_ : Unit) => G.place v) (fun _ => ()) mu
    (qParameterUnitLambdaHull (G := G))

/-- Exact gap: the extension root hull normalized log and its comparison with
the completion qUnit hull log are not constructed. -/
structure RootExtensionCompletionHullLogGap
    [MeasurableSpace (Block (G := G))]
    (mu : Measure (Block (G := G))) : Type where
  extensionRootHullLog : Prop
  completionHullLog_eq : Prop
  logComparison : Prop
  hullMap : Prop

/-- Exact missing log/hull comparison. -/
def RootExtensionCompletionHullLogGapRequired
    [MeasurableSpace (Block (G := G))]
    (mu : Measure (Block (G := G))) : Prop :=
  Nonempty (RootExtensionCompletionHullLogGap (G := G) (l := l) mu)


/-- Conditional qPilot comparison from actual containment and normalized-log
monotonicity.  The qPilot region/log identification is an explicit input, not
faked here. -/
theorem qPilotLog_le_completionPowerHullLog_of_subset
    [MeasurableSpace (Block (G := G))]
    (mu : Measure (Block (G := G))) [Measure.IsAddHaarMeasure mu]
    (qPilotRegion : Set (Block (G := G)))
    (hsub : qPilotRegion ⊆ qParameterUnitLambdaHull (G := G))
    (hqpos : 0 < mu qPilotRegion)
    (hhullfin : mu (qParameterUnitLambdaHull (G := G)) < ⊤) :
    arithmeticTupleNormalizedLogVolume
        (fun v (_ : Unit) => G.place v) (fun _ => ()) mu qPilotRegion ≤
      completionPowerHullLog (G := G) (l := l) mu := by
  unfold completionPowerHullLog
  exact arithmeticTupleNormalizedLogVolume_mono
    (fun v (_ : Unit) => G.place v) (fun _ => ()) mu hsub hqpos hhullfin

/-- Conditional qPilot log comparison, stated with the qPilot log function
identified as the normalized log of the qPilot region. -/
theorem qPilotLog_le_completionPowerHullLog
    [MeasurableSpace (Block (G := G))]
    (mu : Measure (Block (G := G))) [Measure.IsAddHaarMeasure mu]
    (qPilotRegion : Set (Block (G := G)))
    (qPilotLog : Real)
    (hqPilotLog : qPilotLog =
      arithmeticTupleNormalizedLogVolume
        (fun v (_ : Unit) => G.place v) (fun _ => ()) mu qPilotRegion)
    (hsub : qPilotRegion ⊆ qParameterUnitLambdaHull (G := G))
    (hqpos : 0 < mu qPilotRegion)
    (hhullfin : mu (qParameterUnitLambdaHull (G := G)) < ⊤) :
    qPilotLog ≤ completionPowerHullLog (G := G) (l := l) mu := by
  rw [hqPilotLog]
  exact qPilotLog_le_completionPowerHullLog_of_subset
    (G := G) (l := l) mu qPilotRegion hsub hqpos hhullfin

/-- Exact direction/factor gap: a qPilot region/log identification and its
subset in the completion qUnit hull are required; the reverse inclusion, any
factor normalization, and the extension root hull relation are not asserted. -/
structure QPilotCompletionPowerDirectionGap
    [MeasurableSpace (Block (G := G))]
    (mu : Measure (Block (G := G))) where
  qPilotRegion : Set (Block (G := G))
  qPilotLog : Real
  qPilotRegion_actual : Prop
  qPilotLog_eq : Prop
  qPilotRegion_subset_completionHull : Prop
  qPilot_measure_pos : Prop
  completionHull_measure_finite : Prop
  factor_normalization : Prop
  reverse_inclusion : Prop

/-- Exact missing qPilot comparison object. -/
def QPilotCompletionPowerDirectionGapRequired
    [MeasurableSpace (Block (G := G))]
    (mu : Measure (Block (G := G))) : Prop :=
  Nonempty (QPilotCompletionPowerDirectionGap (G := G) (l := l) mu)

/-- Exact gap for comparing with the root-coefficient/rootNormHull: no generic
root-coefficient hull is identified with the completion qUnit hull. -/
structure RootCoefficientCompletionHullRelationGap : Type where
  rootNormHull : Prop
  completionPowerHull : Prop
  subset_one_way : Prop
  normalized_log_comparison : Prop

end LeanFormal.IUT.XiFPaper.RootThetaCompletionHullActual
end
