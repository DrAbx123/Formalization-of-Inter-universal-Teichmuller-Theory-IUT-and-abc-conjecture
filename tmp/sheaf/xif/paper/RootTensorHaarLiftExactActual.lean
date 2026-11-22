import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootTensorHaarActual

/-! # Exact API gap for lifting L-Haar to the root tensor block

Actual Haar on L is constructed in PaperRootTensorHaarActual.  The native
FinitePadicTensor carrier over L does not synthesize the normed additive group,
proper-space or measurable-space instances needed by Measure.addHaarMeasure.
This file records those exact missing instances; no tensor Haar is fabricated.

No sorry/axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.RootTensorHaarLiftExactActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Exact missing tensor-block Haar API: normed additive group and measurable
structure on the native FinitePadicTensor over L. -/
def RootTensorHaarLiftExactMissing : Prop :=
  Nonempty (NormedAddCommGroup (rootTensorBlock T b)) ∧
    Nonempty (MeasurableSpace (rootTensorBlock T b))

/-- The actual L-Haar remains available; this is not a tensor Haar. -/
theorem actualLHaarData : Nonempty (RootNormedHaarData T b) :=
  ⟨rootNormedHaarData T b⟩

end LeanFormal.IUT.XiFPaper.RootTensorHaarLiftExactActual

end