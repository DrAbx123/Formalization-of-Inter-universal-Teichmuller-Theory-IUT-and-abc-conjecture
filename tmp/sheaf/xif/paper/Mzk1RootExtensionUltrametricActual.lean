import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceAlgebraicClosure

/-!
# A553: ultrametric instance bridge for the root extension

`rootNormedAmbient T b` is definitionally `SourceAlgebraicClosure (qVFamTensorPlace T b)`
(its normed-field instance is `inferInstanceAs` of that type), and the ABC bridge
has `IsUltrametricDist (SourceAlgebraicClosure place)` (`FinitePlaceSourceAlgebraicClosure`).
This file transports that instance to `rootNormedAmbient` and exposes the
subtype instance on `rootNormedExtension`, which is needed for the
ultrametric-cylinder proof of the annulus positivity in A552/A553.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1RootExtensionUltrametricActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open MeasureTheory

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The ambient algebraic closure is ultrametric (transported from the ABC bridge
instance on `SourceAlgebraicClosure`). -/
local instance rootNormedAmbientUltrametric :
    IsUltrametricDist (rootNormedAmbient T b) :=
  inferInstanceAs (IsUltrametricDist (SourceAlgebraicClosure (qVFamTensorPlace T b)))

/-- The finite root extension carries the inherited ultrametric structure. -/
theorem rootNormedExtension_ultrametric :
    IsUltrametricDist (rootNormedExtension T b) :=
  inferInstance

/-- Ultrametric maximum triangle for the root extension norm. -/
theorem rootNormedExtension_norm_add_le_max (x y : rootNormedExtension T b) :
    ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  letI : IsUltrametricDist (rootNormedExtension T b) := rootNormedExtension_ultrametric T b
  exact IsUltrametricDist.norm_add_le_max x y

end LeanFormal.IUT.XiFPaper.Mzk1RootExtensionUltrametricActual
