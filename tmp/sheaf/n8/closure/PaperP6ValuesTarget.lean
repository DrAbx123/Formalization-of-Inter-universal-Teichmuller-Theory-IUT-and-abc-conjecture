import tmp.sheaf.n8.closure.PaperValuesFamilyActual
import tmp.sheaf.n8.closure.PaperP6Target

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperP6ValuesTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.PaperP6Target2
open LeanFormal.IUT.N8Closure.PaperValuesFamilyActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

/-- Paper P6 target with an actual values set: Q<=Theta finite, and every
actual q-pilot value is at most Theta. -/
def PaperP6ValuesTarget : Prop :=
  PaperP6Target S ∧ ∀ z ∈ paperValueSet S, z ≤ thetaLogVolume S

theorem paperP6ValuesTarget_actual : PaperP6ValuesTarget S :=
  ⟨paperP6Target_actual S, paperValueSet_bounded S⟩

end LeanFormal.IUT.N8Closure.PaperP6ValuesTarget

end
