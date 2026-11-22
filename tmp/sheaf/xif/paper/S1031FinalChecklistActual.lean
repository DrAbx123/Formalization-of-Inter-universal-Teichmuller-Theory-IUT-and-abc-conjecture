import tmp.sheaf.xif.paper.S1025S994FiniteInputActual
import tmp.sheaf.xif.paper.S1027FinalActualInputActual

/-! # S1031: updated final checklist

S994FiniteInput is now ACTUAL (S1025).  Positivity and finiteness are gone
from the exact list.  The remaining exact items are the source link, its
identification, and the finite link evidence; sourceQ is the hQ part of the
source link (S1009/S1017).  This file does not fake an unconditional link. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S1031FinalChecklistActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S1025S994FiniteInputActual
open LeanFormal.IUT.XiFPaper.S1027FinalActualInputActual
open MeasureTheory

universe u ua uv upi umon ui
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- S994FiniteInput is actual: actual finite linearization, actual qPilot
positivity from S1023, actual hull finiteness from S1008. -/
theorem s1031S994FiniteInput_actual : Nonempty (S994FiniteInput T) :=
  nonempty_s994FiniteInput (l := l) T

/-- Updated final exact checklist. -/
structure S1031FinalExactChecklist where
  finiteInput : S994FiniteInput T
  sourceQ : Prop
  sourceLink : Prop
  linkIdentification : Prop
  finiteLinks : Prop

/-- Actual checklist constructor: S994FiniteInput is filled by the actual
S1025 instance; the remaining four fields are exactly the remaining inputs. -/
noncomputable def s1031FinalChecklist
    (sourceQ sourceLink linkIdentification finiteLinks : Prop) :
    S1031FinalExactChecklist T where
  finiteInput := s994FiniteInput_actual (l := l) T
  sourceQ := sourceQ
  sourceLink := sourceLink
  linkIdentification := linkIdentification
  finiteLinks := finiteLinks

/-- The remaining exact items, separated from the actual finite input. -/
def S1031RemainingExact
    (sourceQ sourceLink linkIdentification finiteLinks : Prop) : Prop :=
  sourceQ ∧ sourceLink ∧ linkIdentification ∧ finiteLinks

end LeanFormal.IUT.XiFPaper.S1031FinalChecklistActual
end