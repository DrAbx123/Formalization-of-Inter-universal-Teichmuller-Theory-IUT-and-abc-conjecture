import tmp.sheaf.xif.paper.S946TensorPaperSContainmentActual
import tmp.sheaf.xif.paper.S945CarrierTopologyActual

/-! # S956: closure containment, not point-set union containment

S946's paperTensorS is only the point-set theta+Ind union.  The paper target is
qPilot image ⊆ closure(paperTensorS), not ⊆ the union itself.  This file
constructs the closure target under an explicit TopologicalSpace instance and
does NOT assert the union containment. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S956ClosureContainmentActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S946TensorPaperSContainmentActual
open LeanFormal.IUT.XiFPaper.S945CarrierTopologyActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable [TopologicalSpace (FinalLValuedCarrier T b)]

/-- Closure of the actual theta+Ind point-set union. -/
noncomputable def paperTensorSClosure : Set (FinalLValuedCarrier T b) :=
  closure (paperTensorS (l := l) T b)

/-- Correct paper containment target: closure, not union. -/
def S956ClosureContainment : Prop :=
  qPilotPaperImageInLValued (l := l) T b ⊆ paperTensorSClosure (l := l) T b

/-- Old S946 point-set union containment; stronger than the paper target and
not asserted. -/
def S956UnionContainment : Prop :=
  qPilotPaperImageInLValued (l := l) T b ⊆ paperTensorS (l := l) T b

/-- If the stronger union containment holds, it implies the paper closure
target.  The converse is not claimed. -/
theorem closureContainment_of_unionContainment
    (h : S956UnionContainment (l := l) T b) :
    S956ClosureContainment (l := l) T b :=
  fun x hx => subset_closure (h hx)

/-- Exact minimal topology datum needed for the closure target. -/
def S956TopologyGap : Prop :=
  S945CarrierTopologyDataRequired (l := l) T b

end LeanFormal.IUT.XiFPaper.S956ClosureContainmentActual
end