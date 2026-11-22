import tmp.sheaf.xif.paper.S349C3TensorLatticeRegionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S349C3TensorLatticeRegionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2826C3RegionFractionalLatticeIdActual

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The SG3b alternative target: the pure-tensor C3 log-shell region should be
a fractional-lattice translate of the holomorphic lattice. -/
def S2826C3RegionFractionalLatticeId (c : C3.tensorIndex -> Real) : Prop :=
  actualC3LogShellTensorRegion C3 =
    (((arithmeticTupleFractionalLattice C3.tensorPlaces C3.tensorTuple c *
      arithmeticTupleHolomorphicLattice C3.tensorPlaces C3.tensorTuple :
        Submodule ℤ_[C3.p]
          (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)) :
      Set (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)))

/-- Actual S349 form: the pure-tensor region is the tensor log-shell region. -/
theorem S2826_region_eq_tensorLogShellRegion :
    actualC3LogShellTensorRegion C3 =
      tensorLogShellRegion
        (fun i : C3.tensorIndex => C3LogShellFiber C3 i) :=
  actualC3LogShellTensorRegion_eq_tensorLogShellRegion C3

/-- Actual S349 inclusion: the pure-tensor region lies in the corrected lattice
region. -/
theorem S2826_region_subset_latticeRegion :
    actualC3LogShellTensorRegion C3 ⊆
      actualC3LogShellTensorLatticeRegion C3 :=
  actualC3LogShellTensorRegion_subset_latticeRegion C3

/-- A necessary condition for the fractional-lattice identification: if it held,
then the fractional lattice would be contained in the corrected tensor lattice. -/
theorem S2826_fractionalLatticeId_implies_lattice_subset
    {c : C3.tensorIndex -> Real}
    (h : S2826C3RegionFractionalLatticeId C3 c) :
    (((arithmeticTupleFractionalLattice C3.tensorPlaces C3.tensorTuple c *
      arithmeticTupleHolomorphicLattice C3.tensorPlaces C3.tensorTuple :
        Submodule ℤ_[C3.p]
          (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)) :
      Set (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))) ⊆
        actualC3LogShellTensorLatticeRegion C3 := by
  rw [← h]
  exact S2826_region_subset_latticeRegion C3

#check S2826C3RegionFractionalLatticeId
#check S2826_region_eq_tensorLogShellRegion
#check S2826_region_subset_latticeRegion
#check S2826_fractionalLatticeId_implies_lattice_subset
#print axioms S2826_region_eq_tensorLogShellRegion
#print axioms S2826_region_subset_latticeRegion
#print axioms S2826_fractionalLatticeId_implies_lattice_subset

end LeanFormal.IUT.XiFPaper.S2826C3RegionFractionalLatticeIdActual
end
