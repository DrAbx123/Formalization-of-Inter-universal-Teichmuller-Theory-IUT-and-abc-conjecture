import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegralTensorLattice

/-!
# S349: paper tensor packet unit region is the tensor lattice, not the
pure-tensor image

The paper tensor packet I(S^pm) is the tensor product of the local integral
log-shells, i.e. the Z_p-span of the pure tensors, not the set of pure tensors
alone.  FinitePadicTensorLogShellRegion explicitly does not assert positive
measure of the pure-tensor image.

This file constructs the corrected C3 region as tensorLogShellLattice (the
integral lattice), proves the pure-tensor image is contained in it, and proves
the lattice region is open, compact, positive and finite under actual Haar.
No unitBall/closure/log-zero surrogate is used.  No inequality is stated.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S349C3TensorLatticeRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance c3LatticeBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance c3LatticeBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The corrected paper unit region: the actual tensor integral lattice of the
local log-shells, not merely the pure-tensor image. -/
noncomputable def actualC3LogShellTensorLattice :
    Submodule ℤ_[C3.p] (C3LogShellTensorBlock C3) :=
  tensorLogShellLattice (p := C3.p)
    (A := fun i : C3.tensorIndex => C3LogShellFiber C3 i)

/-- The corrected actual unit region as a set. -/
noncomputable def actualC3LogShellTensorLatticeRegion :
    Set (C3LogShellTensorBlock C3) :=
  (actualC3LogShellTensorLattice C3 : Set (C3LogShellTensorBlock C3))

/-- The pure-tensor C3 image is exactly the tensorLogShellRegion of the local
integral log-shells. -/
theorem actualC3LogShellTensorRegion_eq_tensorLogShellRegion :
    actualC3LogShellTensorRegion C3 =
      tensorLogShellRegion (p := C3.p)
        (A := fun i : C3.tensorIndex => C3LogShellFiber C3 i) := by
  unfold actualC3LogShellTensorRegion tensorLogShellRegion
  congr 1
  funext i
  exact actualC3LogShell_eq_integralLogShell C3 i

/-- The pure-tensor image is contained in the corrected tensor lattice region. -/
theorem actualC3LogShellTensorRegion_subset_latticeRegion :
    actualC3LogShellTensorRegion C3 ⊆
      actualC3LogShellTensorLatticeRegion C3 := by
  intro x hx
  rw [actualC3LogShellTensorRegion_eq_tensorLogShellRegion C3] at hx
  change x ∈ tensorLogShellLattice (p := C3.p)
    (A := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
  exact tensorLogShellRegion_subset_lattice
    (p := C3.p) (A := fun i : C3.tensorIndex => C3LogShellFiber C3 i) hx

/-- The corrected tensor lattice region is open. -/
theorem actualC3LogShellTensorLatticeRegion_isOpen :
    IsOpen (actualC3LogShellTensorLatticeRegion C3) := by
  unfold actualC3LogShellTensorLatticeRegion actualC3LogShellTensorLattice
  exact isOpen_tensorLogShellLattice (p := C3.p)
    (A := fun i : C3.tensorIndex => C3LogShellFiber C3 i)

/-- The corrected tensor lattice region is compact. -/
theorem actualC3LogShellTensorLatticeRegion_compact :
    IsCompact (actualC3LogShellTensorLatticeRegion C3) := by
  unfold actualC3LogShellTensorLatticeRegion actualC3LogShellTensorLattice
  exact isCompact_tensorLogShellLattice (p := C3.p)
    (A := fun i : C3.tensorIndex => C3LogShellFiber C3 i)

/-- The corrected tensor lattice region has positive actual Haar. -/
theorem actualC3LogShellTensorLatticeRegion_measure_pos :
    0 < actualC3LogShellTensorHaar C3
      (actualC3LogShellTensorLatticeRegion C3) := by
  have hne : (actualC3LogShellTensorLatticeRegion C3).Nonempty :=
    ⟨0, (actualC3LogShellTensorLattice C3).zero_mem⟩
  exact (actualC3LogShellTensorLatticeRegion_isOpen C3).measure_pos
    (actualC3LogShellTensorHaar C3) hne

/-- The corrected tensor lattice region has finite actual Haar. -/
theorem actualC3LogShellTensorLatticeRegion_measure_lt_top :
    actualC3LogShellTensorHaar C3
      (actualC3LogShellTensorLatticeRegion C3) < ⊤ :=
  (actualC3LogShellTensorLatticeRegion_compact C3).measure_lt_top

/-- Actual corrected C3 tensor lattice region object. -/
structure ActualC3TensorLatticeRegion where
  lattice : Submodule ℤ_[C3.p] (C3LogShellTensorBlock C3)
  lattice_eq : lattice = actualC3LogShellTensorLattice C3
  region : Set (C3LogShellTensorBlock C3)
  region_eq : region = (lattice : Set (C3LogShellTensorBlock C3))
  region_open : IsOpen region
  region_compact : IsCompact region
  haar : Measure (C3LogShellTensorBlock C3)
  haar_eq : haar = actualC3LogShellTensorHaar C3
  region_pos : 0 < haar region
  region_lt_top : haar region < ⊤
  pureTensor_subset : actualC3LogShellTensorRegion C3 ⊆ region

/-- Actual corrected C3 tensor lattice region constructor. -/
noncomputable def actualC3TensorLatticeRegion :
    ActualC3TensorLatticeRegion C3 where
  lattice := actualC3LogShellTensorLattice C3
  lattice_eq := rfl
  region := actualC3LogShellTensorLatticeRegion C3
  region_eq := rfl
  region_open := actualC3LogShellTensorLatticeRegion_isOpen C3
  region_compact := actualC3LogShellTensorLatticeRegion_compact C3
  haar := actualC3LogShellTensorHaar C3
  haar_eq := rfl
  region_pos := actualC3LogShellTensorLatticeRegion_measure_pos C3
  region_lt_top := actualC3LogShellTensorLatticeRegion_measure_lt_top C3
  pureTensor_subset := actualC3LogShellTensorRegion_subset_latticeRegion C3

end LeanFormal.IUT.XiFPaper.S349C3TensorLatticeRegionActual

end
