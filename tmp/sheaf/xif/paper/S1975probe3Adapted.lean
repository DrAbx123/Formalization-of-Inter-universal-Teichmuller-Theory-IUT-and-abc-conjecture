import tmp.sheaf.xif.paper.S1962R1AbstractActionActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionIsometry

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open scoped Topology

namespace Probe3

variable {K : Type*} [Field K] [NumberField K]
variable (place : NumberField.FinitePlace K)

/-- Open balls of the spectral norm are open for the finite-subfield ind topology. -/
theorem isOpen_ind_ball (z : SourceAlgebraicClosure place) {ε : ℝ} (hε : 0 < ε) :
    IsOpen[sourceAlgebraicFieldIndTopology place] {y | ‖y - z‖ < ε} := by
  rw [isOpen_algebraicFieldIndTopology_iff]
  intro F
  have hcont : Continuous fun y : F.val => ((y : SourceAlgebraicClosure place) - z) :=
    (isometry_intermediateField_inclusion F.val).continuous.sub continuous_const
  exact isOpen_lt (continuous_norm.comp hcont) continuous_const

end Probe3
