/- Self-contained qPilotMass basic (no RootNuOnePlace dependency; Lead 2026-11-18). -/
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR1QPilotMassBasicActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- paper q-pilot normalized mass: -(cP/(2l)) * log p. -/
noncomputable def qPilotMass (cP : Real) : Real :=
  (-(cP / (2 * (l.value : Real)))) * Real.log (qVFamTensorP T b : Real)

/-- qPilotMass cP = -(cP/(2l)) log p (rfl). -/
theorem qPilotMass_eq (cP : Real) :
    qPilotMass (l := l) T b cP =
      (-(cP / (2 * (l.value : Real)))) * Real.log (qVFamTensorP T b : Real) := rfl

#print axioms qPilotMass_eq

end LeanFormal.IUT.XiFPaper.Mzk1ULR1QPilotMassBasicActual
