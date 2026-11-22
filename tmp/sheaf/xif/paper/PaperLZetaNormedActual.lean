import tmp.sheaf.xif.paper.PaperFinalLMu2lExtensionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceAlgebraicClosure
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- S213: actual normed/measurable structure on FinalL and LZeta has no normed instance.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperLZetaNormedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperFinalLMu2lExtensionActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- FinalL is the spectral-normed source algebraic closure.
instance finalLNormedField : NormedField (FinalL T b) :=
  inferInstanceAs (NormedField
    (SourceAlgebraicClosure ((qVFamTensorPlaces T b () ()).val)))

instance finalLMeasurableSpace : MeasurableSpace (FinalL T b) := borel _

-- LZeta = L(zeta) as a finite intermediate field; normed field via restriction.
instance lZetaNormedField : NormedField (LZeta T b) := inferInstance

instance lZetaMeasurableSpace : MeasurableSpace (LZeta T b) := borel _

-- Minimal exact gap: completeness of LZeta is not available from the
-- spectral algebraic closure, which is not complete.
structure LZetaCompleteSpaceGap where
  completeSpace : CompleteSpace (LZeta T b)
  properSpace : ProperSpace (LZeta T b)

def LZetaCompleteSpaceGapRequired : Prop :=
  Nonempty (LZetaCompleteSpaceGap T b)

#check finalLNormedField
#check lZetaNormedField
#check lZetaMeasurableSpace
#check LZetaCompleteSpaceGap

theorem lZetaField_eq_top : LZetaField T b = ⊤ := by
  ext x
  constructor
  · intro _
    exact IntermediateField.mem_top
  · intro _
    simpa using IntermediateField.algebraMap_mem (LZetaField T b) x

noncomputable def lZetaEquivFinalL : LZeta T b ≃ₗ[FinalL T b] FinalL T b where
  toFun x := (x : FinalL T b)
  invFun x := ⟨x, by rw [lZetaField_eq_top]; trivial⟩
  map_add' x y := rfl
  map_smul' a x := rfl
  left_inv x := rfl
  right_inv x := rfl

instance lZetaFiniteDimensional : FiniteDimensional (FinalL T b) (LZeta T b) :=
  (lZetaEquivFinalL T b).symm.finiteDimensional

#check lZetaField_eq_top
#check lZetaEquivFinalL
#check lZetaFiniteDimensional
end LeanFormal.IUT.XiFPaper.PaperLZetaNormedActual

end