import tmp.sheaf.n8.closure.PaperP6Target
import tmp.sheaf.n8.closure.PaperAllQPilotRegions

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperP6FamilyTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.PaperP6Target2
open LeanFormal.IUT.N8Closure.PaperAllQPilotRegions
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev Block (S : SourceInitialThetaData l) : Type :=
  ArithmeticTensorTupleBlock (places S) (tuple S)

local instance : MeasurableSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace

/-- Actual q-pilot family bound: every norm<=1 q-pilot region is Theta-bounded. -/
def PaperQPilotFamilyBounded : Prop :=
  ∀ T ∈ allQPilotRegions S,
    Real.log
      ((c6UnitRefNormalizedData (places S) (tuple S) T).toReal) ≤
      thetaLogVolume S

theorem paperQPilotFamilyBounded_actual :
    PaperQPilotFamilyBounded S :=
  allQPilotRegions_bounded S

/-- Paper P6 target with an actual q-pilot values family instead of hull-universal only. -/
def PaperP6FamilyTarget : Prop :=
  PaperP6Target S ∧ PaperQPilotFamilyBounded S

theorem paperP6FamilyTarget_actual :
    PaperP6FamilyTarget S :=
  ⟨paperP6Target_actual S, paperQPilotFamilyBounded_actual S⟩

end LeanFormal.IUT.N8Closure.PaperP6FamilyTarget

end
