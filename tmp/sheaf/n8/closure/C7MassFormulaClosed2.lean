import tmp.sheaf.n8.closure.C7MassFormulaClosed
import tmp.sheaf.n8.closure.C7QPilotMassTransport

/-!
# C7 mass formula: remaining Haar-uniqueness gap

Actual image transport is closed.  The mapped unit-reference normalized Haar
and the Kf normalized Haar are both additive Haar measures with unit mass on
`Integers`; the remaining equality is Haar uniqueness. -/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C7MassFormulaClosed2

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.N8Closure.C7MassFormulaClosed
open LeanFormal.IUT.N8Closure.C7OneFactorAlgEquivConstructed2
open LeanFormal.IUT.N8Closure.C7QPilotMassTransport
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

local instance (S : SourceInitialThetaData l) : MeasurableSpace (PaperKf S) := borel _
local instance (S : SourceInitialThetaData l) : BorelSpace (PaperKf S) := ⟨rfl⟩

/-- Mapped unit-reference normalized C6 Haar. -/
noncomputable def mappedUnitRefNormalized : Measure (PaperKf S) := by
  let T := C6NormalizedTensorHaar.rawData (places S) (tuple S)
  letI := T.measurableSpace
  letI := T.borelSpace
  exact Measure.map (fun y => oneFactorAlgEquiv S y)
    (c6UnitRefNormalizedData (places S) (tuple S))

def MappedNormalizedHaarEq : Prop :=
  mappedUnitRefNormalized S = paperKfNormalizedHaar S

def QPilotMassFormula : Prop :=
  (c6UnitRefNormalizedData (places S) (tuple S)
    (qPilotRegion S)).toReal = ‖q S‖ ^ (C7QPilotMassActual.d S)

end LeanFormal.IUT.N8Closure.C7MassFormulaClosed2

end