import tmp.sheaf.n8.closure.PaperP6NormalizedValuesActual
import tmp.sheaf.n8.closure.PaperNormalizedLogBridge

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperP6AlignedTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.PaperP6NormalizedValuesActual
open LeanFormal.IUT.N8Closure.PaperNormalizedLogBridge
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7QPilotMassActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev Block (S : SourceInitialThetaData l) : Type :=
  ArithmeticTensorTupleBlock (places S) (tuple S)

local instance : MeasurableSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace
local instance rawAddHaar :
    (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu.IsAddHaarMeasure :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).addHaar

theorem d_eq_finrank_block : d S = Module.finrank ℚ_[pNat S] (Block S) := by
  unfold d
  exact (C7QPilotRegionActual.e S).finrank_eq.symm

/-- The paper normalizedTheta equals the actual C6 normalizedLogVolume of c6Hull. -/
theorem normalizedTheta_eq_c6NormalizedLogVolume :
    (PaperP6NormalizedValuesActual.normalizedTheta S) =
      (C6ActualIQData.actual (places S) (tuple S)
        (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu).normalizedLogVolume
        (c6Hull (places := places S) (tuple := tuple S)
          (C6NormalizedTensorHaar.rawData (places S) (tuple S))) := by
  unfold PaperP6NormalizedValuesActual.normalizedTheta C7MassFormulaZeroSorry.thetaLogVolume
  rw [d_eq_finrank_block S]
  change PaperNormalizedLogBridge.normalizedTheta S =
    (C6ActualIQData.actual (places S) (tuple S)
      (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu).normalizedLogVolume
      (c6Hull (places := places S) (tuple := tuple S)
        (C6NormalizedTensorHaar.rawData (places S) (tuple S)))
  exact PaperNormalizedLogBridge.normalizedTheta_eq_c6NormalizedLogVolume S

/-- Aligned normalized target: normalized values under Theta, plus the C6
normalizedLogVolume bridge. -/
def PaperP6AlignedTarget : Prop :=
  PaperP6NormalizedTarget S ∧
    (PaperP6NormalizedValuesActual.normalizedTheta S =
      (C6ActualIQData.actual (places S) (tuple S)
        (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu).normalizedLogVolume
        (c6Hull (places := places S) (tuple := tuple S)
          (C6NormalizedTensorHaar.rawData (places S) (tuple S))))

theorem paperP6AlignedTarget_actual : PaperP6AlignedTarget S :=
  ⟨paperP6NormalizedTarget_actual S, normalizedTheta_eq_c6NormalizedLogVolume S⟩

end LeanFormal.IUT.N8Closure.PaperP6AlignedTarget

end
