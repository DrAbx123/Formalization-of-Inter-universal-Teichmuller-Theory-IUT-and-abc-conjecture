import tmp.sheaf.n8.closure.PaperValuesBoundedActual
import tmp.sheaf.n8.closure.C6UnitRefNormalized

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C6ImageValueBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.PaperValuesBoundedActual
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
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

theorem c6ImageSet_subset_c6Hull :
    c6ImageSet (places S) (tuple S) (rawData (places S) (tuple S)) ⊆
      c6Hull (places := places S) (tuple := tuple S)
        (rawData (places S) (tuple S)) := by
  letI := (rawData (places S) (tuple S)).addHaar
  intro x hx
  unfold c6ImageSet c6Hull at *
  exact (rawData (places S) (tuple S)).data.iqInterface.imageSet_subset_hull hx

/-- The actual C6 image-set value is bounded by the Theta log-volume. -/
theorem paperC6ImageLog_le_theta :
    Real.log
      ((c6UnitRefNormalizedData (places S) (tuple S)
        (c6ImageSet (places S) (tuple S)
          (rawData (places S) (tuple S)))).toReal) ≤
      thetaLogVolume S :=
  paperValueLog_le_theta_of_subset S _
    (c6ImageSet_subset_c6Hull S)

end LeanFormal.IUT.N8Closure.C6ImageValueBoundActual

end
