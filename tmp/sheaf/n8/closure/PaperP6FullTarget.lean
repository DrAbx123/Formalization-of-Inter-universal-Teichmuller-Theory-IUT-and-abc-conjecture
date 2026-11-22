import tmp.sheaf.n8.closure.PaperP6Target
import tmp.sheaf.n8.closure.PaperValuesBoundedActual
import tmp.sheaf.n8.closure.C6UnitRefNormalized

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperP6FullTarget

open LeanFormal.IUT.N8Closure.PaperP6Target2
open LeanFormal.IUT.N8Closure.PaperValuesBoundedActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev Block (S : SourceInitialThetaData l) : Type :=
  ArithmeticTensorTupleBlock (places S) (tuple S)

local instance : MeasurableSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace

/-- Paper ValuesBounded: every source region inside the C6 Theta hull has
normalized log-volume at most the Theta log-volume. -/
def PaperValuesBoundedTarget : Prop :=
  ∀ T : Set (Block S),
    T ⊆ c6Hull (places := places S) (tuple := tuple S)
      (rawData (places S) (tuple S)) →
    Real.log ((c6UnitRefNormalizedData (places S) (tuple S) T).toReal) ≤
      thetaLogVolume S

theorem paperValuesBoundedTarget_actual : PaperValuesBoundedTarget S :=
  fun T hT => paperValueLog_le_theta_of_subset S T hT

/-- Combined paper P6 target. -/
def PaperP6FullTarget : Prop :=
  PaperP6Target S ∧ PaperValuesBoundedTarget S

theorem paperP6FullTarget_actual : PaperP6FullTarget S :=
  ⟨paperP6Target_actual S, paperValuesBoundedTarget_actual S⟩

end LeanFormal.IUT.N8Closure.PaperP6FullTarget

end
