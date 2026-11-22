/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2MultiIndexLandingActual
noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2TensorLandingActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockSumActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]

/-- The multi-index tensor landing (product carrier model) is integral. -/
theorem p2TensorLanding_integral
    {ι : Type*} [Fintype ι] (D : P2LabelBlockSumData T ι) :
    p2MultiIndexLanding T D ∈ rootExtensionProductUnitBall T :=
  p2MultiIndexLanding_mem T D

end LeanFormal.IUT.XiFPaper.Mzk1P2TensorLandingActual

end
