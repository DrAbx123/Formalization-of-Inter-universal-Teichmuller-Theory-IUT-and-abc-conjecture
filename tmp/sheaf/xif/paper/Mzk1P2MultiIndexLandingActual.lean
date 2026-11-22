/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2LabelBlockSumActual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockSumActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open scoped BigOperators ENNReal

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]

/-- Multi-index landing in the product carrier. -/
noncomputable def p2MultiIndexLanding
    {ι : Type*} [Fintype ι] (D : P2LabelBlockSumData T ι) :
    RootExtensionProductCarrier T :=
  fun b => ∑ i, D.coeff i b * D.thetaGen i b

theorem p2MultiIndexLanding_mem
    {ι : Type*} [Fintype ι] (D : P2LabelBlockSumData T ι) :
    p2MultiIndexLanding T D ∈ rootExtensionProductUnitBall T :=
  p2_labelBlockSum_qGen_mem T D

end
