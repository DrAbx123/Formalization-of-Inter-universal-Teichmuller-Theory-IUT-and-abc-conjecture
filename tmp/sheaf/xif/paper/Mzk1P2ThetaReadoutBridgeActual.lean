/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2ThetaAllowedImageActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P2ThetaAllowedImageActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open scoped BigOperators ENNReal

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]

/-- Theta readout bridge: the theta landing lies in allowed lambda-O. -/
theorem p2ThetaReadoutBridge (b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))
    (j : ThetaLabel (l := l)) :
    rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) ∈ rootThetaFieldLambdaO T b :=
  p2ThetaValue_mem_allowedO T b j

end
