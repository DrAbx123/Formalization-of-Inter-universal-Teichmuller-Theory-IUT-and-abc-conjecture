/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0PaperInputVActual
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputVConsumptionActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P0ComparisonBridgesActual
open LeanFormal.IUT.XiFPaper.Mzk1P0RemainingBridgeDataActual
open LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputVActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
variable {l : PrimeGeFive}
variable (X : PaperInputV l)
def paperComparisonInput_of_VInput : PaperComparisonInput l X.P := X.B
theorem LPaperInstance_of_VInput (h : NativeComparison X.P.X.S X.B.b) :
    LPaperInstance X.B.I X.B.place :=
  LPaperInstance_of_paperInputV X h
end LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputVConsumptionActual
end
