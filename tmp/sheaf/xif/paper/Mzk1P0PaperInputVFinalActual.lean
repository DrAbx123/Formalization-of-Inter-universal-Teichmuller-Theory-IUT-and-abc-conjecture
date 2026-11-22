/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0PaperInputVConsumptionActual
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputVFinalActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P0ComparisonBridgesActual
open LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputVActual
open LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputVConsumptionActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
variable {l : PrimeGeFive}
variable (X : PaperInputV l)
theorem LPaperInstance_of_paperInputV_final
    (h : NativeComparison X.P.X.S X.B.b) :
    LPaperInstance X.B.I X.B.place :=
  LPaperInstance_of_VInput X h
theorem paperComparisonInput_of_paperInputV_final :
    PaperComparisonInput l X.P := X.B
end LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputVFinalActual
end
