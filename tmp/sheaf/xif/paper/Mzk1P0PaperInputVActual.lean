/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
import tmp.sheaf.xif.paper.Mzk1P0PaperInputActual
import tmp.sheaf.xif.paper.Mzk1P0ComparisonBridgesActual
import tmp.sheaf.xif.paper.Mzk1P0RemainingBridgeDataActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputVActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P0RemainingBridgeDataActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
variable {l : PrimeGeFive}
structure PaperInputV (l : PrimeGeFive) where
  P : P05PaperInput l
  vIndex : VIndexDatum P
  B : PaperComparisonInput l P
theorem LPaperInstance_of_paperInputV
    (X : PaperInputV l) (h : NativeComparison X.P.X.S X.B.b) :
    LPaperInstance X.B.I X.B.place :=
  LPaperInstance_of_paperComparison X.P X.B h
end LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputVActual
end
