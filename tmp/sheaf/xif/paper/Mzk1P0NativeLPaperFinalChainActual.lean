/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0PaperInputVFinalActual
import tmp.sheaf.xif.paper.Mzk1P0NativeThetaR13DefectActual
import tmp.sheaf.xif.paper.Mzk1P0NativeThetaR13BoundActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeLPaperFinalChainActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P0ComparisonBridgesActual
open LeanFormal.IUT.XiFPaper.Mzk1P0RemainingBridgeDataActual
open LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputVActual
open LeanFormal.IUT.XiFPaper.Mzk1P0PaperInputVFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13DefectActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaR13BoundActual
variable {l : PrimeGeFive}
variable (X : PaperInputV l)
/-- Final chain: paper input + nonnegative R1.3 defect => LPaperInstance. -/
theorem LPaperInstance_of_paperInputV_of_defect_nonneg
    (h : 0 ≤ thetaR13Defect X.P.X.S X.B.b) :
    LPaperInstance X.B.I X.B.place :=
  LPaperInstance_of_paperInputV_final X
    (nativeComparison_of_defect_nonneg X.P.X.S X.B.b h)
/-- Final chain via explicit R1.3 equality bridge. -/
theorem LPaperInstance_of_paperInputV_of_thetaR13Bridge
    (h : ThetaR13Bridge X.P.X.S X.B.b) :
    LPaperInstance X.B.I X.B.place :=
  LPaperInstance_of_paperInputV_final X
    (nativeComparison_of_thetaR13Bridge X.P.X.S X.B.b h)
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeLPaperFinalChainActual
end
