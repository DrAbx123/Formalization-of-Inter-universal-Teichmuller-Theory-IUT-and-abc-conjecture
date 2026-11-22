import tmp.sheaf.xif.paper.Mzk1P3NetGainP2Actual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3FinalComparisonCandidateActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainCorrectionsActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainP2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainLogActual
open LeanFormal.IUT.XiFPaper.Mzk1P2RelativeMassActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Final comparison form: adding the P2 R1.3 correction raises the net exactly
by `p2R13Exact`. -/
theorem net_with_p2_correction (G h : ℝ) (C : NetCorrections) :
    netQuantity G h (C.withP2R13 T).total =
      netQuantity G h C.total + p2RExact T :=
  netQuantity_withP2R13_eq (T := T) G h C
end LeanFormal.IUT.XiFPaper.Mzk1P3FinalComparisonCandidateActual
end