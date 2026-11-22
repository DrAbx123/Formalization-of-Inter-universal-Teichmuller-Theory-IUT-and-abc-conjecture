import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceResolvedActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-! # Resolved acceptance slots checks (abstract contract form) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedAcceptanceSlotsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- Resolved strict measure of an abstract realization. -/
theorem resolved_strict (D : KummerXiERealization T) :
    D.vol {qPilotInThetaCarrier T} < D.vol (s1902Hull T) :=
  D.strict_measure

/-- `Cor312Conclusion` is exactly the signed slot inequality (general contract). -/
theorem contract_qSigned_le_iff (C : StepXIContract) :
    Cor312Conclusion C ↔ C.qSigned ≤ C.thetaSigned := by
  unfold Cor312Conclusion
  exact Iff.rfl

end LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedAcceptanceSlotsActual
