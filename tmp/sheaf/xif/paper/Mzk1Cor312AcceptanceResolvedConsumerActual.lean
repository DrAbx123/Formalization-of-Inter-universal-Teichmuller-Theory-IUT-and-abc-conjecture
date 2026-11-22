import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceResolvedActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual

/-! # Resolved acceptance consumer (abstract realization form) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceResolvedConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The resolved realization carries the derived strict volume increase. -/
theorem resolved_strict_measure (D : KummerXiERealization T) :
    D.vol {qPilotInThetaCarrier T} < D.vol (s1902Hull T) :=
  D.strict_measure

/-- Abstract consumer: any realization strict_measure gives the strict signed gap. -/
theorem resolved_strict_signed (D : KummerXiERealization T) :
    -D.vol (s1902Hull T) < -D.vol {qPilotInThetaCarrier T} := by
  have h := D.strict_measure
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceResolvedConsumerActual
