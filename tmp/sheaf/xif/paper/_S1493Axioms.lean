import tmp.sheaf.xif.paper.S1493KSideTateTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1493KSideTateTransportActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

#print axioms s1493CurveTransport
#print axioms completion_isAlgebraic
#print axioms sectionClosureEquiv
#print axioms sectionClosureEquiv_tateParameterUnit
#print axioms s1493KSideTateData_iff_pointTransport
#print axioms s1493CurveTransport_nonempty
