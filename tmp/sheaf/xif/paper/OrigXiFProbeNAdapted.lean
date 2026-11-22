import tmp.sheaf.xif.paper.PaperXiFFinalActual

set_option pp.universes false

#check LeanFormal.IUT.XiFPaper.PaperXiFFinalActual.paperLevelXiF_actual
#check LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.ActualPaperXiFTarget

namespace LeanFormal.IUT.OrigXiFProbeNAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.PaperXiFFinalActual

example {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l) :
    ActualPaperXiFTarget (l := l) T :=
  paperLevelXiF_actual (l := l) T

end LeanFormal.IUT.OrigXiFProbeNAdapted
