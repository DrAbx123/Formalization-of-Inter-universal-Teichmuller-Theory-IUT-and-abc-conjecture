import tmp.sheaf.xif.paper.S1427Ind3PlaceComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1427Ind3PlaceComparisonActual

universe ua uv upi umon ui

namespace LeanFormal.IUT.XiFPaper.S1427ConsumerProbe

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

#check comparisonEquivSourceFinitePlaceIndex I
#check carrierOfSourceFinitePlaceIndex I
#check carrierOfSourceFinitePlaceIndex_shell I
#check stageDatumOfSourceFinitePlaceIndex I
#check integralInd3PlaceComparisonRequired_iff_sourceFinitePlaceIndex I

end LeanFormal.IUT.XiFPaper.S1427ConsumerProbe
