import tmp.sheaf.xif.paper.S2668RootCycleTwelveActual
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual

noncomputable section
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual
open LeanFormal.IUT.XiFPaper.S2668RootCycleTwelveActual

namespace LeanFormal.IUT.XiFPaper.S2669PairTransitiveActual

theorem pairTransitive :
    LeanFormal.IUT.XiFPaper.S2375RangePairTransitiveActual.S2375RangePairTransitiveRequired :=
  S2440RangePairTransitive_of_twelveCycle twelveCycleInput

#check pairTransitive
#print axioms pairTransitive

end LeanFormal.IUT.XiFPaper.S2669PairTransitiveActual
end
