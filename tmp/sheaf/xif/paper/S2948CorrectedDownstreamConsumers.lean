import tmp.sheaf.xif.paper.PaperQPilotObject
import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual

/-!
S2948 audit result: the stale lowercase-paper olean
tmp/sheaf/xif/paper/PaperQPilotObject.olean has been replaced by a real
source wrapper importing the canonical module
tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual.
The uppercase module tmp.sheaf.xif.PaperQPilotObject is its upstream source;
importing both paths now resolves to the same canonical declarations.
-/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

namespace LeanFormal.IUT.XiFPaper.S2948CorrectedDownstreamConsumers

#check LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual.paperQPilotObjectConcrete
#check LeanFormal.IUT.Theorem311Source.PaperQPilotObject

end LeanFormal.IUT.XiFPaper.S2948CorrectedDownstreamConsumers
end
