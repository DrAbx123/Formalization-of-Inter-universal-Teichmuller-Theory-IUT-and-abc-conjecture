import tmp.sheaf.xif.paper.S2570AEvalChainActual
import tmp.sheaf.xif.paper.S2553Mod613DegreeActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
import tmp.sheaf.xif.paper.S2550RabinCriterionActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000000
open Polynomial

namespace S2570ProbeHeadAdapted

open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2570AEvalChainActual

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

lemma G_monic : G.Monic := by unfold G; monicity!
lemma G_natDegree : G.natDegree = 12 := by unfold G; compute_degree!


end S2570ProbeHeadAdapted
end