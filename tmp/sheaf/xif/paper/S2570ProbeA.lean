import tmp.sheaf.xif.paper.S2570AEvalChainActual
import tmp.sheaf.xif.paper.S2553Mod613DegreeActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
import tmp.sheaf.xif.paper.S2550RabinCriterionActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000000
open Polynomial

namespace S2570ProbeA

open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2570AEvalChainActual

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

lemma G_monic : G.Monic := by unfold G; monicity!
lemma G_natDegree : G.natDegree = 12 := by unfold G; compute_degree!

lemma G_dvd_pow4_sub_T4 : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 4) - T4 :=
  LeanFormal.IUT.XiFPaper.S2570AEvalChainActual.G_dvd_pow4_sub_T4

lemma G_dvd_pow6_sub_T6 : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 6) - T6 :=
  LeanFormal.IUT.XiFPaper.S2570AEvalChainActual.G_dvd_pow6_sub_T6


end S2570ProbeA
end