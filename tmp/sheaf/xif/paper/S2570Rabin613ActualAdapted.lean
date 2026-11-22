import tmp.sheaf.xif.paper.S2570Coprime613Actual
import tmp.sheaf.xif.paper.S2550RabinCriterionActual

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2570Rabin613ActualAdapted

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2570AEvalChainActual
open LeanFormal.IUT.XiFPaper.S2570Coprime613Actual

lemma G_natDegree : G.natDegree = 12 := by unfold G; compute_degree!

theorem G_irreducible : Irreducible G :=
  LeanFormal.IUT.XiFPaper.S2550RabinCriterionActual.S2545irreducible_of_degree_twelve
    (K := ZMod 613) G_natDegree G_dvd_pow_sub_X coprime4 coprime6

end LeanFormal.IUT.XiFPaper.S2570Rabin613ActualAdapted
end
