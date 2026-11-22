import tmp.sheaf.xif.paper.S2570AEvalChainActual
import tmp.sheaf.xif.paper.S2553Mod613DegreeActual
import tmp.sheaf.xif.paper.S2550RabinCriterionActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000000
open Polynomial
namespace PH
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2570AEvalChainActual
instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩
lemma gd4 : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 4) - T4 := by
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  rw [map_sub]
  have h : aeval (AdjoinRoot.root G) ((X : (ZMod 613)[X]) ^ (613 ^ 4)) =
      aeval (AdjoinRoot.root G) T4 := by exact chain4_aeval
  rw [h, sub_self]
lemma c4 : IsCoprime G ((X : (ZMod 613)[X]) ^ (613 ^ 4) - X) := by
  obtain ⟨u, v, huv⟩ := LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual.coprime_T4
  obtain ⟨q, hq⟩ := gd4
  refine ⟨u - v * q, v, ?_⟩
  linear_combination huv + v * hq
end PH
end
