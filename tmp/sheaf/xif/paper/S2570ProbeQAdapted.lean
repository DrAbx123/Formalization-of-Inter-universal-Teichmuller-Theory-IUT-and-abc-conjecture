import tmp.sheaf.xif.paper.S2570AEvalChainActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 500000
open Polynomial
namespace PQ
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2570AEvalChainActual
lemma isC {a b c : (ZMod 613)[X]} (h : IsCoprime a b) (hbc : a ∣ c - b) : IsCoprime a c := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨t, ht⟩ := hbc
  refine ⟨u - v * t, v, ?_⟩
  have hb : c - a * t = b := by rw [← ht]; ring
  calc (u - v * t) * a + v * c = u * a + v * (c - a * t) := by ring
    _ = u * a + v * b := by rw [hb]
    _ = 1 := huv
lemma coprime_gen (Y : (ZMod 613)[X]) (hY : Y = (X : (ZMod 613)[X]) ^ (613 ^ 4))
    (hGY : G ∣ Y - T4) : IsCoprime G (Y - X) := by
  have hsub : G ∣ (Y - X) - (T4 - X) := by
    rw [show (Y - X) - (T4 - X) = Y - T4 from sub_sub_sub_cancel_right _ _ _]
    exact hGY
  exact isC LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual.coprime_T4 hsub
example : IsCoprime G ((X : (ZMod 613)[X]) ^ (613 ^ 4) - X) :=
  coprime_gen ((X : (ZMod 613)[X]) ^ (613 ^ 4)) rfl
    LeanFormal.IUT.XiFPaper.S2570AEvalChainActual.G_dvd_pow4_sub_T4
end PQ
end
