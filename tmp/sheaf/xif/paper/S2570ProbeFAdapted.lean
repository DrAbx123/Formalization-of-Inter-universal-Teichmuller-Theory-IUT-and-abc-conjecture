import tmp.sheaf.xif.paper.S2570AEvalChainActual
import tmp.sheaf.xif.paper.S2553Mod613DegreeActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
import tmp.sheaf.xif.paper.S2550RabinCriterionActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
open Polynomial

namespace S2570ProbeFAdapted

open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2570AEvalChainActual

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

lemma G_monic : G.Monic := by unfold G; monicity!
lemma G_natDegree : G.natDegree = 12 := by unfold G; compute_degree!

lemma G_dvd_pow4_sub_T4 : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 4) - T4 := by
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  rw [map_sub]
  have h : aeval (AdjoinRoot.root G) ((X : (ZMod 613)[X]) ^ (613 ^ 4)) =
      aeval (AdjoinRoot.root G) T4 := by
    exact chain4_aeval
  rw [h, sub_self]

lemma G_dvd_pow6_sub_T6 : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 6) - T6 := by
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  rw [map_sub]
  have h : aeval (AdjoinRoot.root G) ((X : (ZMod 613)[X]) ^ (613 ^ 6)) =
      aeval (AdjoinRoot.root G) T6 := by
    exact chain6_aeval
  rw [h, sub_self]

lemma isCoprime_of_dvd_sub {a b c : (ZMod 613)[X]}
    (h : IsCoprime a b) (hbc : a ∣ c - b) : IsCoprime a c := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨t, ht⟩ := hbc
  refine ⟨u - v * t, v, ?_⟩
  have hb : c - a * t = b := by rw [← ht]; ring
  calc (u - v * t) * a + v * c = u * a + v * (c - a * t) := by ring
    _ = u * a + v * b := by rw [hb]
    _ = 1 := huv

lemma coprime4 : IsCoprime G ((X : (ZMod 613)[X]) ^ (613 ^ 4) - X) := by
  have hsub : G ∣ ((X : (ZMod 613)[X]) ^ (613 ^ 4) - X) - (T4 - X) := by
    simpa only [sub_sub_sub_cancel_right] using G_dvd_pow4_sub_T4
  exact isCoprime_of_dvd_sub LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual.coprime_T4 hsub


end S2570ProbeFAdapted
end