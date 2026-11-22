import tmp.sheaf.xif.paper.S2570AEvalChainActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2570Coprime613Actual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

lemma isCoprime_of_dvd_sub {a b c : (ZMod 613)[X]}
    (h : IsCoprime a b) (hbc : a ∣ c - b) : IsCoprime a c := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨t, ht⟩ := hbc
  refine ⟨u - v * t, v, ?_⟩
  have hb : c - a * t = b := by rw [← ht]; ring
  calc (u - v * t) * a + v * c = u * a + v * (c - a * t) := by ring
    _ = u * a + v * b := by rw [hb]
    _ = 1 := huv

lemma isCoprime_of_dvd_sub_T4 {E : (ZMod 613)[X]}
    (hE : G ∣ E - T4) : IsCoprime G (E - X) := by
  refine isCoprime_of_dvd_sub (a := G) (b := T4 - X) (c := E - X)
    LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual.coprime_T4 ?_
  have heq : (E - X) - (T4 - X) = E - T4 := sub_sub_sub_cancel_right E T4 X
  rwa [heq]

lemma isCoprime_of_dvd_sub_T6 {E : (ZMod 613)[X]}
    (hE : G ∣ E - T6) : IsCoprime G (E - X) := by
  refine isCoprime_of_dvd_sub (a := G) (b := T6 - X) (c := E - X)
    LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual.coprime_T6 ?_
  have heq : (E - X) - (T6 - X) = E - T6 := sub_sub_sub_cancel_right E T6 X
  rwa [heq]

theorem coprime4 : IsCoprime G ((X : (ZMod 613)[X]) ^ (613 ^ 4) - X) :=
  isCoprime_of_dvd_sub_T4
    LeanFormal.IUT.XiFPaper.S2570AEvalChainActual.G_dvd_pow4_sub_T4

theorem coprime6 : IsCoprime G ((X : (ZMod 613)[X]) ^ (613 ^ 6) - X) :=
  isCoprime_of_dvd_sub_T6
    LeanFormal.IUT.XiFPaper.S2570AEvalChainActual.G_dvd_pow6_sub_T6

end LeanFormal.IUT.XiFPaper.S2570Coprime613Actual
end