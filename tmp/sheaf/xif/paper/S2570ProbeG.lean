import tmp.sheaf.xif.paper.S2570AEvalChainActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
noncomputable section
open Polynomial
namespace PG
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2570AEvalChainActual
lemma gd4 : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 4) - T4 := by
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  rw [map_sub]
  have h : aeval (AdjoinRoot.root G) ((X : (ZMod 613)[X]) ^ (613 ^ 4)) =
      aeval (AdjoinRoot.root G) T4 := by exact chain4_aeval
  rw [h, sub_self]
lemma isC {a b c : (ZMod 613)[X]} (h : IsCoprime a b) (hbc : a ∣ c - b) : IsCoprime a c := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨t, ht⟩ := hbc
  refine ⟨u - v * t, v, ?_⟩
  have hb : c - a * t = b := by rw [← ht]; ring
  calc (u - v * t) * a + v * c = u * a + v * (c - a * t) := by ring
    _ = u * a + v * b := by rw [hb]
    _ = 1 := huv
example : G ∣ ((X : (ZMod 613)[X]) ^ (613 ^ 4) - X) - (T4 - X) := by
  simpa only [sub_sub_sub_cancel_right] using gd4
example : IsCoprime G (T4 - X) := LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual.coprime_T4
end PG
end
