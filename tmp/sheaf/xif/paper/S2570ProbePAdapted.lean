import tmp.sheaf.xif.paper.S2570AEvalChainActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 500000
open Polynomial
namespace PP
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2570AEvalChainActual

def P4 : (ZMod 613)[X] := (X : (ZMod 613)[X]) ^ (613 ^ 4)
lemma P4_def : P4 = (X : (ZMod 613)[X]) ^ (613 ^ 4) := rfl

lemma gd4 : G ∣ P4 - T4 := by
  show G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 4) - T4
  exact LeanFormal.IUT.XiFPaper.S2570AEvalChainActual.G_dvd_pow4_sub_T4

lemma isC {a b c : (ZMod 613)[X]} (h : IsCoprime a b) (hbc : a ∣ c - b) : IsCoprime a c := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨t, ht⟩ := hbc
  refine ⟨u - v * t, v, ?_⟩
  have hb : c - a * t = b := by rw [← ht]; ring
  calc (u - v * t) * a + v * c = u * a + v * (c - a * t) := by ring
    _ = u * a + v * b := by rw [hb]
    _ = 1 := huv

lemma cP4 : IsCoprime G (P4 - X) := by
  have hsub : G ∣ (P4 - X) - (T4 - X) := by
    rw [show (P4 - X) - (T4 - X) = P4 - T4 from sub_sub_sub_cancel_right _ _ _]
    exact gd4
  exact isC LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual.coprime_T4 hsub

example : IsCoprime G ((X : (ZMod 613)[X]) ^ (613 ^ 4) - X) := by
  have h := cP4
  rw [P4_def] at h
  exact h

end PP
end
