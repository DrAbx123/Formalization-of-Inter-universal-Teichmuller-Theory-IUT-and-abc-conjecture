import tmp.sheaf.xif.paper.S2571F613SpecialRabinActual
import tmp.sheaf.xif.paper.S2570AEvalChainActual
import tmp.sheaf.xif.paper.S2553Mod613DegreeActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2572F613IrreducibleActual

open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2570AEvalChainActual
open LeanFormal.IUT.XiFPaper.S2571F613SpecialRabinActual

lemma G_natDegree : G.natDegree = 12 := by unfold G; compute_degree!

theorem hdvd : G ∣ (X : (ZMod 613)[X]) ^ 613 ^ 12 - X :=
  LeanFormal.IUT.XiFPaper.S2570AEvalChainActual.G_dvd_pow_sub_X

lemma isCoprime_of_dvd_sub {a b c : (ZMod 613)[X]}
    (h : IsCoprime a b) (hbc : a ∣ c - b) : IsCoprime a c := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨t, ht⟩ := hbc
  refine ⟨u - v * t, v, ?_⟩
  have hb : c - a * t = b := by rw [← ht]; ring
  calc (u - v * t) * a + v * c = u * a + v * (c - a * t) := by ring
    _ = u * a + v * b := by rw [hb]
    _ = 1 := huv

lemma coprime_gen4 (Y : (ZMod 613)[X]) (hGY : G ∣ Y - T4) :
    IsCoprime G (Y - X) := by
  have hsub : G ∣ (Y - X) - (T4 - X) := by
    rw [show (Y - X) - (T4 - X) = Y - T4 from sub_sub_sub_cancel_right _ _ _]
    exact hGY
  exact isCoprime_of_dvd_sub LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual.coprime_T4 hsub

lemma coprime_gen6 (Y : (ZMod 613)[X]) (hGY : G ∣ Y - T6) :
    IsCoprime G (Y - X) := by
  have hsub : G ∣ (Y - X) - (T6 - X) := by
    rw [show (Y - X) - (T6 - X) = Y - T6 from sub_sub_sub_cancel_right _ _ _]
    exact hGY
  exact isCoprime_of_dvd_sub LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual.coprime_T6 hsub

lemma coprime4 : IsCoprime G ((X : (ZMod 613)[X]) ^ 613 ^ 4 - X) :=
  coprime_gen4 ((X : (ZMod 613)[X]) ^ 613 ^ 4)
    LeanFormal.IUT.XiFPaper.S2570AEvalChainActual.G_dvd_pow4_sub_T4

lemma coprime6 : IsCoprime G ((X : (ZMod 613)[X]) ^ 613 ^ 6 - X) :=
  coprime_gen6 ((X : (ZMod 613)[X]) ^ 613 ^ 6)
    LeanFormal.IUT.XiFPaper.S2570AEvalChainActual.G_dvd_pow6_sub_T6

theorem G_irreducible : Irreducible G :=
  irreducible_of_degree_twelve G_natDegree hdvd coprime4 coprime6

theorem F613_irreducible : Irreducible F613 := by
  have hunit : IsUnit (C (168 : ZMod 613)) := isUnit_C.mpr (by decide)
  have hassoc : Associated G F613 := by
    rw [G_eq_scaled]
    exact associated_unit_mul_left F613 (C (168 : ZMod 613)) hunit
  exact hassoc.irreducible G_irreducible

end LeanFormal.IUT.XiFPaper.S2572F613IrreducibleActual
end