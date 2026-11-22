import tmp.sheaf.xif.paper.S2553Mod613DegreeActual
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
import tmp.sheaf.xif.paper.S2570Chain10to12ActualAdapted
import tmp.sheaf.xif.paper.S2550RabinCriterionActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2570F613FinalActualAdapted

open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

lemma G_monic : G.Monic := by unfold G; monicity!
lemma G_natDegree : G.natDegree = 12 := by unfold G; compute_degree!

theorem hdvd : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 12) - X := by
  simpa [T12_eq_X] using LeanFormal.IUT.XiFPaper.S2570Chain10to12ActualAdapted.chain12_dvd

lemma coprime4 : IsCoprime G ((X : (ZMod 613)[X]) ^ (613 ^ 4) - X) := by
  have hq : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 4) - T4 :=
    LeanFormal.IUT.XiFPaper.S2570Chain4Actual.chain4_dvd
  rcases hq with ⟨q, hq⟩
  have h := LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual.coprime_T4.add_mul_right_right q
  convert h using 1
  rw [← hq]; ring

lemma coprime6 : IsCoprime G ((X : (ZMod 613)[X]) ^ (613 ^ 6) - X) := by
  have hq : G ∣ (X : (ZMod 613)[X]) ^ (613 ^ 6) - T6 :=
    LeanFormal.IUT.XiFPaper.S2570Chain6to9Actual.chain6_dvd
  rcases hq with ⟨q, hq⟩
  have h := LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual.coprime_T6.add_mul_right_right q
  convert h using 1
  rw [← hq]; ring

theorem G_irreducible : Irreducible G :=
  LeanFormal.IUT.XiFPaper.S2550RabinCriterionActual.S2550irreducible_of_degree_twelve
    (K := ZMod 613) G_natDegree hdvd coprime4 coprime6

theorem F613_irreducible : Irreducible F613 := by
  have hunit : IsUnit (C (168 : ZMod 613)) := isUnit_C.mpr (by decide)
  have hassoc : Associated G F613 := by
    rw [G_eq_scaled]
    exact associated_unit_mul_left F613 (C (168 : ZMod 613)) hunit
  exact hassoc.irreducible G_irreducible

#print axioms F613_irreducible

end LeanFormal.IUT.XiFPaper.S2570F613FinalActualAdapted
end
