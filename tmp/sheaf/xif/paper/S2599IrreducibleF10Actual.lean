import tmp.sheaf.xif.paper.S2586NoFactActual
import Mathlib
import tmp.sheaf.xif.paper.S2592Bezout1249Actual
import tmp.sheaf.xif.paper.S2593bVChainActual
import tmp.sheaf.xif.paper.S2594bAChainActual
import tmp.sheaf.xif.paper.S2597bHBez4Actual
import tmp.sheaf.xif.paper.S2598bHBez5Actual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2599IrreducibleF10Actual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hbezAll (d : Nat) (h1 : 1 ≤ d) (h5 : d ≤ 5) :
    ∃ A B : (ZMod 1249)[X],
      A * LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 +
      B * ((X : (ZMod 1249)[X]) ^ (1249 ^ d) - X) = 1 := by
  interval_cases d
  · obtain ⟨A, B, h⟩ := LeanFormal.IUT.XiFPaper.S2592Bezout1249Actual.hbez1
    refine ⟨A, B, ?_⟩
    convert h using 2
    norm_num
  · rw [show (1249 : Nat) ^ 2 = 1249 * 1249 by norm_num]
    convert LeanFormal.IUT.XiFPaper.S2593bVChainActual.hbez2 using 2
  · rw [show (1249 : Nat) ^ 3 = 1249 * 1249 * 1249 by norm_num]
    convert LeanFormal.IUT.XiFPaper.S2594bAChainActual.hbez3 using 2
  · rw [show (1249 : Nat) ^ 4 = 1249 * 1249 * 1249 * 1249 by norm_num]
    exact LeanFormal.IUT.XiFPaper.S2597bHBez4Actual.hbez4
  · rw [show (1249 : Nat) ^ 5 = 1249 * 1249 * 1249 * 1249 * 1249 by norm_num]
    exact LeanFormal.IUT.XiFPaper.S2598bHBez5Actual.hbez5

theorem irreducible_F10 : Irreducible F10 := by
  by_contra hred
  obtain ⟨g, hgmonic, hgirr, hgdvd, hgdeg⟩ :=
    LeanFormal.IUT.XiFPaper.S2586NoFactActual.exists_small_irreducible_factor hred
  have hgpos : 1 ≤ g.natDegree := by
    have hpos : 0 < g.natDegree :=
      Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic
        (p := LeanFormal.IUT.XiFPaper.S2586NoFactActual.F10)
        LeanFormal.IUT.XiFPaper.S2586NoFactActual.F10_monic hgirr.not_isUnit hgdvd
    omega
  obtain ⟨A, B, hAB⟩ := hbezAll g.natDegree hgpos hgdeg
  have hgdvdS : g ∣ (X : (ZMod 1249)[X]) ^ (1249 ^ g.natDegree) - X := by
    letI : Fact (Nat.Prime 1249) := ⟨by norm_num⟩
    have h := LeanFormal.IUT.XiFPaper.S2583FactorDegreeActual.irreducible_dvd_X_pow_card_pow_sub_X
      (K := ZMod 1249) (g := g) hgirr hgmonic
    simpa using h
  have hgdvd' : g ∣ LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 := by
    convert hgdvd using 2
  have hg_dvd_A : g ∣ A * LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 := dvd_mul_of_dvd_right hgdvd' A
  have hg_dvd_B : g ∣ B * ((X : (ZMod 1249)[X]) ^ (1249 ^ g.natDegree) - X) :=
    dvd_mul_of_dvd_right hgdvdS B
  have hg_dvd_one : g ∣ (1 : (ZMod 1249)[X]) := by
    rw [← hAB]
    exact dvd_add hg_dvd_A hg_dvd_B
  exact hgirr.not_isUnit (isUnit_of_dvd_one hg_dvd_one)

#check irreducible_F10
#print axioms irreducible_F10

end LeanFormal.IUT.XiFPaper.S2599IrreducibleF10Actual
end
