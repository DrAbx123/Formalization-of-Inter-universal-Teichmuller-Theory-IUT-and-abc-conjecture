import tmp.sheaf.xif.paper.S2570AEvalChainActual
import tmp.sheaf.xif.paper.S2553Mod613DegreeActual
import tmp.sheaf.xif.paper.S2555Mod613BezoutActual
import tmp.sheaf.xif.paper.S2549RabinNonmonicDvdActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2571F613SpecialRabinActual

open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2570AEvalChainActual

lemma X_pow_dvd {d m : ℕ} (h : d ∣ m) :
    ((X : (ZMod 613)[X]) ^ 613 ^ d - X) ∣ ((X : (ZMod 613)[X]) ^ 613 ^ m - X) :=
  dvd_pow_pow_sub_self_of_dvd (r := (X : (ZMod 613)[X])) (p := 613) h

/-- Specialized degree-12 Rabin criterion over ZMod 613 (no Nat.card unification). -/
theorem irreducible_of_degree_twelve {f : (ZMod 613)[X]}
    (hdeg : f.natDegree = 12)
    (hdvd : f ∣ (X : (ZMod 613)[X]) ^ 613 ^ 12 - X)
    (h4 : IsCoprime f ((X : (ZMod 613)[X]) ^ 613 ^ 4 - X))
    (h6 : IsCoprime f ((X : (ZMod 613)[X]) ^ 613 ^ 6 - X)) :
    Irreducible f := by
  by_contra hf
  have hf0 : f ≠ 0 := by intro h; rw [h, natDegree_zero] at hdeg; omega
  have hfunit : ¬ IsUnit f := by intro hu; have h0 := natDegree_eq_zero_of_isUnit hu; omega
  obtain ⟨g, hg_irr, hg_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hfunit hf0
  have hg_dvd_E : g ∣ (X : (ZMod 613)[X]) ^ 613 ^ 12 - X := hg_dvd.trans hdvd
  have hdvd12 : g.natDegree ∣ 12 :=
    Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hg_irr (by
      simpa [Nat.card_eq_fintype_card, ZMod.card] using hg_dvd_E)
  have hgpos : 0 < g.natDegree := Irreducible.natDegree_pos hg_irr
  have hgle : g.natDegree ≤ 12 := by rw [← hdeg]; exact natDegree_le_of_dvd hg_dvd hf0
  have hgne : g.natDegree ≠ 12 := by
    intro h12
    have hassoc : Associated g f := associated_of_dvd_of_natDegree_le hg_dvd hf0 (by omega)
    exact hf (hassoc.irreducible hg_irr)
  set d := g.natDegree with hddef
  have hdvd' : d ∣ 12 := by simpa [hddef] using hdvd12
  have hlt' : d < 12 := by simpa [hddef] using lt_of_le_of_ne hgle hgne
  have hpos' : 0 < d := by simpa [hddef] using hgpos
  have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 6 := by
    interval_cases d <;> norm_num at hdvd' <;> norm_num
  rcases hcases with h1 | h2 | h3 | h4d | h6d
  · have hgd : g.natDegree = 1 := by omega
    have hg1 : g ∣ (X : (ZMod 613)[X]) ^ 613 ^ g.natDegree - X := by
      simpa [Nat.card_eq_fintype_card, ZMod.card] using
        LeanFormal.IUT.XiFPaper.S2549RabinNonmonicDvdActual.S2549_irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    have hg1' : g ∣ (X : (ZMod 613)[X]) ^ 613 ^ 1 - X := by simpa [hgd] using hg1
    have hg6 : g ∣ (X : (ZMod 613)[X]) ^ 613 ^ 6 - X :=
      hg1'.trans (X_pow_dvd (d := 1) (m := 6) (by norm_num))
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)
  · have hgd : g.natDegree = 2 := by omega
    have hg2 : g ∣ (X : (ZMod 613)[X]) ^ 613 ^ 2 - X := by
      simpa [hgd, Nat.card_eq_fintype_card, ZMod.card] using
        LeanFormal.IUT.XiFPaper.S2549RabinNonmonicDvdActual.S2549_irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    have hg6 : g ∣ (X : (ZMod 613)[X]) ^ 613 ^ 6 - X :=
      hg2.trans (X_pow_dvd (d := 2) (m := 6) (by norm_num))
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)
  · have hgd : g.natDegree = 3 := by omega
    have hg3 : g ∣ (X : (ZMod 613)[X]) ^ 613 ^ 3 - X := by
      simpa [hgd, Nat.card_eq_fintype_card, ZMod.card] using
        LeanFormal.IUT.XiFPaper.S2549RabinNonmonicDvdActual.S2549_irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    have hg6 : g ∣ (X : (ZMod 613)[X]) ^ 613 ^ 6 - X :=
      hg3.trans (X_pow_dvd (d := 3) (m := 6) (by norm_num))
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)
  · have hgd : g.natDegree = 4 := by omega
    have hg4 : g ∣ (X : (ZMod 613)[X]) ^ 613 ^ 4 - X := by
      simpa [hgd, Nat.card_eq_fintype_card, ZMod.card] using
        LeanFormal.IUT.XiFPaper.S2549RabinNonmonicDvdActual.S2549_irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    exact hg_irr.not_isUnit (h4.isUnit_of_dvd' hg_dvd hg4)
  · have hgd : g.natDegree = 6 := by omega
    have hg6 : g ∣ (X : (ZMod 613)[X]) ^ 613 ^ 6 - X := by
      simpa [hgd, Nat.card_eq_fintype_card, ZMod.card] using
        LeanFormal.IUT.XiFPaper.S2549RabinNonmonicDvdActual.S2549_irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)

end LeanFormal.IUT.XiFPaper.S2571F613SpecialRabinActual
end