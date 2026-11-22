import Mathlib

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2545RabinDegreeTwelveActual

lemma S2545_irreducible_dvd_X_pow_card_pow_sub_X
    {K : Type*} [Field K] [Fintype K] {g : K[X]} (hg : Irreducible g) :
    g ∣ (X : K[X]) ^ (Nat.card K ^ g.natDegree) - X := by
  classical
  haveI : Fact (Irreducible g) := ⟨hg⟩
  letI : Algebra K (AdjoinRoot g) :=
    ((AdjoinRoot.mkₐ g).comp (Algebra.ofId K K[X])).toAlgebra
  haveI : Field (AdjoinRoot g) := inferInstance
  haveI : Module K (AdjoinRoot g) := Algebra.toModule
  haveI : FiniteDimensional K (AdjoinRoot g) :=
    (AdjoinRoot.powerBasis hg.ne_zero).finite
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite K
  haveI : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  let r : AdjoinRoot g := AdjoinRoot.root g
  have hroot : r ^ Nat.card (AdjoinRoot g) = r := FiniteField.pow_card r
  have hcard : Nat.card (AdjoinRoot g) = Nat.card K ^ g.natDegree := by
    rw [Module.card_eq_pow_finrank (K := K) (V := AdjoinRoot g)]
    congr 1
    exact (AdjoinRoot.powerBasis hg.ne_zero).finrank
  have hmin_dvd : minpoly K r ∣ (X : K[X]) ^ (Nat.card K ^ g.natDegree) - X := by
    apply minpoly.dvd
    rw [map_sub, map_pow, aeval_X, hcard, hroot, sub_self]
  have hgroot : aeval r g = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hmin_dvd_g : minpoly K r ∣ g := minpoly.dvd K r hgroot
  have hassoc : Associated g (minpoly K r) := by
    exact hg.associated_of_dvd hmin_dvd_g (minpoly.ne_zero hgroot)
  exact hassoc.dvd_iff.mpr hmin_dvd

lemma S2545X_pow_dvd {K : Type*} [CommRing K] {d m : ℕ} (h : d ∣ m) :
    ((X : K[X]) ^ Nat.card K ^ d - X) ∣ ((X : K[X]) ^ Nat.card K ^ m - X) :=
  dvd_pow_pow_sub_self_of_dvd (r := (X : K[X])) (p := Nat.card K) h

theorem S2545irreducible_of_degree_twelve {K : Type*} [Field K] [Fintype K] {f : K[X]}
    (hdeg : f.natDegree = 12)
    (hdvd : f ∣ (X : K[X]) ^ Nat.card K ^ 12 - X)
    (h4 : IsCoprime f ((X : K[X]) ^ Nat.card K ^ 4 - X))
    (h6 : IsCoprime f ((X : K[X]) ^ Nat.card K ^ 6 - X)) :
    Irreducible f := by
  by_contra hf
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hfunit : ¬ IsUnit f := by
    intro hu
    have h0 := natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨g, hg_irr, hg_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hfunit hf0
  have hg_dvd_E : g ∣ (X : K[X]) ^ Nat.card K ^ 12 - X := hg_dvd.trans hdvd
  have hdvd12 : g.natDegree ∣ 12 :=
    Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hg_irr hg_dvd_E
  have hgpos : 0 < g.natDegree := Irreducible.natDegree_pos hg_irr
  have hgle : g.natDegree ≤ 12 := by
    rw [← hdeg]
    exact natDegree_le_of_dvd hg_dvd hf0
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
    have hg1 : g ∣ (X : K[X]) ^ Nat.card K ^ g.natDegree - X :=
      irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    have hg1' : g ∣ (X : K[X]) ^ Nat.card K ^ 1 - X := by simpa [hgd] using hg1
    have hg6 : g ∣ (X : K[X]) ^ Nat.card K ^ 6 - X :=
      hg1'.trans (S2545X_pow_dvd (K := K) (d := 1) (m := 6) (by norm_num))
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)
  · have hgd : g.natDegree = 2 := by omega
    have hg2 : g ∣ (X : K[X]) ^ Nat.card K ^ 2 - X := by
      simpa [hgd] using irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    have hg6 : g ∣ (X : K[X]) ^ Nat.card K ^ 6 - X :=
      hg2.trans (S2545X_pow_dvd (K := K) (d := 2) (m := 6) (by norm_num))
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)
  · have hgd : g.natDegree = 3 := by omega
    have hg3 : g ∣ (X : K[X]) ^ Nat.card K ^ 3 - X := by
      simpa [hgd] using irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    have hg6 : g ∣ (X : K[X]) ^ Nat.card K ^ 6 - X :=
      hg3.trans (S2545X_pow_dvd (K := K) (d := 3) (m := 6) (by norm_num))
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)
  · have hgd : g.natDegree = 4 := by omega
    have hg4 : g ∣ (X : K[X]) ^ Nat.card K ^ 4 - X := by
      simpa [hgd] using irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    exact hg_irr.not_isUnit (h4.isUnit_of_dvd' hg_dvd hg4)
  · have hgd : g.natDegree = 6 := by omega
    have hg6 : g ∣ (X : K[X]) ^ Nat.card K ^ 6 - X := by
      simpa [hgd] using irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)

#print axioms S2545irreducible_of_degree_twelve

end LeanFormal.IUT.XiFPaper.S2545RabinDegreeTwelveActual
end