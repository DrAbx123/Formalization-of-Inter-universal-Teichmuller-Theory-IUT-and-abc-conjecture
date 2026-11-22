import Mathlib

open Polynomial

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

lemma X_pow_card_sub_X_dvd_X_pow_card_pow_sub_X
    {K : Type*} [Field K] [Fintype K] :
    ((X : K[X]) ^ Nat.card K - X) ∣ ((X : K[X]) ^ (Nat.card K)^2 - X) := by
  have hqpos : 0 < Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  have hq : 1 ≤ Nat.card K := hqpos
  have hdiv : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
    have h := Nat.pow_sub_one_dvd_pow_sub_one (x := Nat.card K) (m := 1) (k := 2) (by norm_num)
    simpa using h
  obtain ⟨c, hc⟩ := hdiv
  have hpoly : (X : K[X]) ^ (Nat.card K - 1) - 1 ∣ (X : K[X]) ^ (Nat.card K ^ 2 - 1) - 1 := by
    rw [hc]
    exact pow_one_sub_dvd_pow_mul_sub_one X (Nat.card K - 1) c
  have hmul := mul_dvd_mul_left (X : K[X]) hpoly
  convert hmul using 1
  · rw [mul_sub, mul_one, ← pow_succ']
    rw [Nat.sub_add_cancel hq]
  · rw [mul_sub, mul_one, ← pow_succ']
    rw [Nat.sub_add_cancel (Nat.one_le_pow 2 (Nat.card K) hqpos)]

lemma irreducible_dvd_X_pow_card_pow_sub_X
    {K : Type*} [Field K] [Fintype K] {g : K[X]} (hg : Irreducible g) :
    g ∣ (X : K[X]) ^ (Nat.card K) ^ g.natDegree - X := by
  haveI : Fact (Irreducible g) := ⟨hg⟩
  letI : Field (AdjoinRoot g) := AdjoinRoot.instField
  letI : Algebra K (AdjoinRoot g) := inferInstance
  let pb : PowerBasis K (AdjoinRoot g) := AdjoinRoot.powerBasis hg.ne_zero
  haveI : Module.Finite K (AdjoinRoot g) := pb.finite
  haveI : Fintype (AdjoinRoot g) := Fintype.ofEquiv (Fin pb.dim → K) pb.basis.equivFun.symm.toEquiv
  have hfr : Module.finrank K (AdjoinRoot g) = g.natDegree := by
    rw [pb.finrank]
    rfl
  have hcard : Nat.card (AdjoinRoot g) = Nat.card K ^ g.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := K), hfr]
  have hroot : aeval (AdjoinRoot.root g) ((X : K[X]) ^ (Nat.card K) ^ g.natDegree - X) = 0 := by
    simp only [map_sub, map_pow, aeval_X]
    have hpow : (AdjoinRoot.root g) ^ (Nat.card K ^ g.natDegree) = AdjoinRoot.root g := by
      rw [← hcard]
      simpa [Nat.card_eq_fintype_card] using (FiniteField.pow_card (AdjoinRoot.root g))
    rw [hpow, sub_self]
  have hdvd : minpoly K (AdjoinRoot.root g) ∣ (X : K[X]) ^ (Nat.card K) ^ g.natDegree - X :=
    minpoly.dvd K _ hroot
  have hmin : minpoly K (AdjoinRoot.root g) = g * C g.leadingCoeff⁻¹ :=
    AdjoinRoot.minpoly_root hg.ne_zero
  have hgdvd : g ∣ minpoly K (AdjoinRoot.root g) := by
    rw [hmin]
    exact dvd_mul_right _ _
  exact hgdvd.trans hdvd

theorem irreducible_of_degree_ten
    {K : Type*} [Field K] [Fintype K] {f : K[X]}
    (hm : f.Monic) (hdeg : f.natDegree = 10)
    (hdvd : f ∣ (X : K[X]) ^ (Nat.card K) ^ 10 - X)
    (h2 : IsCoprime f ((X : K[X]) ^ (Nat.card K) ^ 2 - X))
    (h5 : IsCoprime f ((X : K[X]) ^ (Nat.card K) ^ 5 - X)) :
    Irreducible f := by
  by_contra hf
  have hf0 : f ≠ 0 := hm.ne_zero
  have hfunit : ¬ IsUnit f := by
    intro hu
    have h0 := natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨g, hg_irr, hg_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hfunit hf0
  have hg_dvd_E : g ∣ (X : K[X]) ^ (Nat.card K) ^ 10 - X := hg_dvd.trans hdvd
  have hdvd10 : g.natDegree ∣ 10 :=
    Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hg_irr hg_dvd_E
  have hgpos : 0 < g.natDegree := Irreducible.natDegree_pos hg_irr
  have hgle : g.natDegree ≤ 10 := by
    rw [← hdeg]
    exact natDegree_le_of_dvd hg_dvd hf0
  have hgne : g.natDegree ≠ 10 := by
    intro h10
    have hassoc : Associated g f := associated_of_dvd_of_natDegree_le hg_dvd hf0 (by omega)
    exact hf (hassoc.symm.irreducible hg_irr)
  set d := g.natDegree with hddef
  have hdvd10' : d ∣ 10 := by simpa [hddef] using hdvd10
  have hlt' : d < 10 := by simpa [hddef] using lt_of_le_of_ne hgle hgne
  have hpos' : 0 < d := by simpa [hddef] using hgpos
  have hcases : d = 1 ∨ d = 2 ∨ d = 5 := by
    interval_cases d <;> norm_num at hdvd10' ⊢
  rcases hcases with h1 | h2d | h5d
  · have hg1 : g ∣ (X : K[X]) ^ (Nat.card K) ^ g.natDegree - X :=
      irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    have hg2 : g ∣ (X : K[X]) ^ (Nat.card K) ^ 2 - X := by
      have hdiv := X_pow_card_sub_X_dvd_X_pow_card_pow_sub_X (K := K)
      have hg1' : g ∣ (X : K[X]) ^ Nat.card K - X := by simpa [h1] using hg1
      exact hg1'.trans hdiv
    exact hg_irr.not_unit (h2.isUnit_of_dvd' hg_dvd hg2)
  · have hg2 : g ∣ (X : K[X]) ^ (Nat.card K) ^ 2 - X := by
      simpa [h2d] using irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    exact hg_irr.not_unit (h2.isUnit_of_dvd' hg_dvd hg2)
  · have hg5 : g ∣ (X : K[X]) ^ (Nat.card K) ^ 5 - X := by
      simpa [h5d] using irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    exact hg_irr.not_unit (h5.isUnit_of_dvd' hg_dvd hg5)
