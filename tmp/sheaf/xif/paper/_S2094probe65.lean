import Mathlib

open Polynomial

local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

lemma irreducible_dvd_X_pow_card_pow_sub_X
    {K : Type*} [Field K] [Fintype K] {g : K[X]} (hg : Irreducible g) :
    g ∣ X ^ (Nat.card K) ^ g.natDegree - X := by
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
  have hroot : aeval (AdjoinRoot.root g) (X ^ (Nat.card K) ^ g.natDegree - X) = 0 := by
    simp only [map_sub, map_pow, aeval_X]
    have hpow : (AdjoinRoot.root g) ^ (Nat.card K ^ g.natDegree) = AdjoinRoot.root g := by
      rw [← hcard]
      simpa [Nat.card_eq_fintype_card] using (FiniteField.pow_card (AdjoinRoot.root g))
    rw [hpow, sub_self]
  have hdvd : minpoly K (AdjoinRoot.root g) ∣ X ^ (Nat.card K) ^ g.natDegree - X :=
    minpoly.dvd K _ hroot
  have hmin : minpoly K (AdjoinRoot.root g) = g * C g.leadingCoeff⁻¹ :=
    AdjoinRoot.minpoly_root hg.ne_zero
  have hgdvd : g ∣ minpoly K (AdjoinRoot.root g) := by
    rw [hmin]
    exact dvd_mul_right _ _
  exact hgdvd.trans hdvd
