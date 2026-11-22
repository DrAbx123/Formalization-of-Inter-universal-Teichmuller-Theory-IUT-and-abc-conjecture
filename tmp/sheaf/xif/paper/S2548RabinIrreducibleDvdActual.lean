import Mathlib
noncomputable section
set_option maxHeartbeats 4000000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2548RabinIrreducibleDvdActual
theorem S2545_irreducible_dvd_X_pow_card_pow_sub_X
    {K : Type*} [Field K] [Fintype K]
    {g : K[X]} (hg : Irreducible g) (hgmonic : g.Monic) :
    g ∣ X ^ (Fintype.card K ^ g.natDegree) - X := by
  classical
  letI : Fact (Irreducible g) := ⟨hg⟩
  let L := AdjoinRoot g
  let r : L := AdjoinRoot.root g
  haveI : Module.Finite K L := hgmonic.finite_adjoinRoot
  haveI : Finite L := Module.finite_of_finite K
  haveI : Fintype L := Fintype.ofFinite L
  have hgne : g ≠ 0 := hgmonic.ne_zero
  have hfin : Module.finrank K L = g.natDegree := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hgne), AdjoinRoot.powerBasis_dim hgne]
  have hcard : Fintype.card L = Fintype.card K ^ g.natDegree := by
    rw [Module.card_eq_pow_finrank (K := K) (V := L), hfin]
  have hrpow : r ^ (Fintype.card K ^ g.natDegree) = r := by
    rw [← hcard]
    exact FiniteField.pow_card r
  have hrootg : aeval r g = 0 := by
    rw [aeval_def, AdjoinRoot.algebraMap_eq g]
    exact AdjoinRoot.eval₂_root g
  have hmin : minpoly K r = g := by
    exact (minpoly.eq_of_irreducible_of_monic hg hrootg hgmonic).symm
  have hroot : aeval r ((X ^ (Fintype.card K ^ ((minpoly K r).natDegree)) - X : K[X])) = 0 := by
    rw [hmin, ← hcard]
    simp [FiniteField.pow_card r]
  rw [← hmin]
  exact minpoly.dvd K r hroot
#print axioms S2545_irreducible_dvd_X_pow_card_pow_sub_X
end LeanFormal.IUT.XiFPaper.S2548RabinIrreducibleDvdActual
end
