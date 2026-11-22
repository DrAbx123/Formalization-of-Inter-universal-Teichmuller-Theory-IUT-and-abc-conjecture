import tmp.sheaf.xif.paper.S2548RabinIrreducibleDvdActual

noncomputable section
set_option maxHeartbeats 4000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2549RabinNonmonicDvdActual

theorem S2549_irreducible_dvd_X_pow_card_pow_sub_X
    {K : Type*} [Field K] [Fintype K] {g : K[X]} (hg : Irreducible g) :
    g ∣ (X : K[X]) ^ (Fintype.card K ^ g.natDegree) - X := by
  have hg0 : g ≠ 0 := hg.ne_zero
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  have hunit : IsUnit (C g.leadingCoeff⁻¹) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hlc))
  let g' : K[X] := C g.leadingCoeff⁻¹ * g
  have hg'monic : g'.Monic := by
    change (C g.leadingCoeff⁻¹ * g).Monic
    rw [mul_comm]
    exact monic_mul_leadingCoeff_inv hg0
  have hassoc : Associated g' g := associated_unit_mul_left g (C g.leadingCoeff⁻¹) hunit
  have hg'irr : Irreducible g' := hassoc.symm.irreducible hg
  have hdvd' : g' ∣ (X : K[X]) ^ (Fintype.card K ^ g'.natDegree) - X :=
    LeanFormal.IUT.XiFPaper.S2548RabinIrreducibleDvdActual.S2545_irreducible_dvd_X_pow_card_pow_sub_X hg'irr hg'monic
  have hdeg : g'.natDegree = g.natDegree := by
    change (C g.leadingCoeff⁻¹ * g).natDegree = g.natDegree
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hlc)]
  rw [← hdeg]
  exact hassoc.dvd_iff_dvd_left.mp hdvd'

#print axioms S2549_irreducible_dvd_X_pow_card_pow_sub_X

end LeanFormal.IUT.XiFPaper.S2549RabinNonmonicDvdActual
end