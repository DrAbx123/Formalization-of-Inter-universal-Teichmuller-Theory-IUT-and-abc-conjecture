import tmp.sheaf.xif.paper.S2556HZcMonicActual
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2555ConcreteIntegralClosureActual
open LeanFormal.IUT.XiFPaper.S2556HZcMonicActual
open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual
def c0 : ℤ := 463856467968
def Dval : ℤ :=
  4345305365083382316090978154266740962137056508754049584537562001452629669347552693333318628339444576241125166305517397135246066050452111172703998714925023232000000000000000000000000
noncomputable def Cden : ℤ := c0 * Dval
lemma Cden_ne_zero : Cden ≠ 0 := by
  unfold Cden c0 Dval
  norm_num
abbrev R2 : Type := Localization (Submonoid.powers Cden)
lemma hR2_inj : Function.Injective (algebraMap ℤ R2) := by
  have hCmem : Cden ∈ nonZeroDivisors ℤ :=
    mem_nonZeroDivisors_of_ne_zero Cden_ne_zero
  exact IsLocalization.injective R2 ((Submonoid.powers_le).mpr hCmem)
noncomputable def HZR2 : R2[X] := S2481HZ.map (algebraMap ℤ R2)
lemma HZR2_natDegree : HZR2.natDegree = 8 := by
  rw [HZR2, Polynomial.natDegree_map_eq_of_injective hR2_inj, HZ_natDegree]
lemma HZR2_leadingCoeff : HZR2.leadingCoeff = algebraMap ℤ R2 c0 := by
  have h : HZR2.leadingCoeff = HZR2.coeff 8 := by
    rw [show HZR2.leadingCoeff = HZR2.coeff HZR2.natDegree from rfl, HZR2_natDegree]
  rw [h, HZR2, Polynomial.coeff_map]
  have hcoeff : S2481HZ.coeff 8 = c0 := by
    unfold S2481HZ c0
    simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_one]
  rw [hcoeff]
lemma hCden_unit : IsUnit (algebraMap ℤ R2 Cden) := by
  exact IsLocalization.map_units R2 ⟨Cden, (Submonoid.mem_powers_iff Cden Cden).mpr ⟨1, by simp⟩⟩
lemma hc0_unit : IsUnit (algebraMap ℤ R2 c0) := by
  have hmul : algebraMap ℤ R2 Cden = algebraMap ℤ R2 c0 * algebraMap ℤ R2 Dval := by
    unfold Cden
    rw [map_mul]
    rfl
  have hu : IsUnit (algebraMap ℤ R2 c0 * algebraMap ℤ R2 Dval) := by
    rw [← hmul]
    exact hCden_unit
  exact isUnit_of_mul_isUnit_left hu
noncomputable def cu2 : R2ˣ := hc0_unit.unit
lemma cu2_spec : (cu2 : R2) = algebraMap ℤ R2 c0 := hc0_unit.unit_spec
noncomputable def HZc2 : R2[X] := Polynomial.C (((cu2⁻¹ : R2ˣ) : R2)) * HZR2
theorem HZc2_monic : HZc2.Monic := by
  rw [HZc2]
  apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [HZR2_leadingCoeff, ← cu2_spec]
  exact Units.inv_mul cu2
#print axioms HZc2_monic
end LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
end
