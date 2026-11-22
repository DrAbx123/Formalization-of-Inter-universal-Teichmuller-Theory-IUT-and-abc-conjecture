import tmp.sheaf.xif.paper.S2555ConcreteIntegralClosureActual
import tmp.sheaf.xif.paper.S2481PairTransitiveHardActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2556HZcMonicActual
open LeanFormal.IUT.XiFPaper.S2555ConcreteIntegralClosureActual
open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual
lemma HZ_natDegree : S2481HZ.natDegree = 8 := by
  unfold S2481HZ
  compute_degree!
lemma HZ_coeff_eight : S2481HZ.coeff 8 = (463856467968 : ℤ) := by
  unfold S2481HZ
  simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_one]
lemma hR_inj : Function.Injective (algebraMap ℤ R) := by
  have hcNZ : (463856467968 : ℤ) ∈ nonZeroDivisors ℤ := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    norm_num
  exact IsLocalization.injective R ((Submonoid.powers_le).mpr hcNZ)
noncomputable def HZR : R[X] := S2481HZ.map (algebraMap ℤ R)
lemma HZR_natDegree : HZR.natDegree = 8 := by
  rw [HZR, Polynomial.natDegree_map_eq_of_injective hR_inj, HZ_natDegree]
lemma HZR_leadingCoeff : HZR.leadingCoeff = algebraMap ℤ R c := by
  have h : HZR.leadingCoeff = HZR.coeff 8 := by
    rw [show HZR.leadingCoeff = HZR.coeff HZR.natDegree from rfl, HZR_natDegree]
  rw [h, HZR, Polynomial.coeff_map, HZ_coeff_eight]
lemma hlc_unit : IsUnit (algebraMap ℤ R c) := by
  exact IsLocalization.map_units R ⟨c, (Submonoid.mem_powers_iff c c).mpr ⟨1, by simp⟩⟩
noncomputable def cu : Rˣ := hlc_unit.unit
lemma cu_spec : (cu : R) = algebraMap ℤ R c := hlc_unit.unit_spec
noncomputable def HZc : R[X] :=
  Polynomial.C (((cu⁻¹ : Rˣ) : R)) * HZR
theorem HZc_monic : HZc.Monic := by
  dsimp [HZc]
  apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [HZR_leadingCoeff, ← cu_spec]
  exact Units.inv_mul cu
#print axioms HZc_monic
end LeanFormal.IUT.XiFPaper.S2556HZcMonicActual
end