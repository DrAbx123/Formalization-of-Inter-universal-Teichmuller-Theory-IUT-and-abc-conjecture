import tmp.sheaf.xif.paper.S2537ConcreteLocalizationActual
import tmp.sheaf.xif.paper.S2003Psi5ModelActual
import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import tmp.sheaf.xif.paper.S2000D5Mod13CertificateActual

noncomputable section
set_option maxHeartbeats 8000000

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2003Psi5ModelActual
open LeanFormal.IUT.XiFPaper.S2000D5Mod13CertificateActual

namespace LeanFormal.IUT.XiFPaper.S2660R10ModelActual

def lead : ℤ := 343597383680

lemma lead_eq : lead = 2 ^ 36 * 5 := by decide

theorem h10_unit : IsUnit (algebraMap A R (10 : A)) := by
  have hmem : (10 : A) ∈ Submonoid.powers (10 : A) :=
    (Submonoid.mem_powers_iff (10 : A) (10 : A)).mpr ⟨1, by simp⟩
  exact IsLocalization.map_units R ⟨(10 : A), hmem⟩

theorem h2_unit : IsUnit (algebraMap A R (2 : A)) := by
  have h : IsUnit ((algebraMap A R (2 : A)) *
      (algebraMap A R (5 : A))) := by
    convert h10_unit using 1
    rw [← map_mul]
    norm_num
  exact isUnit_of_mul_isUnit_left h

theorem h5_unit : IsUnit (algebraMap A R (5 : A)) := by
  have h : IsUnit ((algebraMap A R (2 : A)) *
      (algebraMap A R (5 : A))) := by
    convert h10_unit using 1
    rw [← map_mul]
    norm_num
  exact isUnit_of_mul_isUnit_right h

theorem hlead_unit : IsUnit (algebraMap A R (lead : A)) := by
  have hz : (lead : A) = (2 : A) ^ 36 * (5 : A) := by
    rw [lead_eq]
    push_cast
    ring
  rw [hz, map_mul, map_pow]
  exact (h2_unit.pow 36).mul h5_unit

noncomputable def S2660u : Rˣ := hlead_unit.unit

noncomputable def f10 : R[X] :=
  C (((S2660u)⁻¹ : Rˣ) : R) * S2132Psi5Z.map (algebraMap ℤ R)

theorem hlead_tower : algebraMap ℤ R lead = algebraMap A R (lead : A) := by
  calc algebraMap ℤ R lead =
      algebraMap A R (algebraMap ℤ A lead) :=
        (IsScalarTower.algebraMap_apply ℤ A R (x := lead)).symm
    _ = algebraMap A R (lead : A) := by norm_num

theorem S2132Psi5Z_leadingCoeff :
    S2132Psi5Z.leadingCoeff = lead := by
  have hdeg : S2132Psi5Z.natDegree = 12 := S2000S2132Psi5Z_natDegree
  have hcoeff : S2132Psi5Z.coeff 12 = lead := by
    unfold S2132Psi5Z lead
    norm_num [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Polynomial.leadingCoeff, hdeg]
  exact hcoeff

theorem map_leading :
    (S2132Psi5Z.map (algebraMap ℤ R)).leadingCoeff =
      algebraMap ℤ R lead := by
  have hM : Submonoid.powers (10 : A) ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num : (10 : A) ≠ 0)
  have hinjA : Function.Injective (algebraMap A R) :=
    IsLocalization.injective R hM
  have hinj : Function.Injective (algebraMap ℤ R) :=
    hinjA.comp (show Function.Injective (algebraMap ℤ A) from
      Int.cast_injective)
  rw [Polynomial.leadingCoeff_map_of_injective
    (f := algebraMap ℤ R) hinj S2132Psi5Z,
    S2132Psi5Z_leadingCoeff]

theorem f10_leading : f10.leadingCoeff = 1 := by
  rw [f10, Polynomial.leadingCoeff_C_mul_of_isUnit
    ((S2660u)⁻¹).isUnit, map_leading, hlead_tower]
  rw [← IsUnit.unit_spec hlead_unit]
  exact Units.inv_mul _

theorem f10_monic : f10.Monic :=
  f10_leading

#check f10
#check f10_monic

end LeanFormal.IUT.XiFPaper.S2660R10ModelActual
end
