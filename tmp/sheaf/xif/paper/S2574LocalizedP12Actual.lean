import tmp.sheaf.xif.paper.S2565ConcreteIntegralClosureCActual
import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import tmp.sheaf.xif.paper.S2562HZcMonicCActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2574LocalizedP12Actual

/-! ### The localized ring S = O_F'[1/Cden] and the monic model -/

lemma S2574_hcC_ne : (c : C) ≠ 0 := by
  exact Int.cast_ne_zero.mpr hcA

lemma hMle : Algebra.algebraMapSubmonoid C M ≤ nonZeroDivisors C := by
  rintro x ⟨a, ha, rfl⟩
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff a (c : A)).mp ha
  rw [← hn, map_pow]
  exact pow_mem (mem_nonZeroDivisors_of_ne_zero S2574_hcC_ne) n

local instance : IsDomain S :=
  IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Algebra.algebraMapSubmonoid C M) (S := S) hMle

noncomputable def S2574P : S[X] :=
  S2132Psi5Z.map (algebraMap ℤ S)

theorem S2574_dvd_Cden : (343597383680 : ℤ) ∣ Cden := by
  unfold LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden
    LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.c0
    LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Dval
  norm_num

theorem S2574_lead_unit : IsUnit (algebraMap ℤ S (343597383680 : ℤ)) := by
  obtain ⟨k, hk⟩ := S2574_dvd_Cden
  have hmem : algebraMap ℤ C Cden ∈ Algebra.algebraMapSubmonoid C M := by
    refine ⟨Cden, ?_, rfl⟩
    show Cden ∈ Submonoid.powers (c : A)
    rw [show (c : A) = Cden from rfl]
    exact (Submonoid.mem_powers_iff (Cden : A) (Cden : A)).mpr ⟨1, by simp⟩
  have hCunit : IsUnit (algebraMap C S (algebraMap ℤ C Cden)) :=
    IsLocalization.map_units S ⟨_, hmem⟩
  have hZunit : IsUnit (algebraMap ℤ S Cden) := by
    rw [IsScalarTower.algebraMap_apply ℤ C S]
    exact hCunit
  have hmul : algebraMap ℤ S Cden =
      algebraMap ℤ S (343597383680 : ℤ) * algebraMap ℤ S k := by
    rw [hk, map_mul]
  rw [hmul] at hZunit
  exact isUnit_of_mul_isUnit_left hZunit

lemma S2574P_coeff12 :
    S2574P.coeff 12 = algebraMap ℤ S (343597383680 : ℤ) := by
  rw [S2574P, Polynomial.coeff_map]
  rw [show S2132Psi5Z.coeff 12 = (343597383680 : ℤ) by
    unfold S2132Psi5Z
    norm_num [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]]

lemma S2574P_natDegree : S2574P.natDegree = 12 := by
  have hle : S2574P.natDegree ≤ 12 := by
    rw [S2574P]
    calc (S2132Psi5Z.map (algebraMap ℤ S)).natDegree
        ≤ S2132Psi5Z.natDegree := Polynomial.natDegree_map_le
      _ = 12 := by unfold S2132Psi5Z; compute_degree!
  have hge : 12 ≤ S2574P.natDegree := by
    by_contra h
    have hzero : S2574P.coeff 12 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [S2574P_coeff12] at hzero
    exact S2574_lead_unit.ne_zero hzero
  exact le_antisymm hle hge

lemma S2574P_leadingCoeff [Nontrivial S] :
    S2574P.leadingCoeff = algebraMap ℤ S (343597383680 : ℤ) := by
  rw [Polynomial.leadingCoeff, S2574P_natDegree, S2574P_coeff12]

noncomputable def S2574f : S[X] :=
  Polynomial.C ((((S2574_lead_unit.unit)⁻¹ : Sˣ) : S)) * S2574P

theorem S2574f_monic : S2574f.Monic := by
  rw [S2574f]
  refine Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one ?_
  rw [S2574P_leadingCoeff]
  have hu : ((S2574_lead_unit.unit : S)) = algebraMap ℤ S (343597383680 : ℤ) :=
    IsUnit.unit_spec S2574_lead_unit
  calc ((S2574_lead_unit.unit)⁻¹ : Sˣ) * (algebraMap ℤ S (343597383680 : ℤ))
      = ((S2574_lead_unit.unit)⁻¹ : Sˣ) * (S2574_lead_unit.unit : S) :=
        congrArg (fun z : S => (((S2574_lead_unit.unit)⁻¹ : Sˣ) : S) * z) hu.symm
    _ = 1 := Units.inv_mul S2574_lead_unit.unit

#check S2574f
#check S2574f_monic
#print axioms S2574f_monic

end LeanFormal.IUT.XiFPaper.S2574LocalizedP12Actual
end