import tmp.sheaf.xif.paper.S2596bConcreteFixesCActual
import tmp.sheaf.xif.paper.S2594LP0PActual
noncomputable section
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596cDenomClearActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
abbrev aOL : OL := algebraMap C OL Cden
noncomputable def u : T := IsLocalization.Away.invSelf aOL
lemma hu : algebraMap OL T aOL * u = 1 :=
  IsLocalization.Away.mul_invSelf aOL
lemma T_denom_clear (t : T) :
    ∃ (k : ℕ) (b : OL), t = algebraMap OL T b * u ^ k := by
  haveI : IsLocalization (Submonoid.powers aOL) T := inferInstance
  obtain ⟨b, y, hy⟩ := IsLocalization.exists_mk'_eq (M := Submonoid.powers aOL) t
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (y : OL) aOL).mp y.2
  refine ⟨k, b, ?_⟩
  rw [← hy]
  have hyk : y = ⟨aOL ^ k, by rw [hk]; exact y.2⟩ := Subtype.ext hk.symm
  rw [hyk]
  have hspec := IsLocalization.mk'_spec T b ⟨aOL ^ k, by rw [hk]; exact y.2⟩
  have hY : (algebraMap OL T aOL) ^ k * u ^ k = 1 := by
    rw [← mul_pow, hu, one_pow]
  have hspec' : IsLocalization.mk' T b ⟨aOL ^ k, by rw [hk]; exact y.2⟩ *
      (algebraMap OL T aOL) ^ k = algebraMap OL T b := by
    simpa [map_pow] using hspec
  have hunit : IsUnit ((algebraMap OL T aOL) ^ k) :=
    IsUnit.pow k (IsUnit.of_mul_eq_one _ hu)
  apply hunit.mul_right_cancel
  rw [hspec', mul_assoc, mul_comm (u ^ k) ((algebraMap OL T aOL) ^ k), hY, mul_one]
#print axioms T_denom_clear
end LeanFormal.IUT.XiFPaper.S2596cDenomClearActual
end
