import tmp.sheaf.xif.paper.S3108IsGaloisActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3108IsGaloisActual
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S3108TopFiniteSolvable

local instance : Fact (Irreducible p) :=
  ⟨by
    rw [show p = (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ) by rfl]
    exact X_pow_sub_C_irreducible_of_prime (p := 2) (by norm_num) (a := (-1 : ℚ))
      (by intro b hb; nlinarith [sq_nonneg b])⟩

theorem S3108_finrank_eq_two : Module.finrank ℚ F = 2 := by
  have hp0 : p ≠ 0 := by
    have h : p = (Polynomial.X ^ 2 + 1 : Polynomial ℚ) := by simp [p]
    rw [h]
    exact (Polynomial.monic_X_pow_add_C (n := 2) (a := (1 : ℚ)) (by norm_num)).ne_zero
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis (K := ℚ) hp0)]
  have hdeg : (Polynomial.X ^ 2 + 1 : Polynomial ℚ).natDegree = 2 := by
    rw [show (1 : Polynomial ℚ) = Polynomial.C (1 : ℚ) by simp]
    exact Polynomial.natDegree_X_pow_add_C
  simpa [AdjoinRoot.powerBasis, p, hdeg]

theorem S3108_top_finiteSolvable :
    isFiniteSolvableGaloisSubextension (⊤ : IntermediateField ℚ F) := by
  have hp0 : p ≠ 0 := by
    have h : p = (Polynomial.X ^ 2 + 1 : Polynomial ℚ) := by simp [p]
    rw [h]
    exact (Polynomial.monic_X_pow_add_C (n := 2) (a := (1 : ℚ)) (by norm_num)).ne_zero
  haveI : FiniteDimensional ℚ F := (AdjoinRoot.powerBasis (K := ℚ) hp0).finite
  haveI : IsGalois ℚ F := S3108_isGalois
  have hcard : Nat.card (F ≃ₐ[ℚ] F) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, S3108_finrank_eq_two]
  have hcard' : Fintype.card (F ≃ₐ[ℚ] F) = 2 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  have hsq : ∀ a : F ≃ₐ[ℚ] F, a * a = 1 := by
    intro a
    have hdvd : orderOf a ∣ 2 := by
      simpa [hcard'] using orderOf_dvd_card (x := a)
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hcomm : ∀ a b : F ≃ₐ[ℚ] F, a * b = b * a := by
    intro a b
    have ha : a = a⁻¹ := eq_inv_of_mul_eq_one_right (hsq a)
    have hb : b = b⁻¹ := eq_inv_of_mul_eq_one_right (hsq b)
    have hab : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right (hsq (a * b))
    calc
      a * b = (a * b)⁻¹ := hab
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [← ha, ← hb]
  haveI : IsSolvable (F ≃ₐ[ℚ] F) := isSolvable_of_comm hcomm
  let e : (⊤ : IntermediateField ℚ F) ≃ₐ[ℚ] F := IntermediateField.topEquiv
  have hcommE : ∀ a b : (⊤ : IntermediateField ℚ F) ≃ₐ[ℚ] (⊤ : IntermediateField ℚ F), a * b = b * a := by
    intro a b
    apply (AlgEquiv.autCongr e).injective
    rw [map_mul, map_mul, hcomm]
  refine ⟨?_, ?_, ?_⟩
  · infer_instance
  · exact (isGalois_iff_isGalois_top (F := ℚ) (E := F)).mpr S3108_isGalois
  · exact isSolvable_of_comm hcommE

#check S3108_top_finiteSolvable
#print axioms S3108_top_finiteSolvable
#print axioms S3108_finrank_eq_two

end LeanFormal.IUT.XiFPaper.S3108TopFiniteSolvable
end
