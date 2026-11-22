import Mathlib
import tmp.sheaf.xif.paper.S3076PhiXLinearActual

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3076CSqEqOneAttempt

open LeanFormal.IUT.XiFPaper.S3076PhiXLinearActual

variable {K R0 : Type*} [Field K] [CommRing R0] [Algebra K R0]

/-- Conditional order-two coefficient statement: if an order-two K-algebra
endomorphism sends x into K + K·x and 1, x are linearly independent, then the
x-coefficient is ±1. -/
theorem S3076CSqEqOneAttempt
    (φ : R0 →ₐ[K] R0) (x : R0)
    (hφ2 : φ.comp φ = AlgHom.id K R0)
    (hdeg : φ x ∈ Submodule.span K ({1, x} : Set R0))
    (hx_indep : ∀ a c : K, algebraMap K R0 a + c • x = 0 → a = 0 ∧ c = 0) :
    ∃ a c : K, φ x = algebraMap K R0 a + c • x ∧ c ^ 2 = 1 := by
  obtain ⟨a, c, hx⟩ :=
    S3076_phi_X_linear_of_degree (K := K) (R0 := R0) x φ.toLinearMap hdeg
  refine ⟨a, c, hx, ?_⟩
  have hfix : φ (φ x) = x := by
    have h := congrArg (fun f : R0 →ₐ[K] R0 => f x) hφ2
    simpa using h
  have hφx : φ x = algebraMap K R0 a + c • x := hx
  have hcalc : φ (φ x) =
      algebraMap K R0 a + c • (algebraMap K R0 a + c • x) := by
    calc
      φ (φ x) = φ (algebraMap K R0 a + c • x) := by rw [hφx]
      _ = φ (algebraMap K R0 a) + c • φ x := by rw [map_add, map_smul]
      _ = algebraMap K R0 a + c • (algebraMap K R0 a + c • x) := by
        rw [AlgHom.commutes, hφx]
  have hxeq : algebraMap K R0 a + c • (algebraMap K R0 a + c • x) = x := by
    rw [← hcalc]
    exact hfix
  have hrel : algebraMap K R0 (a + c * a) + (c ^ 2 - 1) • x = 0 := by
    have htarget :
        algebraMap K R0 (a + c * a) + (c ^ 2 - 1) • x =
          (algebraMap K R0 a + c • (algebraMap K R0 a + c • x)) - x := by
      rw [map_add, map_mul, ← Algebra.smul_def, smul_add, smul_smul,
        sub_smul, one_smul, pow_two]
      abel
    rw [htarget, hxeq, sub_self]
  obtain ⟨_, hc⟩ := hx_indep (a + c * a) (c ^ 2 - 1) hrel
  exact sub_eq_zero.mp hc

#check S3076CSqEqOneAttempt
#print axioms S3076CSqEqOneAttempt

end LeanFormal.IUT.XiFPaper.S3076CSqEqOneAttempt
end
