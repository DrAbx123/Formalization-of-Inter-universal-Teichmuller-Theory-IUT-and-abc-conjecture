import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Basic

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2536RootSetScaleActual

variable {R A : Type*} [CommRing R] [Nontrivial R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]

theorem S2536_aeval_C_mul (u : Rˣ) (f : R[X]) (x : A) :
    aeval x (C (u : R) * f) = algebraMap R A (u : R) * aeval x f := by
  rw [aeval_mul, aeval_C]

noncomputable def S2536RootSetEquivC_mul (u : Rˣ) (f : R[X]) :
    f.rootSet A ≃ (C (u : R) * f).rootSet A where
  toFun x := ⟨x.1, by
    have hx := x.2
    rw [mem_rootSet'] at hx ⊢
    constructor
    · rw [Polynomial.map_mul, Polynomial.map_C]
      exact mul_ne_zero (C_ne_zero.mpr (by simpa using (FaithfulSMul.algebraMap_injective R A).ne (Units.ne_zero u))) hx.1
    · rw [S2536_aeval_C_mul, hx.2, mul_zero]⟩
  invFun y := ⟨y.1, by
    have hfg : C ((u⁻¹ : Rˣ) : R) * (C (u : R) * f) = f := by
      rw [← mul_assoc, ← C_mul, Units.inv_mul, C_1, one_mul]
    have hy := y.2
    rw [mem_rootSet'] at hy ⊢
    constructor
    · have hmapf : map (algebraMap R A) f ≠ 0 := by
        rw [← hfg, Polynomial.map_mul, Polynomial.map_C]
        exact mul_ne_zero (C_ne_zero.mpr (by simpa using (FaithfulSMul.algebraMap_injective R A).ne (Units.ne_zero ((u⁻¹ : Rˣ))))) hy.1
      exact hmapf
    · have hval : (aeval y.1) (C ((u⁻¹ : Rˣ) : R) * (C (u : R) * f)) = 0 := by
        rw [S2536_aeval_C_mul, hy.2, mul_zero]
      rw [hfg] at hval
      exact hval⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl

#check S2536RootSetEquivC_mul

end LeanFormal.IUT.XiFPaper.S2536RootSetScaleActual
end
