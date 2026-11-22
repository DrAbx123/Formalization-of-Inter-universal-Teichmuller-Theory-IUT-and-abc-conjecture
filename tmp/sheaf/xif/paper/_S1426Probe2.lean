import LeanFormal.IUT.IUTII.Kummer.TimesMuIsm
import LeanFormal.IUT.IUTII.Frobenioid.LocalPrimeStrip
import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Analysis.Complex.Basic

open LeanFormal.IUT

#check (inferInstance : Group (ℚ ≃ₗ[ℚ] ℚ))
#check (inferInstance : Monoid (ℚ ≃ₗ[ℚ] ℚ))
#check (inferInstance : Group (ℂ ≃ₗ[ℚ] ℂ))
#check LinearEquiv.trans_apply
#check LinearEquiv.mul_apply
#check AlgEquiv.aut_mul
example (e f : ℚ ≃ₗ[ℚ] ℚ) (x : ℚ) : (e * f) x = e (f x) := by rfl
example (e f : ℚ ≃ₗ[ℚ] ℚ) (x : ℚ) : (e * f) x = f (e x) := by rfl

noncomputable def testConj : ℂ ≃ₗ[ℚ] ℂ where
  toFun z := star z
  invFun z := star z
  left_inv z := by simp
  right_inv z := by simp
  map_add' x y := by simp
  map_smul' c x := by simp

#check starRingEnd ℂ
#check (starRingEnd ℂ).toLinearEquiv
#check (starRingEnd ℂ).toRingEquiv.toMulEquiv
#check Complex.conjAe
#check Complex.conjAe.toLinearEquiv

namespace Test
open LeanFormal.IUT
universe u v
variable {V : Type v}
#check (FPrimeStrip.{u, v, u} V)
#check (fun (F : FPrimeStrip.{u, v, u} V) (w : V) => F.toDPrimeStrip.Pi w)
#check (fun (F : FPrimeStrip.{u, v, u} V) (w : V) => F.Mon w)
#check (fun (F : FPrimeStrip.{u, v, u} V) (w : V) => F.action w)
#check (fun (F : FPrimeStrip.{u, v, u} V) (w : V) => TimesMuKummer.Ism (F.action w))
end Test
