import Mathlib.CategoryTheory.Action
import Mathlib.CategoryTheory.IsConnected
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open CategoryTheory

def translationSmul (g : Multiplicative Real) (x : Real) : Real := x + toAdd g

instance translationMulAction : MulAction (Multiplicative Real) Real where
  smul := translationSmul
  one_smul x := by simp [translationSmul]
  mul_smul g h x := by simp [translationSmul, toAdd_mul, add_assoc]

abbrev TG : Type := CategoryTheory.ActionCategory (Multiplicative Real) Real

#synth Category TG
#synth Groupoid TG
instance : MulAction.IsPretransitive (Multiplicative Real) Real where
  exists_smul_eq x y := ⟨Multiplicative.ofAdd (y - x), by simp [translationSmul]⟩
#synth IsConnected TG
#check (fun (x : Real) => (x : TG))
#check (fun (x : Real) => (CategoryTheory.ActionCategory.objEquiv (Multiplicative Real) Real x : TG))
example (x : Real) : CategoryTheory.ActionCategory.back ((x : TG)) = x := rfl
@[simp] theorem back_objEquiv (x : Real) : CategoryTheory.ActionCategory.back
    (CategoryTheory.ActionCategory.objEquiv (Multiplicative Real) Real x) = x := rfl
#check (fun (x y : Real) => (show (x : TG) ⟶ (y : TG) from ⟨Multiplicative.ofAdd (y - x), by simp [translationSmul]⟩))
