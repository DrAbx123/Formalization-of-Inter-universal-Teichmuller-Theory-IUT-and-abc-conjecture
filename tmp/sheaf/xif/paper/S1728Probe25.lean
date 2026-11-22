import Mathlib.Data.Quot
import Mathlib.Logic.Equiv.Defs

namespace ProbeQuot

universe u v

variable {α : Type u} {β : Type v} (r : α → α → Prop) (e : β ≃ α)

def quotCongrEquiv : Quot (fun (x y : β) => r (e x) (e y)) ≃ Quot r where
  toFun := Quot.lift (fun x => Quot.mk r (e x)) (fun x y h => Quot.sound h)
  invFun := Quot.lift (fun a => Quot.mk (fun (x y : β) => r (e x) (e y)) (e.symm a))
    (fun a b h => by
      apply Quot.sound
      simpa using h)
  left_inv q := by
    induction q using Quot.inductionOn with
    | h x =>
      apply Quot.sound
      simp
  right_inv q := by
    induction q using Quot.inductionOn with
    | h a =>
      apply Quot.sound
      simp

end ProbeQuot
