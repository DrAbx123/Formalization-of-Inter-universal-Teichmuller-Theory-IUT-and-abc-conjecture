import Mathlib.Data.Quot
import Mathlib.Logic.Equiv.Defs

universe u v
variable {α : Type u} {β : Type v}
variable (r : α → α → Prop)
variable (e : β ≃ α)
#check (fun (x y : β) => r (e x) (e y))
#check Quot (fun (x y : β) => r (e x) (e y))
