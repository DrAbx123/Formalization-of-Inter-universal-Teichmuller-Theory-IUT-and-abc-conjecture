import Mathlib.Data.Quot

universe u v
variable {α : Type u} {β : Type v}
variable (r : α → α → Prop)
variable (e : Equiv β α)
#check (fun (x y : β) => r (e x) (e y))
#check Quot (fun (x y : β) => r (e x) (e y))
