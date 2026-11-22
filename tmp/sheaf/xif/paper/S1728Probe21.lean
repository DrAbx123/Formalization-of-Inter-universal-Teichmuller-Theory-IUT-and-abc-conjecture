import Mathlib.Data.Quot

universe u v
variable {α : Type u} {β : Type v} (r : α → α → Prop) (e : (β ≃ α))
#check (fun (x y : β) => r (e x) (e y))
#check Quot (fun (x y : β) => r (e x) (e y))
#check Quot r
