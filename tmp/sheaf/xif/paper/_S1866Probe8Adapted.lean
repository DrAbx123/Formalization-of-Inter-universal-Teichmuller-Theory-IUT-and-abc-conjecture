
example (α : Type) (a : α) : Classical.choice (Nonempty.intro a) = a := rfl
example (α : Type) (a : α) : Nonempty.some (Nonempty.intro a) = a := rfl
#check Classical.choice
#print Classical.choice
