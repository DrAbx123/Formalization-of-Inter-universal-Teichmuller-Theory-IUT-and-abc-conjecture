import Mathlib
#check Classical.choice
example : Classical.choice (Nonempty.intro (5:Nat)) = 5 := rfl
example : Classical.choice (show Nonempty Nat from ⟨7⟩) = 7 := rfl
