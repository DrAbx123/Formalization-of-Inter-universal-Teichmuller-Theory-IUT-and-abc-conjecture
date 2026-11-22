import Iut.Foundations.Orbicurve
open CategoryTheory
example (f : Iut.SignGroup) (hf : f ≠ 1) : f = Iut.signActionGenerator := by
  revert f
  decide
example (f g : Iut.signActionObject ⟶ Iut.signActionObject) (hf : f ≠ 𝟙 _) (hg : g ≠ 𝟙 _) : f ≫ g = 𝟙 _ := by
  revert f g
  decide